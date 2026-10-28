import BbuKraken.Model
import BbuKraken.Asm
import BbuKraken.Specs
import PermuteKraken.Proof

/-!
The memory layout of `struct st` in `c/build_bottom_up.c`, and the shape of the
function specs.

The model state and environment are functions of the memory and the address `S`
of the struct (`stOf`, `envOf`), so a spec needs no ghost state. The struct is
520 words: 8 header words (len, pending, nops, n, target, spilled, ops,
blocked), then `stack[256]` from word 8 and `dest[256]` from word 264. Operation
`i` is the words `2i` and `2i + 1` from `ops`. The ops buffer holds `6n`
operations.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

abbrev Addr := BitVec 64

-- The word at `a`, in the form that the load specs give.
def rd (m : Mem 64) (a : Addr) : Word := BitVec.ofInt 64 (m.loadInt a 8).get!

-- The byte at `a`, in the form that `cmpb` gives.
def rdb (m : Mem 64) (a : Addr) : BitVec 8 := BitVec.ofInt 8 (m.loadInt a 1).get!

-- The address of word `k` from `b`.
abbrev wordAt (b : Addr) (k : Nat) : Addr := b + BitVec.ofNat 64 (8 * k)

def STACK : Nat := 8
def DEST : Nat := 264
-- The size of the struct in words.
def WORDS : Nat := 520

section
variable (m : Mem 64) (S : Addr)

def nOf : Nat := (rd m (wordAt S 3)).toNat
def tgtOf : Addr := rd m (wordAt S 4)
def splOf : Addr := rd m (wordAt S 5)
def opsOf : Addr := rd m (wordAt S 6)
def blkOf : Addr := rd m (wordAt S 7)

def slotOf (i : Nat) : Slot :=
  ⟨rd m (wordAt S (STACK + i)), (rd m (wordAt S (DEST + i))).toNat⟩

def opOf (i : Nat) : Op := ⟨rd m (wordAt (opsOf m S) (2 * i)), rd m (wordAt (opsOf m S) (2 * i + 1))⟩

-- The model state in memory.
def stOf : St where
  slots := (List.range (rd m (wordAt S 0)).toNat).map (slotOf m S)
  pending := (rd m (wordAt S 1)).toNat
  ops := (List.range (rd m (wordAt S 2)).toNat).map (opOf m S)

-- The variable id `i` is in the target: `is_spilled` reads only these bytes.
def tgtVar (i : Nat) : Bool :=
  (List.range (nOf m S)).any fun d =>
    let v := (rd m (wordAt (tgtOf m S) d)).toNat
    2 ≤ v && v % 2 == 0 && (v - 2) / 2 == i

-- The environment in memory. Spilled bytes of ids that are not in the target are 0.
def envOf : Env where
  target := (List.range (nOf m S)).map fun i => rd m (wordAt (tgtOf m S) i)
  spilled := fun i =>
    if tgtVar m S i then UInt8.ofBitVec (rdb m (splOf m S + BitVec.ofNat 64 i)) else 0

-- The spilled bytes that `is_spilled` reads: one for each variable in the target.
def splBlocks : List (Addr × Nat) :=
  (List.range (nOf m S)).filterMap fun d =>
    let v := (rd m (wordAt (tgtOf m S) d)).toNat
    if 2 ≤ v ∧ v % 2 = 0 then some (splOf m S + BitVec.ofNat 64 ((v - 2) / 2), 1) else none

-- The memory that the functions write: len, pending and nops, the stack and
-- dest arrays, the ops buffer and `blocked`.
def writable : List (Addr × Nat) :=
  [(S, 24), (wordAt S STACK, 8 * 512), (opsOf m S, 96 * nOf m S), (blkOf m S, 16)]

-- The memory that the functions only read: the rest of the header, the target
-- and the spilled bytes.
def readable : List (Addr × Nat) :=
  (wordAt S 3, 40) :: (tgtOf m S, 8 * nOf m S) :: splBlocks m S

-- The struct at `S` is well formed.
structure Wf : Prop where
  mapped : Mem.Mapped (writable m S ++ readable m S) m
  struct_lt : S.toNat + 8 * WORDS ≤ 2 ^ 64
  ops_lt : (opsOf m S).toNat + 96 * nOf m S ≤ 2 ^ 64
  blk_lt : (blkOf m S).toNat + 16 ≤ 2 ^ 64
  tgt_lt : (tgtOf m S).toNat + 8 * nOf m S ≤ 2 ^ 64
  -- The struct, the ops buffer and `blocked` do not overlap each other or the inputs.
  disj_struct : Mem.Blocks.Disjoint [(S, 8 * WORDS)]
    ((opsOf m S, 96 * nOf m S) :: (blkOf m S, 16) :: (tgtOf m S, 8 * nOf m S) :: splBlocks m S)
  disj_ops : Mem.Blocks.Disjoint [(opsOf m S, 96 * nOf m S)]
    ((blkOf m S, 16) :: (tgtOf m S, 8 * nOf m S) :: splBlocks m S)
  disj_blk : Mem.Blocks.Disjoint [(blkOf m S, 16)] ((tgtOf m S, 8 * nOf m S) :: splBlocks m S)
  len_le : (rd m (wordAt S 0)).toNat ≤ 256
  nops_le : (rd m (wordAt S 2)).toNat ≤ 6 * nOf m S
  n_le : nOf m S ≤ 256

end

/-! ## Spec shape -/

abbrev rsp (s : MachineData) : Addr := s.regs.get64 .rsp
abbrev rdi (s : MachineData) : Addr := s.regs.get64 .rdi
abbrev rsi (s : MachineData) : Word := s.regs.get64 .rsi
abbrev rdx (s : MachineData) : Word := s.regs.get64 .rdx
abbrev rcx (s : MachineData) : Word := s.regs.get64 .rcx
abbrev r8 (s : MachineData) : Word := s.regs.get64 .r8
abbrev rax (s : MachineData) : Word := s.regs.get64 .rax

-- The stack frame of a function that uses `F` bytes below `rsp` at the call,
-- with the return address.
abbrev frame (F : Nat) (s : MachineData) : Addr × Nat := (rsp s - BitVec.ofNat 64 F, F)

structure FrameOk (F : Nat) (s : MachineData) : Prop where
  le : F ≤ (rsp s).toNat
  mapped : Mem.Mapped [frame F s] s.dmem
  disj : Mem.Blocks.Disjoint [frame F s] (writable s.dmem (rdi s) ++ readable s.dmem (rdi s))

-- The precondition of a function with the struct in `rdi`, frame size `F`, and
-- the further condition `A`.
def Pre (F : Nat) (A : MachineData → Prop) (s : MachineData) : Prop :=
  Wf s.dmem (rdi s) ∧ FrameOk F s ∧ A s

-- The registers that the functions may change, and the memory they may write.
def mod (F : Nat) (s : MachineData) : Modifies :=
  ⟨[.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11],
    frame F s :: writable s.dmem (rdi s)⟩

-- The postcondition: the struct stays well formed, the frame stays mapped, and `R`.
def Post (F : Nat) (R : MachineData → MachineData → Prop) (s t : MachineData) : Prop :=
  Wf t.dmem (rdi s) ∧ Mem.Mapped [frame F s] t.dmem ∧ R s t

-- The return value of a function with the model result `r`: `ok a` gives `Q a`,
-- `blocked` writes `blocked` and returns -1, `assertion` returns -2.
def Res {α : Type} (S : Addr) (r : M α) (Q : α → Prop) (t : MachineData) : Prop :=
  match r with
  | .ok a => Q a
  | .error (.blocked pos excess) =>
    rax t = -1#64 ∧ rd t.dmem (blkOf t.dmem S) = BitVec.ofNat 64 pos
      ∧ rd t.dmem (wordAt (blkOf t.dmem S) 1) = BitVec.ofNat 64 excess
  | .error .assertion => rax t = -2#64

-- `-1` for none
def encOpt : Option Nat → Word
  | some i => BitVec.ofNat 64 i
  | none => -1#64

/-! ## Memory lemmas -/

section
variable {m m' : Mem 64} {S : Addr} {l : List (Addr × Nat)}

-- The `n` bytes at `x` lie in `a ++ b` if they lie in `a` or in `b`.
theorem inside_append {x : Addr} {n : Nat} {a b : List (Addr × Nat)} :
    Mem.Blocks.Inside x n (a ++ b) ↔ Mem.Blocks.Inside x n a ∨ Mem.Blocks.Inside x n b := by
  induction a with
  | nil => simp [Mem.Blocks.Inside]
  | cons p a ih => obtain ⟨c, k⟩ := p; simp only [List.cons_append, Mem.Blocks.Inside, ih, or_assoc]

-- The bytes in a block of a list lie in the list.
theorem inside_of_mem {x : Addr} {n : Nat} {p : Addr × Nat} {bs : List (Addr × Nat)}
    (hp : p ∈ bs) (h : Mem.Blocks.Inside x n [p]) : Mem.Blocks.Inside x n bs := by
  induction bs with
  | nil => cases hp
  | cons q bs ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨c, k⟩ := p; exact h.elim Or.inl False.elim
    · exact (ih hp).tail

-- `Disjoint` holds for a part of a block list.
theorem disjoint_mono {bs bs' l : List (Addr × Nat)}
    (hs : ∀ x, Mem.Blocks.Inside x 1 bs → Mem.Blocks.Inside x 1 bs')
    (hd : Mem.Blocks.Disjoint bs' l) : Mem.Blocks.Disjoint bs l := fun x hx => hd x (hs x hx)

theorem disjoint_symm {a b : List (Addr × Nat)} (h : Mem.Blocks.Disjoint a b) :
    Mem.Blocks.Disjoint b a := fun x hb ha => h x ha hb

theorem rd_storeInt_self {a : Addr} (x : Word) (_h : Mem.Mapped [(a, 8)] m) :
    rd (m.storeInt a 8 x.toInt) a = x := by
  rw [rd, Mem.loadInt_storeInt _ _ _ _ (by decide), Option.get!_some]
  exact BitVec.ofInt_ofBytes_toBytes 64 8 rfl x

-- A store does not change a word that it does not overlap.
theorem rd_storeInt_of_disjoint {a b : Addr} {v : Int}
    (h : Mem.Blocks.Disjoint [(a, 8)] [(b, 8)]) : rd (m.storeInt a 8 v) b = rd m b := by
  rw [rd, rd, Mem.loadInt_congr (m' := m)]
  intro i hi
  exact (Mem.Blocks.Inside.base (bs := []) (Nat.le_refl 8)).get?_storeInt
    (fun hb => h _ hb ((Mem.Blocks.Inside.base (bs := []) (Nat.le_refl 8)).add_ofNat hi)) v

theorem rdb_storeInt_of_disjoint {a b : Addr} {v : Int}
    (h : Mem.Blocks.Disjoint [(a, 8)] [(b, 1)]) : rdb (m.storeInt a 8 v) b = rdb m b := by
  rw [rdb, rdb, Mem.loadInt_congr (m' := m)]
  intro i hi
  exact (Mem.Blocks.Inside.base (bs := []) (Nat.le_refl 8)).get?_storeInt
    (fun hb => h _ hb ((Mem.Blocks.Inside.base (bs := []) (Nat.le_refl 1)).add_ofNat hi)) v

-- Words `j ≠ k` of a block that does not wrap do not overlap.
theorem disjoint_wordAt {b : Addr} {j k K : Nat} (hjk : j ≠ k) (hj : j < K) (hk : k < K)
    (hb : b.toNat + 8 * K ≤ 2 ^ 64) :
    Mem.Blocks.Disjoint [(wordAt b j, 8)] [(wordAt b k, 8)] := by
  intro x hx hy
  simp only [Mem.Blocks.Inside, or_false] at hx hy
  bv_omega

theorem rd_congr {a : Addr} (h : Mem.UnchangedOutside l m m')
    (ha : Mem.Blocks.Disjoint [(a, 8)] l) : rd m' a = rd m a := by
  rw [rd, rd, Mem.loadInt_congr (m' := m)]
  intro i hi
  exact h _ (ha _ ((Mem.Blocks.Inside.base (bs := []) (Nat.le_refl 8)).add_ofNat hi))

theorem rdb_congr {a : Addr} (h : Mem.UnchangedOutside l m m')
    (ha : Mem.Blocks.Disjoint [(a, 1)] l) : rdb m' a = rdb m a := by
  rw [rdb, rdb, Mem.loadInt_congr (m' := m)]
  intro i hi
  exact h _ (ha _ ((Mem.Blocks.Inside.base (bs := []) (Nat.le_refl 1)).add_ofNat hi))

private theorem filterMap_congr' {α β} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr' (fun b hb => h b (List.mem_cons_of_mem _ hb))]

-- The header words 3 to 7 lie in `readable`.
theorem hdr_congr (h : Mem.UnchangedOutside l m m') (hd : Mem.Blocks.Disjoint (readable m S) l)
    {k : Nat} (hk3 : 3 ≤ k) (hk : k < 8) : rd m' (wordAt S k) = rd m (wordAt S k) :=
  rd_congr h (disjoint_mono (bs' := readable m S) (fun x hx => Or.inl (by
    simp only [Mem.Blocks.Inside, or_false] at hx; bv_omega)) hd)

-- The target words lie in `readable`.
theorem tgt_congr (h : Mem.UnchangedOutside l m m') (hw : Wf m S)
    (hd : Mem.Blocks.Disjoint (readable m S) l) {d : Nat} (hdn : d < nOf m S) :
    rd m' (wordAt (tgtOf m S) d) = rd m (wordAt (tgtOf m S) d) :=
  rd_congr h (disjoint_mono (bs' := readable m S) (fun x hx => Or.inr (Or.inl (by
    have := hw.n_le
    simp only [Mem.Blocks.Inside, or_false] at hx; bv_omega))) hd)

-- A change outside `writable` and the header keeps the environment, the well
-- formedness and the regions.
theorem envOf_congr (h : Mem.UnchangedOutside l m m') (hw : Wf m S)
    (hd : Mem.Blocks.Disjoint (readable m S) l) :
    envOf m' S = envOf m S ∧ readable m' S = readable m S ∧ writable m' S = writable m S := by
  have hn : nOf m' S = nOf m S := congrArg BitVec.toNat (hdr_congr h hd (k := 3) (by omega) (by omega))
  have ht : tgtOf m' S = tgtOf m S := hdr_congr h hd (k := 4) (by omega) (by omega)
  have hs : splOf m' S = splOf m S := hdr_congr h hd (k := 5) (by omega) (by omega)
  have ho : opsOf m' S = opsOf m S := hdr_congr h hd (k := 6) (by omega) (by omega)
  have hb : blkOf m' S = blkOf m S := hdr_congr h hd (k := 7) (by omega) (by omega)
  have htv : tgtVar m' S = tgtVar m S := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [tgtVar, hn, ht, List.any_eq_true, List.mem_range]
    constructor <;> rintro ⟨d, hdn, hp⟩ <;> refine ⟨d, hdn, ?_⟩
    · rwa [tgt_congr h hw hd hdn] at hp
    · rwa [tgt_congr h hw hd hdn]
  have hspl : splBlocks m' S = splBlocks m S := by
    simp only [splBlocks, hn, ht, hs]
    exact filterMap_congr' fun d hdn => by rw [tgt_congr h hw hd (List.mem_range.mp hdn)]
  refine ⟨?_, ?_, ?_⟩
  · simp only [envOf, hn, ht, hs, htv]
    congr 1
    · exact List.map_congr_left fun d hdn => tgt_congr h hw hd (List.mem_range.mp hdn)
    · funext i
      split
      · rename_i hi
        rw [rdb_congr h (disjoint_mono (bs' := readable m S) (fun x hx => Or.inr (Or.inr ?_)) hd)]
        simp only [tgtVar, List.any_eq_true, List.mem_range] at hi
        obtain ⟨d, hdn, hp⟩ := hi
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
        refine inside_of_mem (List.mem_filterMap.mpr ⟨d, List.mem_range.mpr hdn, ?_⟩) hx
        simp only [hp.1, and_self, ite_true, hp.2]
      · rfl
  · simp only [readable, hn, ht, hspl]
  · simp only [writable, hn, ho, hb]
-- A change outside `readable` that keeps `writable` mapped and len and nops in
-- range keeps the well formedness.
theorem Wf.congr (h : Mem.UnchangedOutside l m m') (hw : Wf m S)
    (hd : Mem.Blocks.Disjoint (readable m S) l) (hm : Mem.Mapped (writable m S) m')
    (hlen : (rd m' (wordAt S 0)).toNat ≤ 256) (hnops : (rd m' (wordAt S 2)).toNat ≤ 6 * nOf m S) :
    Wf m' S := by
  obtain ⟨-, hr, hwr⟩ := envOf_congr h hw hd
  have hn : nOf m' S = nOf m S := congrArg BitVec.toNat (hdr_congr h hd (k := 3) (by omega) (by omega))
  have ht : tgtOf m' S = tgtOf m S := hdr_congr h hd (k := 4) (by omega) (by omega)
  have ho : opsOf m' S = opsOf m S := hdr_congr h hd (k := 6) (by omega) (by omega)
  have hb : blkOf m' S = blkOf m S := hdr_congr h hd (k := 7) (by omega) (by omega)
  have hspl : splBlocks m' S = splBlocks m S := by
    simp only [readable, hn, ht, List.cons.injEq, true_and] at hr; exact hr
  refine ⟨?_, hw.struct_lt, ?_, ?_, ?_, ?_, ?_, ?_, hlen, ?_, ?_⟩
  · rw [hr, hwr]
    intro x hx
    rcases inside_append.mp hx with hx | hx
    · exact hm x hx
    · rw [h x (hd x hx)]; exact hw.mapped x (inside_append.mpr (Or.inr hx))
  · rw [ho, hn]; exact hw.ops_lt
  · rw [hb]; exact hw.blk_lt
  · rw [ht, hn]; exact hw.tgt_lt
  · rw [ho, hn, hb, ht, hspl]; exact hw.disj_struct
  · rw [ho, hn, hb, ht, hspl]; exact hw.disj_ops
  · rw [hn, hb, ht, hspl]; exact hw.disj_blk
  · rw [hn]; exact hnops
  · rw [hn]; exact hw.n_le

-- A change outside the struct and the ops buffer keeps the model state.
theorem stOf_congr (h : Mem.UnchangedOutside l m m') (hw : Wf m S)
    (hd : Mem.Blocks.Disjoint (writable m S ++ readable m S) l) : stOf m' S = stOf m S := by
  have hdr : Mem.Blocks.Disjoint (readable m S) l :=
    disjoint_mono (fun x hx => inside_append.mpr (Or.inr hx)) hd
  have hwr : Mem.Blocks.Disjoint (writable m S) l :=
    disjoint_mono (fun x hx => inside_append.mpr (Or.inl hx)) hd
  have ho : opsOf m' S = opsOf m S := hdr_congr h hdr (k := 6) (by omega) (by omega)
  have hlo : ∀ {k}, k < 3 → rd m' (wordAt S k) = rd m (wordAt S k) := fun hk =>
    rd_congr h (disjoint_mono (bs' := writable m S) (fun x hx => Or.inl (by
      simp only [Mem.Blocks.Inside, or_false] at hx; bv_omega)) hwr)
  have hslot : ∀ {k}, STACK ≤ k → k < STACK + 512 → rd m' (wordAt S k) = rd m (wordAt S k) :=
    fun hk1 hk2 => rd_congr h (disjoint_mono (bs' := writable m S) (fun x hx => Or.inr (Or.inl (by
      have := hw.struct_lt
      simp only [Mem.Blocks.Inside, or_false, STACK, WORDS] at hx hk1 hk2 this ⊢; bv_omega))) hwr)
  have hop : ∀ {k}, k < 12 * nOf m S → rd m' (wordAt (opsOf m S) k) = rd m (wordAt (opsOf m S) k) :=
    fun hk => rd_congr h (disjoint_mono (bs' := writable m S) (fun x hx => Or.inr (Or.inr (Or.inl (by
      have := hw.n_le
      simp only [Mem.Blocks.Inside, or_false] at hx; bv_omega)))) hwr)
  have hlen := hw.len_le
  have hnops := hw.nops_le
  simp only [stOf, hlo (k := 0) (by omega), hlo (k := 1) (by omega), hlo (k := 2) (by omega)]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [slotOf, hslot (k := STACK + i) (by omega) (by simp only [STACK]; omega),
      hslot (k := DEST + i) (by simp only [STACK, DEST]; omega) (by simp only [STACK, DEST]; omega)]
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [opOf, ho, hop (k := 2 * i) (by omega), hop (k := 2 * i + 1) (by omega)]

-- A change outside the struct, the ops buffer and the inputs keeps the well formedness.
theorem Wf.congr_of_disjoint (h : Mem.UnchangedOutside l m m') (hw : Wf m S)
    (hd : Mem.Blocks.Disjoint (writable m S ++ readable m S) l) : Wf m' S := by
  have hst := congrArg St.slots (stOf_congr h hw hd)
  have hops := congrArg St.ops (stOf_congr h hw hd)
  simp only [stOf] at hst hops
  refine Wf.congr h hw (disjoint_mono (fun x hx => inside_append.mpr (Or.inr hx)) hd)
    (fun x hx => ?_) ?_ ?_
  · rw [h x (hd x (inside_append.mpr (Or.inl hx)))]
    exact hw.mapped x (inside_append.mpr (Or.inl hx))
  · have := congrArg List.length hst; simp only [List.length_map, List.length_range] at this
    rw [this]; exact hw.len_le
  · have := congrArg List.length hops; simp only [List.length_map, List.length_range] at this
    rw [this]; exact hw.nops_le

-- The frame of a callee lies in the frame of its caller: `t` is the state at
-- the call, `k` bytes below the `rsp` of the caller at its own call.
theorem FrameOk.sub {s t : MachineData} {F G k : Nat} (h : FrameOk F s) (_hw : Wf s.dmem (rdi s))
    (hrdi : rdi t = rdi s) (hrsp : rsp t = rsp s - BitVec.ofNat 64 k) (hk : k + G ≤ F)
    (hmap : Mem.Mapped [frame F s] t.dmem)
    (hr : readable t.dmem (rdi s) = readable s.dmem (rdi s))
    (hwr : writable t.dmem (rdi s) = writable s.dmem (rdi s)) :
    FrameOk G t := by
  have hle := h.le
  have hsub : ∀ x, Mem.Blocks.Inside x 1 [frame G t] → Mem.Blocks.Inside x 1 [frame F s] := by
    intro x hx
    simp only [Mem.Blocks.Inside, or_false, hrsp] at hx ⊢
    bv_omega
  refine ⟨?_, fun x hx => hmap x (hsub x hx), ?_⟩
  · simp only [hrsp]; bv_omega
  · rw [hrdi, hr, hwr]; exact disjoint_mono hsub h.disj

-- The memory that a callee may write does not overlap the memory it only reads.
theorem Pre.disj {F : Nat} {A : MachineData → Prop} {s : MachineData} (hpre : Pre F A s) :
    Mem.Blocks.Disjoint (readable s.dmem (rdi s)) (mod F s).mem := by
  obtain ⟨hw, hf, -⟩ := hpre
  intro x hr hl
  have hsl := hw.struct_lt
  simp only [WORDS] at hsl
  -- `x` in the struct
  have hst : ∀ c n, c + n ≤ 8 * WORDS → (x - (rdi s + BitVec.ofNat 64 c)).toNat + 1 ≤ n →
      Mem.Blocks.Inside x 1 [(rdi s, 8 * WORDS)] := by
    intro c n hc hx
    simp only [Mem.Blocks.Inside, or_false, WORDS] at hc ⊢; bv_omega
  simp only [mod] at hl
  rcases hl with hl | hl | hl | hl | hl | hl
  · exact hf.disj x (Or.inl hl) (inside_append.mpr (Or.inr hr))
  · -- (S, 24)
    rcases hr with hr | hr | hr
    · simp only [wordAt] at hr; bv_omega
    · exact hw.disj_struct x (hst 0 24 (by simp [WORDS]) (by simpa using hl)) (Or.inr (Or.inr (Or.inl hr)))
    · exact hw.disj_struct x (hst 0 24 (by simp [WORDS]) (by simpa using hl)) (Or.inr (Or.inr (Or.inr hr)))
  · -- the stack and dest arrays
    simp only [STACK] at hl
    rcases hr with hr | hr | hr
    · simp only [wordAt] at hr hl; bv_omega
    · exact hw.disj_struct x (hst 64 4096 (by simp [WORDS]) hl) (Or.inr (Or.inr (Or.inl hr)))
    · exact hw.disj_struct x (hst 64 4096 (by simp [WORDS]) hl) (Or.inr (Or.inr (Or.inr hr)))
  · -- ops
    rcases hr with hr | hr | hr
    · exact hw.disj_struct x (hst 24 40 (by simp [WORDS]) hr) (Or.inl hl)
    · exact hw.disj_ops x (Or.inl hl) (Or.inr (Or.inl hr))
    · exact hw.disj_ops x (Or.inl hl) (Or.inr (Or.inr hr))
  · -- blocked
    rcases hr with hr | hr | hr
    · exact hw.disj_struct x (hst 24 40 (by simp [WORDS]) hr) (Or.inr (Or.inl hl))
    · exact hw.disj_blk x (Or.inl hl) (Or.inl hr)
    · exact hw.disj_blk x (Or.inl hl) (Or.inr hr)
  · exact hl

-- A callee keeps the environment and the regions.
theorem Post.env {F : Nat} {A : MachineData → Prop}
    {s t : MachineData} (hpre : Pre F A s) (hag : (mod F s).Agree s t) :
    envOf t.dmem (rdi s) = envOf s.dmem (rdi s) ∧ readable t.dmem (rdi s) = readable s.dmem (rdi s)
      ∧ writable t.dmem (rdi s) = writable s.dmem (rdi s) :=
  envOf_congr hag.2 hpre.1 hpre.disj

-- `Mapped` survives a change that maps the blocks it changes.
theorem Mapped.of_unchanged {X : List (Addr × Nat)} (hX : Mem.Mapped X m)
    (h : Mem.UnchangedOutside l m m') (hl : Mem.Mapped l m') : Mem.Mapped X m' := by
  intro b hb
  by_cases hbl : Mem.Blocks.Inside b 1 l
  · exact hl b hbl
  · rw [h b hbl]; exact hX b hb

end

end Bbu
