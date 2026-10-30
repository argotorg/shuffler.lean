import BbuKraken.Model
import BbuKraken.Asm
import BbuKraken.Specs
import PermuteKraken.Proof
import BbuKraken.StructLayout

/-!
The memory layout of `class Emission` in `c/build_bottom_up.cpp`, and the shape of
the function specs.

The model state and environment are functions of the memory and the address `S`
of the struct (`stOf`, `envOf`), so a spec needs no ghost state. The struct is
`WORDS` words, in the order of the members: `m_target` (word 0), `m_targetSize`
(1), `m_spills` (2), the `Stack` `m_stack` (`m_data` 3, `m_size` 4, `m_trace` 5,
`m_traceSize` 6), the `Mapping` (`m_destinationOf[MAX_N]` from word `DEST`,
`m_positionOf[MAX_N]` from word `POS`), `m_pendingGenerations` (word `PEND`) and
`m_blocked` (words `BLK` and `BLK + 1`). An element of `m_destinationOf` or
`m_positionOf` is an `Optional<StackOffset>`, with `-1` (`SIZE_MAX`) for none (`optOf`).
`slotOf` reads a destination as a `Nat`; with `Pos`, each destination is below `n`, so
no slot of the stack has none. `layout_probe` checks these offsets
against the g++ offsets in `StructLayout` (`test/struct_layout.sh`). A `StackSlot`
is 8 bytes: the payload, the kind and the opcode in the low 6 bytes, then 2 bytes
of padding (`StackSlot.ofWord`). The working stack `m_data` and the target are `n`
slots each. Operation `i` is the 12 bytes at `12i` from `m_trace`: the kind, the
depth, 2 bytes of padding and the slot. The ops buffer (`m_trace`) holds `6n`
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

def DEST : Nat := 7
def POS : Nat := DEST + MAX_N
def PEND : Nat := POS + MAX_N
def BLK : Nat := PEND + 1
-- The size of the struct in words.
def WORDS : Nat := BLK + 2
-- The values, for `simp only` before `omega`.
theorem DEST_eq : DEST = 7 := rfl
theorem POS_eq : POS = 1031 := rfl
theorem PEND_eq : PEND = 2055 := rfl
theorem BLK_eq : BLK = 2056 := rfl
theorem WORDS_eq : WORDS = 2058 := rfl

-- The slot in the word `w`: the low 6 bytes. `==` in the C++ compares these bytes.
def StackSlot.ofWord (w : Word) : StackSlot :=
  ⟨w.extractLsb' 0 32, w.extractLsb' 32 8, w.extractLsb' 40 8⟩

-- An entry of `m_positionOf`: `SIZE_MAX` is none.
def optOf (w : Word) : Option Nat := if w = -1#64 then none else some w.toNat

-- The variable id that `isSpilled` reads for the slot `x`, if it reads one.
def spillId (x : StackSlot) : Option Nat :=
  if x.kind = Value ∧ x.valueOpcode ≠ Const then some x.payload.toNat else none

section
variable (m : Mem 64) (S : Addr)

def tgtOf : Addr := rd m (wordAt S 0)
def nOf : Nat := (rd m (wordAt S 1)).toNat
def splOf : Addr := rd m (wordAt S 2)
def dataOf : Addr := rd m (wordAt S 3)
def opsOf : Addr := rd m (wordAt S 5)

def slotOf (i : Nat) : Slot :=
  ⟨StackSlot.ofWord (rd m (wordAt (dataOf m S) i)), (rd m (wordAt S (DEST + i))).toNat⟩

-- The address of operation `i`.
abbrev opAt (i : Nat) : Addr := opsOf m S + BitVec.ofNat 64 (12 * i)

def opOf (i : Nat) : Op :=
  ⟨rdb m (opAt m S i), rdb m (opAt m S i + 1#64), StackSlot.ofWord (rd m (opAt m S i + 4#64))⟩

-- The model state in memory.
def stOf : St where
  slots := (List.range (rd m (wordAt S 4)).toNat).map (slotOf m S)
  positionOf := (List.range (nOf m S)).map fun d => optOf (rd m (wordAt S (POS + d)))
  pendingGenerations := (rd m (wordAt S PEND)).toNat
  trace := (List.range (rd m (wordAt S 6)).toNat).map (opOf m S)

-- The target slot `d`.
def tgtSlot (d : Nat) : StackSlot := StackSlot.ofWord (rd m (wordAt (tgtOf m S) d))

-- The variable id `i` is in the target: `isSpilled` reads only these bytes.
def tgtVar (i : Nat) : Bool := (List.range (nOf m S)).any fun d => spillId (tgtSlot m S d) == some i

-- The environment in memory. Spilled bytes of ids that are not in the target are 0.
def envOf : Env where
  target := (List.range (nOf m S)).map (tgtSlot m S)
  spills := fun i =>
    if tgtVar m S i then UInt8.ofBitVec (rdb m (splOf m S + BitVec.ofNat 64 i)) else 0

-- The spilled bytes that `isSpilled` reads: one for each variable in the target.
def splBlocks : List (Addr × Nat) :=
  (List.range (nOf m S)).filterMap fun d =>
    (spillId (tgtSlot m S d)).map fun i => (splOf m S + BitVec.ofNat 64 i, 1)

-- The memory that the functions write: `m_size`, the words from `m_traceSize` to
-- `m_blocked`, the working stack and the ops buffer.
def writable : List (Addr × Nat) :=
  [(wordAt S 4, 8), (wordAt S 6, 8 * (WORDS - 6)), (dataOf m S, 8 * nOf m S),
    (opsOf m S, 72 * nOf m S)]

-- The memory that the functions only read: the words 0 to 3 and 5 of the struct,
-- the target and the spilled bytes.
def readable : List (Addr × Nat) :=
  (S, 32) :: (wordAt S 5, 8) :: (tgtOf m S, 8 * nOf m S) :: splBlocks m S

-- The struct at `S` is well formed.
structure Wf : Prop where
  mapped : Mem.Mapped (writable m S ++ readable m S) m
  struct_lt : S.toNat + 8 * WORDS ≤ 2 ^ 64
  data_lt : (dataOf m S).toNat + 8 * nOf m S ≤ 2 ^ 64
  ops_lt : (opsOf m S).toNat + 72 * nOf m S ≤ 2 ^ 64
  tgt_lt : (tgtOf m S).toNat + 8 * nOf m S ≤ 2 ^ 64
  -- The struct, the working stack, the ops buffer and the inputs do not overlap.
  disj_struct : Mem.Blocks.Disjoint [(S, 8 * WORDS)]
    ((dataOf m S, 8 * nOf m S) :: (opsOf m S, 72 * nOf m S) :: (tgtOf m S, 8 * nOf m S)
      :: splBlocks m S)
  disj_data : Mem.Blocks.Disjoint [(dataOf m S, 8 * nOf m S)]
    ((opsOf m S, 72 * nOf m S) :: (tgtOf m S, 8 * nOf m S) :: splBlocks m S)
  disj_ops : Mem.Blocks.Disjoint [(opsOf m S, 72 * nOf m S)] ((tgtOf m S, 8 * nOf m S) :: splBlocks m S)
  len_le : (rd m (wordAt S 4)).toNat ≤ nOf m S
  nops_le : (rd m (wordAt S 6)).toNat ≤ 6 * nOf m S
  n_le : nOf m S ≤ MAX_N

end

/-! ## Spec shape -/

abbrev rsp (s : MachineData) : Addr := s.regs.get64 .rsp
abbrev rdi (s : MachineData) : Addr := s.regs.get64 .rdi
abbrev rsi (s : MachineData) : Word := s.regs.get64 .rsi
abbrev rdx (s : MachineData) : Word := s.regs.get64 .rdx
abbrev rcx (s : MachineData) : Word := s.regs.get64 .rcx
abbrev r8 (s : MachineData) : Word := s.regs.get64 .r8
abbrev rax (s : MachineData) : Word := s.regs.get64 .rax

-- A `Status` or a `bool` result: the byte `al`. The ABI does not define the other
-- bytes of `rax`.
abbrev al (s : MachineData) : BitVec 8 := (rax s).setWidth 8

-- `Status::Done`, `Status::Blocked` and `Status::AssertionFailed`
abbrev DONE : BitVec 8 := 0#8
abbrev BLOCKED : BitVec 8 := 1#8
abbrev ASSERTION_FAILED : BitVec 8 := 2#8

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

-- The `Status` of a function with the model result `r`: `ok a` gives `Q a`,
-- `blocked` writes `m_blocked` and returns `Blocked`, `assertion` returns
-- `AssertionFailed`.
def Res {α : Type} (S : Addr) (r : M α) (Q : α → Prop) (t : MachineData) : Prop :=
  match r with
  | .ok a => Q a
  | .error (.blocked pos excess _) =>
    al t = BLOCKED ∧ rd t.dmem (wordAt S BLK) = BitVec.ofNat 64 pos
      ∧ rd t.dmem (wordAt S (BLK + 1)) = BitVec.ofNat 64 excess
  | .error .assertion => al t = ASSERTION_FAILED

-- `-1` for none
def encOpt : Option Nat → Word
  | some i => BitVec.ofNat 64 i
  | none => -1#64

-- The words agree with the byte offsets that g++ gives (`test/struct_layout.sh`).
theorem layout_probe : StructLayout.offsets =
    [("m_target", 8 * 0), ("m_targetSize", 8 * 1), ("m_spills", 8 * 2), ("m_stack.m_data", 8 * 3),
      ("m_stack.m_size", 8 * 4), ("m_stack.m_trace", 8 * 5), ("m_stack.m_traceSize", 8 * 6),
      ("m_mapping.m_destinationOf", 8 * DEST), ("m_mapping.m_positionOf", 8 * POS),
      ("m_pendingGenerations", 8 * PEND), ("m_blocked.offset", 8 * BLK),
      ("m_blocked.excess", 8 * (BLK + 1)), ("size", 8 * WORDS)] := by decide
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

theorem filterMap_congr {α β} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr (fun b hb => h b (List.mem_cons_of_mem _ hb))]


-- The struct words 0 to 3 and 5 lie in `readable`.
theorem hdr_congr (h : Mem.UnchangedOutside l m m') (hd : Mem.Blocks.Disjoint (readable m S) l)
    {k : Nat} (hk : k < 4 ∨ k = 5) : rd m' (wordAt S k) = rd m (wordAt S k) :=
  rd_congr h (disjoint_mono (bs' := readable m S) (fun x hx => by
    simp only [Mem.Blocks.Inside, or_false] at hx
    rcases hk with hk | rfl
    · exact Or.inl (by bv_omega)
    · exact Or.inr (Or.inl (by bv_omega))) hd)

-- The target words lie in `readable`.
theorem tgt_congr (h : Mem.UnchangedOutside l m m') (hw : Wf m S)
    (hd : Mem.Blocks.Disjoint (readable m S) l) {d : Nat} (hdn : d < nOf m S) :
    rd m' (wordAt (tgtOf m S) d) = rd m (wordAt (tgtOf m S) d) :=
  rd_congr h (disjoint_mono (bs' := readable m S) (fun x hx => Or.inr (Or.inr (Or.inl (by
    have := hw.n_le
    simp only [Mem.Blocks.Inside, or_false] at hx; bv_omega)))) hd)

-- The struct words of a change outside `readable`.
theorem hdr_congr' (h : Mem.UnchangedOutside l m m') (hd : Mem.Blocks.Disjoint (readable m S) l) :
    nOf m' S = nOf m S ∧ tgtOf m' S = tgtOf m S ∧ splOf m' S = splOf m S ∧ opsOf m' S = opsOf m S
      ∧ dataOf m' S = dataOf m S :=
  ⟨congrArg BitVec.toNat (hdr_congr h hd (k := 1) (by omega)),
    hdr_congr h hd (k := 0) (by omega), hdr_congr h hd (k := 2) (by omega),
    hdr_congr h hd (k := 5) (by omega), hdr_congr h hd (k := 3) (by omega)⟩

-- A change outside `writable` and the header keeps the environment, the well
-- formedness and the regions.
theorem envOf_congr (h : Mem.UnchangedOutside l m m') (hw : Wf m S)
    (hd : Mem.Blocks.Disjoint (readable m S) l) :
    envOf m' S = envOf m S ∧ readable m' S = readable m S ∧ writable m' S = writable m S := by
  obtain ⟨hn, ht, hs, ho, hda⟩ := hdr_congr' h hd
  have hts : ∀ d, d < nOf m S → tgtSlot m' S d = tgtSlot m S d := fun d hdn => by
    simp only [tgtSlot, ht, tgt_congr h hw hd hdn]
  have htv : tgtVar m' S = tgtVar m S := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [tgtVar, hn, List.any_eq_true, List.mem_range]
    constructor <;> rintro ⟨d, hdn, hp⟩ <;> refine ⟨d, hdn, ?_⟩
    · rwa [hts d hdn] at hp
    · rwa [hts d hdn]
  have hspl : splBlocks m' S = splBlocks m S := by
    simp only [splBlocks, hn, hs]
    exact filterMap_congr fun d hdn => by rw [hts d (List.mem_range.mp hdn)]
  refine ⟨?_, ?_, ?_⟩
  · simp only [envOf, hn, hs, htv]
    congr 1
    · exact List.map_congr_left fun d hdn => hts d (List.mem_range.mp hdn)
    · funext i
      split
      · rename_i hi
        rw [rdb_congr h (disjoint_mono (bs' := readable m S)
          (fun x hx => Or.inr (Or.inr (Or.inr ?_))) hd)]
        simp only [tgtVar, List.any_eq_true, List.mem_range, beq_iff_eq] at hi
        obtain ⟨d, hdn, hp⟩ := hi
        refine inside_of_mem (List.mem_filterMap.mpr ⟨d, List.mem_range.mpr hdn, ?_⟩) hx
        simp only [hp, Option.map_some]
      · rfl
  · simp only [readable, hn, ht, hspl]
  · simp only [writable, hn, ho, hda]

-- A change outside `readable` that keeps `writable` mapped and len and nops in
-- range keeps the well formedness.
theorem Wf.congr (h : Mem.UnchangedOutside l m m') (hw : Wf m S)
    (hd : Mem.Blocks.Disjoint (readable m S) l) (hm : Mem.Mapped (writable m S) m')
    (hlen : (rd m' (wordAt S 4)).toNat ≤ nOf m S) (hnops : (rd m' (wordAt S 6)).toNat ≤ 6 * nOf m S) :
    Wf m' S := by
  obtain ⟨-, hr, hwr⟩ := envOf_congr h hw hd
  obtain ⟨hn, ht, -, ho, hda⟩ := hdr_congr' h hd
  have hspl : splBlocks m' S = splBlocks m S := by
    simp only [readable, hn, ht, List.cons.injEq, true_and] at hr; exact hr
  refine ⟨?_, hw.struct_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr, hwr]
    intro x hx
    rcases inside_append.mp hx with hx | hx
    · exact hm x hx
    · rw [h x (hd x hx)]; exact hw.mapped x (inside_append.mpr (Or.inr hx))
  · rw [hda, hn]; exact hw.data_lt
  · rw [ho, hn]; exact hw.ops_lt
  · rw [ht, hn]; exact hw.tgt_lt
  · rw [hda, ho, hn, ht, hspl]; exact hw.disj_struct
  · rw [hda, ho, hn, ht, hspl]; exact hw.disj_data
  · rw [ho, hn, ht, hspl]; exact hw.disj_ops
  · rw [hn]; exact hlen
  · rw [hn]; exact hnops
  · rw [hn]; exact hw.n_le

-- A change outside the struct, the working stack and the ops buffer keeps the model state.
theorem stOf_congr (h : Mem.UnchangedOutside l m m') (hw : Wf m S)
    (hd : Mem.Blocks.Disjoint (writable m S ++ readable m S) l) : stOf m' S = stOf m S := by
  have hdr : Mem.Blocks.Disjoint (readable m S) l :=
    disjoint_mono (fun x hx => inside_append.mpr (Or.inr hx)) hd
  have hwr : Mem.Blocks.Disjoint (writable m S) l :=
    disjoint_mono (fun x hx => inside_append.mpr (Or.inl hx)) hd
  obtain ⟨hn, -, -, ho, hda⟩ := hdr_congr' h hdr
  have hlen : rd m' (wordAt S 4) = rd m (wordAt S 4) :=
    rd_congr h (disjoint_mono (bs' := writable m S) (fun x hx => Or.inl (by
      simp only [Mem.Blocks.Inside, or_false] at hx; bv_omega)) hwr)
  -- the words from `m_traceSize` to `m_blocked`
  have hmap : ∀ {k}, 6 ≤ k → k < WORDS → rd m' (wordAt S k) = rd m (wordAt S k) :=
    fun hk1 hk2 => rd_congr h (disjoint_mono (bs' := writable m S) (fun x hx => Or.inr (Or.inl (by
      have := hw.struct_lt
      simp only [Mem.Blocks.Inside, or_false, BLK, PEND, POS, DEST, WORDS, MAX_N] at hx hk1 hk2 this ⊢
      bv_omega))) hwr)
  have hdata : ∀ {k}, k < nOf m S → rd m' (wordAt (dataOf m S) k) = rd m (wordAt (dataOf m S) k) :=
    fun hk => rd_congr h (disjoint_mono (bs' := writable m S) (fun x hx => Or.inr (Or.inr (Or.inl (by
      have := hw.n_le
      simp only [Mem.Blocks.Inside, or_false] at hx; bv_omega)))) hwr)
  have hop : ∀ {i}, i < 6 * nOf m S → opOf m' S i = opOf m S i := fun {i} hi => by
    have := hw.n_le
    have hin : ∀ (a : Addr) (n : Nat), (a - opAt m S i).toNat + n ≤ 12 → (a - opAt m S i).toNat < 12 →
        Mem.Blocks.Disjoint [(a, n)] l := fun a n hc _ => disjoint_mono (bs' := writable m S)
      (fun x hx => Or.inr (Or.inr (Or.inr (Or.inl (by
        simp only [Mem.Blocks.Inside, or_false] at hx; bv_omega))))) hwr
    simp only [opOf, opAt, ho]
    rw [rdb_congr h (hin _ 1 (by simp) (by simp)), rdb_congr h (hin _ 1 (by bv_omega) (by bv_omega)),
      rd_congr h (hin _ 8 (by bv_omega) (by bv_omega))]
  have hlen' := hw.len_le
  have hnops := hw.nops_le
  simp only [stOf, hlen, hmap (k := 6) (by omega) (by simp only [WORDS_eq]; omega),
    hmap (k := PEND) (by simp only [PEND_eq]; omega) (by simp only [PEND_eq, WORDS_eq]; omega), hn]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    have := hw.n_le; rw [show MAX_N = 1024 from rfl] at this
    simp only [slotOf, hda, hdata (k := i) (by omega),
      hmap (k := DEST + i) (by simp only [DEST_eq]; omega) (by simp only [WORDS_eq, DEST_eq]; omega)]
  · refine List.map_congr_left fun d hd => ?_
    have := List.mem_range.mp hd
    have := hw.n_le; rw [show MAX_N = 1024 from rfl] at this
    rw [hmap (k := POS + d) (by simp only [POS_eq]; omega) (by simp only [WORDS_eq, POS_eq]; omega)]
  · exact List.map_congr_left fun i hi => hop (by have := List.mem_range.mp hi; omega)

-- A change outside the struct, the buffers and the inputs keeps the well formedness.
theorem Wf.congr_of_disjoint (h : Mem.UnchangedOutside l m m') (hw : Wf m S)
    (hd : Mem.Blocks.Disjoint (writable m S ++ readable m S) l) : Wf m' S := by
  have hst := congrArg St.slots (stOf_congr h hw hd)
  have hops := congrArg St.trace (stOf_congr h hw hd)
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
  simp only [WORDS, BLK, PEND, POS, DEST, MAX_N] at hsl
  -- `x` in the struct
  have hst : ∀ c n, c + n ≤ 8 * WORDS → (x - (rdi s + BitVec.ofNat 64 c)).toNat + 1 ≤ n →
      Mem.Blocks.Inside x 1 [(rdi s, 8 * WORDS)] := by
    intro c n hc hx
    simp only [Mem.Blocks.Inside, or_false, WORDS, BLK, PEND, POS, DEST, MAX_N] at hc ⊢; bv_omega
  have hw03 : (x - rdi s).toNat + 1 ≤ 32 → Mem.Blocks.Inside x 1 [(rdi s, 8 * WORDS)] :=
    fun h => by simp only [Mem.Blocks.Inside, or_false, WORDS, BLK, PEND, POS, DEST, MAX_N]; bv_omega
  have hw5 : (x - wordAt (rdi s) 5).toNat + 1 ≤ 8 → Mem.Blocks.Inside x 1 [(rdi s, 8 * WORDS)] :=
    hst (8 * 5) 8 (by simp [WORDS, BLK, PEND, POS, DEST, MAX_N])
  simp only [mod] at hl
  rcases hl with hl | hl | hl | hl | hl | hl
  · exact hf.disj x (Or.inl hl) (inside_append.mpr (Or.inr hr))
  · -- `m_size`
    rcases hr with hr | hr | hr | hr
    · simp only [wordAt] at hl; bv_omega
    · simp only [wordAt] at hr hl; bv_omega
    · exact hw.disj_struct x (hst (8 * 4) 8 (by simp [WORDS, BLK, PEND, POS, DEST, MAX_N]) hl)
        (Or.inr (Or.inr (Or.inl hr)))
    · exact hw.disj_struct x (hst (8 * 4) 8 (by simp [WORDS, BLK, PEND, POS, DEST, MAX_N]) hl)
        (Or.inr (Or.inr (Or.inr hr)))
  · -- the words from `m_traceSize` to `m_blocked`
    simp only [WORDS, BLK, PEND, POS, DEST, MAX_N] at hl
    rcases hr with hr | hr | hr | hr
    · simp only [wordAt] at hl; bv_omega
    · simp only [wordAt] at hr hl; bv_omega
    · exact hw.disj_struct x
        (hst (8 * 6) (8 * (WORDS - 6)) (by simp [WORDS, BLK, PEND, POS, DEST, MAX_N]) hl)
        (Or.inr (Or.inr (Or.inl hr)))
    · exact hw.disj_struct x
        (hst (8 * 6) (8 * (WORDS - 6)) (by simp [WORDS, BLK, PEND, POS, DEST, MAX_N]) hl)
        (Or.inr (Or.inr (Or.inr hr)))
  · -- the working stack
    rcases hr with hr | hr | hr | hr
    · exact hw.disj_struct x (hw03 hr) (Or.inl hl)
    · exact hw.disj_struct x (hw5 hr) (Or.inl hl)
    · exact hw.disj_data x (Or.inl hl) (Or.inr (Or.inl hr))
    · exact hw.disj_data x (Or.inl hl) (Or.inr (Or.inr hr))
  · -- ops
    rcases hr with hr | hr | hr | hr
    · exact hw.disj_struct x (hw03 hr) (Or.inr (Or.inl hl))
    · exact hw.disj_struct x (hw5 hr) (Or.inr (Or.inl hl))
    · exact hw.disj_ops x (Or.inl hl) (Or.inl hr)
    · exact hw.disj_ops x (Or.inl hl) (Or.inr hr)
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
