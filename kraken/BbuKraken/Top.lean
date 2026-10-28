import BbuKraken.Contracts
import BbuKraken.ModelLemmas
import BbuKraken.Kit

/-!
The spec of `build_bottom_up(m, n, source, target, dest, spilled, ops, blocked)`.
`s` is the state at the call: the first six arguments are in registers, `ops`
and `blocked` are the words at `rsp`. The model inputs are functions of `s`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

section
variable (s : MachineData)

abbrev mArg : Nat := (rdi s).toNat
abbrev nArg : Nat := (rsi s).toNat
abbrev srcArg : Addr := rdx s
abbrev tgtArg : Addr := rcx s
abbrev dstArg : Addr := r8 s
abbrev splArg : Addr := s.regs.get64 .r9
abbrev opsArg : Addr := rd s.dmem (rsp s)
abbrev blkArg : Addr := rd s.dmem (rsp s + 8#64)

def topEnv : Env where
  target := (List.range (nArg s)).map fun i => rd s.dmem (wordAt (tgtArg s) i)
  spilled := fun i => UInt8.ofBitVec (rdb s.dmem (splArg s + BitVec.ofNat 64 i))

def topSource : List Word := (List.range (mArg s)).map fun i => rd s.dmem (wordAt (srcArg s) i)

def topDests : List Nat :=
  (List.range (mArg s)).map fun i => (rd s.dmem (wordAt (dstArg s) i)).toNat

-- The spilled bytes of the variables in the target.
def topSpl : List (Addr × Nat) :=
  (List.range (nArg s)).filterMap fun d =>
    let v := (rd s.dmem (wordAt (tgtArg s) d)).toNat
    if 2 ≤ v ∧ v % 2 = 0 then some (splArg s + BitVec.ofNat 64 ((v - 2) / 2), 1) else none

-- The frame: the return address, two pushes, the struct and the frame of `finish`.
def topF : Nat := 8 + 16 + 4168 + finishF

-- The memory that `build_bottom_up` writes and reads.
def topOut : List (Addr × Nat) := [(opsArg s, 96 * nArg s), (blkArg s, 16)]
-- The inputs that the callees read: the target and the spilled bytes.
def topRd : List (Addr × Nat) := (tgtArg s, 8 * nArg s) :: topSpl s
def topIn : List (Addr × Nat) :=
  (rsp s, 16) :: (srcArg s, 8 * mArg s) :: (dstArg s, 8 * mArg s) :: topRd s

-- The arguments at `rsp`, `source` and `dest` are read before the first store to
-- the ops buffer or `blocked`, so these may overlap them. The arguments at `rsp`
-- lie above the frame. `m ≤ n` follows from `dests` (`TopPre.m_le`). The callees
-- need `tgt_lt`, `ops_lt` and `blk_lt` (`Wf`).
structure TopPre : Prop where
  n_le : nArg s ≤ 256
  dests : Dests (nArg s) (topDests s)
  mapped : Mem.Mapped (frame topF s :: topOut s ++ topIn s) s.dmem
  rsp_le : topF ≤ (rsp s).toNat
  tgt_lt : (tgtArg s).toNat + 8 * nArg s ≤ 2 ^ 64
  ops_lt : (opsArg s).toNat + 96 * nArg s ≤ 2 ^ 64
  blk_lt : (blkArg s).toNat + 16 ≤ 2 ^ 64
  disj_frame : Mem.Blocks.Disjoint [frame topF s]
    (topOut s ++ (srcArg s, 8 * mArg s) :: (dstArg s, 8 * mArg s) :: topRd s)
  disj_ops : Mem.Blocks.Disjoint [(opsArg s, 96 * nArg s)] (topRd s)
  disj_blk : Mem.Blocks.Disjoint [(blkArg s, 16)] (topRd s)

def topMod : Modifies :=
  ⟨[.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11], frame topF s :: topOut s⟩

-- Operation `i` in the ops buffer of `t`.
def topOp (t : MachineData) (i : Nat) : Op :=
  ⟨rd t.dmem (wordAt (opsArg s) (2 * i)), rd t.dmem (wordAt (opsArg s) (2 * i + 1))⟩

-- The result of `build_bottom_up` in `t` is the result of the model.
def TopPost (t : MachineData) : Prop :=
  Mem.Mapped [frame topF s] t.dmem ∧
  match buildBottomUp (topEnv s) (topSource s) (topDests s) with
  | .ok ops => rax t = BitVec.ofNat 64 ops.length ∧ (List.range ops.length).map (topOp s t) = ops
  | .error (.blocked pos excess) =>
    rax t = -1#64 ∧ rd t.dmem (blkArg s) = BitVec.ofNat 64 pos
      ∧ rd t.dmem (wordAt (blkArg s) 1) = BitVec.ofNat 64 excess
  | .error .assertion => rax t = -2#64

end

end Bbu

/-! # The proof of `buildBottomUp_body` -/

namespace Bbu
namespace TopProof

section
variable (s : MachineData)

-- The struct: at the bottom of the frame, below the two pushes and the padding.
abbrev bS : Addr := rsp s - 4192#64

def topRes : M (List Op) := buildBottomUp (topEnv s) (topSource s) (topDests s)

def st0 : St := ⟨List.zipWith Slot.mk (topSource s) (topDests s), nArg s - mArg s, []⟩
end

section
variable {s : MachineData}

theorem _root_.Bbu.TopPre.rsp_ge (hp : TopPre s) : 5008 ≤ (rsp s).toNat := by
  have := hp.rsp_le; simp only [topF, finishF] at this; omega

-- A list of distinct offsets below `n` has at most `n` entries.
theorem Dests.length_le {n : Nat} {l : List Nat} (h : Dests n l) : l.length ≤ n := by
  have hnd : l.Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij he => by
    have := h.2 i hi j hj he; omega
  have := hnd.length_le_of_subset (l₂ := List.range n) fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact List.mem_range.mpr (h.1 i hi)
  simpa using this

theorem _root_.Bbu.TopPre.m_le (hp : TopPre s) : mArg s ≤ nArg s := by
  simpa [topDests] using Dests.length_le hp.dests

theorem inside_head {x : Addr} {p : Addr × Nat} {l : List (Addr × Nat)}
    (h : Mem.Blocks.Inside x 1 [p]) : Mem.Blocks.Inside x 1 (p :: l) := by
  obtain ⟨a, k⟩ := p; exact h.elim Or.inl False.elim

-- The struct lies in the frame.
theorem struct_in_frame (hp : TopPre s) :
    ∀ x, Mem.Blocks.Inside x 1 [(bS s, 8 * WORDS)] → Mem.Blocks.Inside x 1 [frame topF s] := by
  intro x hx
  have := hp.rsp_ge
  simp only [Mem.Blocks.Inside, or_false, WORDS, topF, finishF, bS, rsp] at *
  bv_omega

theorem topOut_frame (hp : TopPre s) :
    ∀ x, Mem.Blocks.Inside x 1 (topOut s) → ¬ Mem.Blocks.Inside x 1 [frame topF s] :=
  fun x hx hf => hp.disj_frame x hf (inside_append.mpr (.inl hx))

theorem topRd_out (hp : TopPre s) :
    ∀ x, Mem.Blocks.Inside x 1 (topRd s) → ¬ Mem.Blocks.Inside x 1 (frame topF s :: topOut s) := by
  intro x hx hf
  rcases hf with hf | hf | hf | hf
  · exact hp.disj_frame x (Or.inl hf) (inside_append.mpr (.inr hx.tail.tail))
  · exact hp.disj_ops x (Or.inl hf) hx
  · exact hp.disj_blk x (Or.inl hf) hx
  · exact hf

theorem topRd_in {x : Addr} (h : Mem.Blocks.Inside x 1 (topRd s)) : Mem.Blocks.Inside x 1 (topIn s) :=
  h.tail.tail.tail

end

/-! ## The header and the inputs -/

section
variable (s : MachineData)

-- The memory `m` keeps the header words 3 to 7 and the bytes outside the
-- frame and the outputs.
structure Hd (m : Mem 64) : Prop where
  n : rd m (wordAt (bS s) 3) = rsi s
  tgt : rd m (wordAt (bS s) 4) = tgtArg s
  spl : rd m (wordAt (bS s) 5) = splArg s
  ops : rd m (wordAt (bS s) 6) = opsArg s
  blk : rd m (wordAt (bS s) 7) = blkArg s
  un : Mem.UnchangedOutside (frame topF s :: topOut s) s.dmem m
end

section
variable {s : MachineData} {m : Mem 64}

theorem Hd.rd_in (hp : TopPre s) (h : Hd s m) {a : Addr}
    (ha : ∀ y, Mem.Blocks.Inside y 1 [(a, 8)] → Mem.Blocks.Inside y 1 (topRd s)) :
    rd m a = rd s.dmem a :=
  rd_congr h.un fun y hy => topRd_out hp y (ha y hy)

theorem Hd.rdb_in (hp : TopPre s) (h : Hd s m) {a : Addr}
    (ha : ∀ y, Mem.Blocks.Inside y 1 [(a, 1)] → Mem.Blocks.Inside y 1 (topRd s)) :
    rdb m a = rdb s.dmem a :=
  rdb_congr h.un fun y hy => topRd_out hp y (ha y hy)

theorem Hd.tgt_rd (hp : TopPre s) (h : Hd s m) {d : Nat} (hd : d < nArg s) :
    rd m (wordAt (tgtArg s) d) = rd s.dmem (wordAt (tgtArg s) d) :=
  h.rd_in hp fun y hy => Or.inl (by
    have := hp.tgt_lt; have := hp.n_le
    simp only [Mem.Blocks.Inside, or_false, wordAt] at hy ⊢; bv_omega)

theorem Hd.nOf_eq (h : Hd s m) : nOf m (bS s) = nArg s := by unfold nOf; rw [h.n]

private theorem filterMap_congr {α β} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem Hd.spl_eq (hp : TopPre s) (h : Hd s m) : splBlocks m (bS s) = topSpl s := by
  unfold splBlocks topSpl
  simp only [nOf, tgtOf, splOf, h.n, h.tgt, h.spl]
  exact filterMap_congr fun d hd => by rw [h.tgt_rd hp (List.mem_range.mp hd)]

theorem Hd.w_sub (hp : TopPre s) (h : Hd s m) {x : Addr}
    (hx : Mem.Blocks.Inside x 1 (writable m (bS s))) :
    Mem.Blocks.Inside x 1 [(bS s, 8 * WORDS)] ∨ Mem.Blocks.Inside x 1 (topOut s) := by
  have := hp.rsp_ge
  simp only [writable, nOf, opsOf, blkOf, h.n, h.ops, h.blk] at hx
  rcases hx with hx | hx | hx | hx | hx
  · left; simp only [Mem.Blocks.Inside, or_false, WORDS, bS, rsp] at *; bv_omega
  · left; simp only [Mem.Blocks.Inside, or_false, WORDS, STACK, bS, rsp] at *; bv_omega
  · exact .inr (Or.inl hx)
  · exact .inr (Or.inr (Or.inl hx))
  · exact hx.elim

theorem Hd.r_sub (hp : TopPre s) (h : Hd s m) {x : Addr}
    (hx : Mem.Blocks.Inside x 1 (readable m (bS s))) :
    Mem.Blocks.Inside x 1 [(bS s, 8 * WORDS)] ∨ Mem.Blocks.Inside x 1 (topRd s) := by
  have := hp.rsp_ge
  simp only [readable, nOf, tgtOf, h.n, h.tgt, h.spl_eq hp] at hx
  rcases hx with hx | hx | hx
  · left; simp only [Mem.Blocks.Inside, or_false, WORDS, bS, rsp] at *; bv_omega
  · exact .inr (Or.inl hx)
  · exact .inr hx.tail

theorem Hd.map_all (hp : TopPre s) (h : Hd s m) (hmap : Mem.Mapped (frame topF s :: topOut s) m) :
    Mem.Mapped (frame topF s :: topOut s ++ topIn s) m :=
  Mapped.of_unchanged hp.mapped h.un hmap

theorem Hd.wf (hp : TopPre s) (h : Hd s m) (hmap : Mem.Mapped (frame topF s :: topOut s) m)
    (hlen : (rd m (wordAt (bS s) 0)).toNat ≤ 256) (hnops : (rd m (wordAt (bS s) 2)).toNat ≤ 6 * nArg s) :
    Wf m (bS s) := by
  have hge := hp.rsp_ge
  have hst := struct_in_frame hp
  have hsp := h.spl_eq hp
  simp only [splBlocks] at hsp
  refine ⟨fun x hx => h.map_all hp hmap x ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlen, ?_, ?_⟩
  · rcases inside_append.mp hx with hx | hx
    · rcases h.w_sub hp hx with hx | hx
      · exact inside_head (hst x hx)
      · exact (inside_append.mpr (.inl hx)).tail
    · rcases h.r_sub hp hx with hx | hx
      · exact inside_head (hst x hx)
      · exact (inside_append.mpr (.inr (topRd_in hx))).tail
  · simp only [WORDS, bS, rsp] at *; bv_omega
  · simp only [opsOf, nOf, h.ops, h.n]; exact hp.ops_lt
  · simp only [blkOf, h.blk]; exact hp.blk_lt
  · simp only [tgtOf, nOf, h.tgt, h.n]; exact hp.tgt_lt
  · simp only [opsOf, nOf, blkOf, tgtOf, splBlocks, splOf, h.ops, h.n, h.blk, h.tgt, h.spl] at hsp ⊢
    rw [hsp]
    intro x hx hr
    refine hp.disj_frame x (hst x hx) (inside_append.mpr ?_)
    rcases hr with hr | hr | hr | hr
    · exact .inl (Or.inl hr)
    · exact .inl (Or.inr (Or.inl hr))
    · exact .inr (Or.inr (Or.inr (Or.inl hr)))
    · exact .inr hr.tail.tail.tail
  · simp only [opsOf, nOf, tgtOf, splBlocks, splOf, h.ops, h.n, h.tgt, h.spl] at hsp ⊢
    rw [hsp]
    intro x hx hr
    refine hp.disj_ops x hx ?_
    rcases hr with hr | hr
    · exact Or.inl hr
    · exact hr.tail
  · simp only [nOf, blkOf, tgtOf, splBlocks, splOf, h.n, h.blk, h.tgt, h.spl] at hsp ⊢
    rw [hsp]
    intro x hx hr
    refine hp.disj_blk x hx ?_
    rcases hr with hr | hr
    · exact Or.inl hr
    · exact hr.tail
  · rw [h.nOf_eq]; exact hnops
  · rw [h.nOf_eq]; exact hp.n_le

end

/-! ## The memory of the body -/

section
variable (s : MachineData) (ra : Int64)

-- The memory `m` of the body: the saved words, the struct and the frame.
structure Fm (m : Mem 64) : Prop where
  hd : Hd s m
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  rbp : rd m (rsp s - 16#64) = s.regs.rbp.toBitVec
  rbx : rd m (rsp s - 24#64) = s.regs.rbx.toBitVec
  map : Mem.Mapped (frame topF s :: topOut s) m
  wf : Wf m (bS s)
end

section
variable {s : MachineData} {ra : Int64} {m : Mem 64}

-- The precondition of a callee with the struct at `rsp`.
theorem Fm.pre {F : Nat} {A : MachineData → Prop} {c : MachineData} (hp : TopPre s)
    (h : Fm s ra m) (hF : F ≤ finishF) (hc : c.dmem = m) (hrsp : rsp c = bS s)
    (hrdi : rdi c = bS s) (hA : A c) : Pre F A c := by
  have hge := hp.rsp_ge
  refine ⟨by rw [hc, hrdi]; exact h.wf, ⟨?_, fun x hx => ?_, ?_⟩, hA⟩
  · rw [hrsp]; simp only [finishF, bS, rsp] at *; bv_omega
  · rw [hc]
    refine h.map x (inside_head ?_)
    simp only [Mem.Blocks.Inside, or_false, hrsp, topF, finishF, bS, rsp] at *; bv_omega
  · rw [hc, hrdi]
    intro x hx hwr
    have hx' : Mem.Blocks.Inside x 1 [frame topF s] := by
      simp only [Mem.Blocks.Inside, or_false, hrsp, topF, finishF, bS, rsp] at *; bv_omega
    rcases inside_append.mp hwr with hw | hr
    · rcases h.hd.w_sub hp hw with hw | hw
      · simp only [Mem.Blocks.Inside, or_false, hrsp, WORDS, finishF, bS, rsp] at *; bv_omega
      · exact topOut_frame hp x hw hx'
    · rcases h.hd.r_sub hp hr with hr | hr
      · simp only [Mem.Blocks.Inside, or_false, hrsp, WORDS, finishF, bS, rsp] at *; bv_omega
      · exact topRd_out hp x hr (inside_head hx')

-- A callee with the struct at `rsp` keeps `Fm`.
theorem Fm.call {F : Nat} {A : MachineData → Prop} {R : MachineData → MachineData → Prop}
    {c t : MachineData} (hp : TopPre s) (h : Fm s ra m) (hF : F ≤ finishF) (hc : c.dmem = m)
    (hrsp : rsp c = bS s) (hrdi : rdi c = bS s) (hpre : Pre F A c) (hpost : Post F R c t)
    (hag : (mod F c).Agree c t) : Fm s ra t.dmem := by
  have hge := hp.rsp_ge
  have hu : Mem.UnchangedOutside (frame F c :: writable m (bS s)) m t.dmem := by
    have := hag.2; simp only [mod, hc, hrdi] at this; exact this
  have hdr : ∀ {k}, 3 ≤ k → k < 8 → rd t.dmem (wordAt (bS s) k) = rd m (wordAt (bS s) k) :=
    fun hk3 hk => by have := hdr_congr hag.2 hpre.disj hk3 hk; rwa [hrdi, hc] at this
  have hwr : writable t.dmem (bS s) = writable m (bS s) := by
    have := (Post.env hpre hag).2.2; rwa [hrdi, hc] at this
  -- The callee frame lies in the frame.
  have hcf : ∀ x, Mem.Blocks.Inside x 1 [frame F c] → Mem.Blocks.Inside x 1 [frame topF s] := by
    intro x hx; simp only [Mem.Blocks.Inside, or_false, hrsp, topF, finishF, bS, rsp] at *; bv_omega
  -- A saved word lies in neither the callee frame nor `writable`.
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 24 →
      rd t.dmem (rsp s - BitVec.ofNat 64 k) = rd m (rsp s - BitVec.ofNat 64 k) := fun hk hk' =>
    rd_congr hu fun x hx hl => by
      have hxf : Mem.Blocks.Inside x 1 [frame topF s] := by
        simp only [Mem.Blocks.Inside, or_false, topF, finishF, rsp] at *; bv_omega
      rcases hl with hl | hl
      · simp only [Mem.Blocks.Inside, or_false, hrsp, finishF, bS, rsp] at *; bv_omega
      · rcases h.hd.w_sub hp hl with hl | hl
        · simp only [Mem.Blocks.Inside, or_false, WORDS, bS, rsp] at *; bv_omega
        · exact topOut_frame hp x hl hxf
  have hun : ∀ x, ¬ Mem.Blocks.Inside x 1 (frame topF s :: topOut s) → t.dmem.get? x = m.get? x :=
    fun x hx => hu x fun hl => by
      rcases hl with hl | hl
      · exact hx (inside_head (hcf x (Or.inl hl)))
      · rcases h.hd.w_sub hp hl with hl | hl
        · exact hx (inside_head (struct_in_frame hp x hl))
        · exact hx hl.tail
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdr (by omega) (by omega)]; exact h.hd.n
  · rw [hdr (by omega) (by omega)]; exact h.hd.tgt
  · rw [hdr (by omega) (by omega)]; exact h.hd.spl
  · rw [hdr (by omega) (by omega)]; exact h.hd.ops
  · rw [hdr (by omega) (by omega)]; exact h.hd.blk
  · intro x hx; rw [hun x hx]; exact h.hd.un x hx
  · rw [show (8#64 : Addr) = BitVec.ofNat 64 8 from rfl, hsv (by omega) (by omega)]; exact h.ra
  · rw [show (16#64 : Addr) = BitVec.ofNat 64 16 from rfl, hsv (by omega) (by omega)]; exact h.rbp
  · rw [show (24#64 : Addr) = BitVec.ofNat 64 24 from rfl, hsv (by omega) (by omega)]; exact h.rbx
  · refine Mapped.of_unchanged h.map hu fun x hx => ?_
    rcases hx with hx | hx
    · exact hpost.2.1 x (Or.inl hx)
    · have := hpost.1.mapped x (inside_append.mpr (.inl (by rw [hrdi, hwr]; exact hx)))
      exact this
  · rw [← hrdi]; exact hpost.1

-- A store in the stack and dest arrays keeps `Fm`.
theorem Fm.store (hp : TopPre s) (h : Fm s ra m) {a : Addr}
    (ha : Mem.Blocks.Inside a 8 [(wordAt (bS s) STACK, 8 * 512)]) (v : Int) :
    Fm s ra (m.storeInt a 8 v) := by
  have hge := hp.rsp_ge
  have hu : Mem.UnchangedOutside [(wordAt (bS s) STACK, 8 * 512)] m (m.storeInt a 8 v) :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl) ha v
  have hreg : ∀ x, Mem.Blocks.Inside x 1 [(wordAt (bS s) STACK, 8 * 512)] →
      Mem.Blocks.Inside x 1 [(bS s, 8 * WORDS)] := by
    intro x hx; simp only [Mem.Blocks.Inside, or_false, WORDS, STACK, bS, rsp] at *; bv_omega
  have hk : ∀ {k}, k < 8 → rd (m.storeInt a 8 v) (wordAt (bS s) k) = rd m (wordAt (bS s) k) :=
    fun hk => rd_congr hu fun x hx hl => by
      simp only [Mem.Blocks.Inside, or_false, STACK, bS, rsp] at *; bv_omega
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 24 →
      rd (m.storeInt a 8 v) (rsp s - BitVec.ofNat 64 k) = rd m (rsp s - BitVec.ofNat 64 k) :=
    fun hk hk' => rd_congr hu fun x hx hl => by
      simp only [Mem.Blocks.Inside, or_false, STACK, bS, rsp] at *; bv_omega
  have hd : Hd s (m.storeInt a 8 v) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
    · rw [hk (by omega)]; exact h.hd.n
    · rw [hk (by omega)]; exact h.hd.tgt
    · rw [hk (by omega)]; exact h.hd.spl
    · rw [hk (by omega)]; exact h.hd.ops
    · rw [hk (by omega)]; exact h.hd.blk
    · rw [hu x fun hl => hx (inside_head (struct_in_frame hp x (hreg x hl)))]; exact h.hd.un x hx
  have hmap : Mem.Mapped (frame topF s :: topOut s) (m.storeInt a 8 v) := h.map.storeInt _ _ _
  refine ⟨hd, ?_, ?_, ?_, hmap, hd.wf hp hmap ?_ ?_⟩
  · rw [show (8#64 : Addr) = BitVec.ofNat 64 8 from rfl, hsv (by omega) (by omega)]; exact h.ra
  · rw [show (16#64 : Addr) = BitVec.ofNat 64 16 from rfl, hsv (by omega) (by omega)]; exact h.rbp
  · rw [show (24#64 : Addr) = BitVec.ofNat 64 24 from rfl, hsv (by omega) (by omega)]; exact h.rbx
  · rw [hk (by omega)]; exact h.wf.len_le
  · rw [hk (by omega), ← h.hd.nOf_eq]; exact h.wf.nops_le

/-! ## The model at the start -/

theorem Fm.env_n (h : Fm s ra m) : (envOf m (bS s)).n = nArg s := by
  simp only [Env.n, envOf, List.length_map, List.length_range, h.hd.nOf_eq]

theorem Fm.env (hp : TopPre s) (h : Fm s ra m) :
    buildBottomUp (envOf m (bS s)) (topSource s) (topDests s) = topRes s := by
  have ht : (envOf m (bS s)).target = (topEnv s).target := by
    simp only [envOf, topEnv, nOf, tgtOf, h.hd.n, h.hd.tgt]
    exact List.map_congr_left fun d hd => h.hd.tgt_rd hp (List.mem_range.mp hd)
  refine buildBottomUp_congr ht ?_ _ _
  intro v hv h2 he
  rw [ht] at hv
  simp only [topEnv, List.mem_map, List.mem_range] at hv
  obtain ⟨d, hd, rfl⟩ := hv
  have htv : tgtVar m (bS s) (((rd s.dmem (wordAt (tgtArg s) d)).toNat - 2) / 2) = true := by
    simp only [tgtVar, nOf, tgtOf, h.hd.n, h.hd.tgt, List.any_eq_true, List.mem_range]
    refine ⟨d, hd, ?_⟩
    simp only [h.hd.tgt_rd hp hd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    simp; exact ⟨h2, he⟩
  simp only [envOf, topEnv, htv, ite_true, splOf, h.hd.spl]
  congr 1
  refine h.hd.rdb_in hp fun y hy => ?_
  refine (inside_of_mem (List.mem_filterMap.mpr ⟨d, List.mem_range.mpr hd, ?_⟩) hy).tail
  simp only [h2, he, and_self, ite_true]

theorem length_topSource : (topSource s).length = mArg s := by simp [topSource]
theorem length_topDests : (topDests s).length = mArg s := by simp [topDests]

theorem Fm.init_loop (hp : TopPre s) (h : Fm s ra m) (hst : stOf m (bS s) = st0 s) :
    loop (envOf m (bS s)) (stOf m (bS s)) 0 = topRes s ∧ Inv (envOf m (bS s)) (stOf m (bS s)) 0 := by
  have hn := h.env_n
  have hsl : (envOf m (bS s)).n - (topSource s).length = nArg s - mArg s := by
    rw [hn, length_topSource]
  refine ⟨?_, ?_⟩
  · rw [hst, ← h.env hp, buildBottomUp, hsl]; rfl
  · have := Inv_init (e := envOf m (bS s)) (source := topSource s) (dests := topDests s)
      (by rw [length_topSource, length_topDests]) (by rw [length_topDests, hn]; exact hp.m_le)
      (by rw [hn]; exact hp.n_le) (by rw [hn]; exact hp.dests)
    rw [hsl] at this
    rw [hst]; exact this

/-! ## The struct after the entry block and the copy loop -/

-- Words 0 to 2 of the header at the start.
def H012 (m : Mem 64) : Prop :=
  rd m (wordAt (bS s) 0) = rdi s ∧ rd m (wordAt (bS s) 1) = rsi s - rdi s
    ∧ rd m (wordAt (bS s) 2) = 0#64

-- The first `i` stack and dest words are copies of the inputs.
def Copied (m : Mem 64) (i : Nat) : Prop :=
  ∀ j < i, rd m (wordAt (bS s) (STACK + j)) = rd s.dmem (wordAt (srcArg s) j)
    ∧ rd m (wordAt (bS s) (DEST + j)) = rd s.dmem (wordAt (dstArg s) j)


/-! ## The memory after the entry block -/

theorem Fm.mk0 (hp : TopPre s) (hu : Mem.UnchangedOutside [frame topF s] s.dmem m)
    (hmap : Mem.Mapped [frame topF s] m)
    (hra : rd m (rsp s - 8#64) = ra.toBitVec) (hrbp : rd m (rsp s - 16#64) = s.regs.rbp.toBitVec)
    (hrbx : rd m (rsp s - 24#64) = s.regs.rbx.toBitVec)
    (h0 : rd m (wordAt (bS s) 0) = rdi s) (h1 : rd m (wordAt (bS s) 1) = rsi s - rdi s)
    (h2 : rd m (wordAt (bS s) 2) = 0#64) (h3 : rd m (wordAt (bS s) 3) = rsi s)
    (h4 : rd m (wordAt (bS s) 4) = tgtArg s) (h5 : rd m (wordAt (bS s) 5) = splArg s)
    (h6 : rd m (wordAt (bS s) 6) = opsArg s) (h7 : rd m (wordAt (bS s) 7) = blkArg s) :
    Fm s ra m ∧ H012 (s := s) m := by
  have hun : Mem.UnchangedOutside (frame topF s :: topOut s) s.dmem m :=
    fun x hx => hu x fun h => hx (inside_head h)
  have hd : Hd s m := ⟨h3, h4, h5, h6, h7, hun⟩
  have hm : Mem.Mapped (frame topF s :: topOut s) m :=
    Mapped.of_unchanged (fun x hx => hp.mapped x (by
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact (inside_append.mpr (.inl hx)).tail)) hu hmap
  have hml := hp.m_le
  have hnl := hp.n_le
  refine ⟨⟨hd, hra, hrbp, hrbx, hm, hd.wf hp hm ?_ ?_⟩, h0, h1, h2⟩
  · rw [h0]; simp only [mArg, nArg] at *; omega
  · rw [h2]; simp
theorem st0_of (hp : TopPre s) (h0 : H012 (s := s) m) (hc : Copied (s := s) m (mArg s)) :
    stOf m (bS s) = st0 s := by
  obtain ⟨h0, h1, h2⟩ := h0
  have hml := hp.m_le
  simp only [stOf, st0, h0, h1, h2]
  congr 1
  · apply List.ext_getElem (by simp [topSource, topDests, mArg, rdi])
    intro j h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, topSource, topDests,
      slotOf, (hc j h1).1, (hc j h1).2]
  · simp only [mArg, nArg] at hml ⊢; bv_omega

end

/-! ## The invariants -/

section
variable (s : MachineData) (ra : Int64)

-- The registers at the labels after the entry block.
structure Rg (t : MachineData) : Prop where
  rsp : t.regs.rsp.toBitVec = bS s
  rbx : t.regs.rbx.toBitVec = rsi s
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

-- `.LB110`: the copy loop at the index `i` in `rax`. Only the frame changed, so the
-- inputs are as at the start.
def At110 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧ t.regs.rdi.toBitVec = rdi s ∧ t.regs.rsi.toBitVec = srcArg s
    ∧ t.regs.r8.toBitVec = dstArg s ∧ t.regs.rax.toNat < mArg s ∧ H012 (s := s) t.dmem
    ∧ Copied (s := s) t.dmem t.regs.rax.toNat
    ∧ Mem.UnchangedOutside [frame topF s] s.dmem t.dmem

-- `.LB109`: no sources.
def At109 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧ mArg s = 0 ∧ t.regs.rsi.toBitVec = rsi s ∧ stOf t.dmem (bS s) = st0 s

-- `.LB115`: the model state is the start state.
def At115 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧ 0 < nArg s ∧ stOf t.dmem (bS s) = st0 s

-- `.LB114`: the loop at the offset `t` in `rsi`.
def At114 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧ t.regs.rbp.toBitVec = bS s ∧ t.regs.rsi.toNat < nArg s
    ∧ Inv (envOf t.dmem (bS s)) (stOf t.dmem (bS s)) t.regs.rsi.toNat
    ∧ loop (envOf t.dmem (bS s)) (stOf t.dmem (bS s)) t.regs.rsi.toNat = topRes s

-- `.LB111`: the loop is done.
def At111 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧
    (if (stOf t.dmem (bS s)).len = nArg s then .ok (stOf t.dmem (bS s)).ops else .error .assertion)
      = topRes s

-- `.LB116`: the result is the ops in the struct.
def At116 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧ topRes s = .ok (stOf t.dmem (bS s)).ops

-- `.LB122`: `step` returned `finish`.
def At122 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧
    (if (stOf t.dmem (bS s)).len = nArg s then finish (stOf t.dmem (bS s)) else .error .assertion)
      = topRes s
    ∧ IsPerm ((stOf t.dmem (bS s)).slots.map Slot.dest)
    ∧ (stOf t.dmem (bS s)).ops.length + 2 * (stOf t.dmem (bS s)).len ≤ 6 * nArg s

-- `.LB117` and `.LB118`: the result is an assertion failure.
def AtErr (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧ topRes s = .error .assertion

-- The result in `rax` and memory.
def Out (t : MachineData) : Prop :=
  match topRes s with
  | .ok ops => rax t = BitVec.ofNat 64 ops.length ∧ (List.range ops.length).map (topOp s t) = ops
  | .error (.blocked pos excess) =>
    rax t = -1#64 ∧ rd t.dmem (blkArg s) = BitVec.ofNat 64 pos
      ∧ rd t.dmem (wordAt (blkArg s) 1) = BitVec.ofNat 64 excess
  | .error .assertion => rax t = -2#64

-- `.LB108`: the result is in `rax`.
def At108 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ Rg s t ∧ Out s t

-- The variant.
def V : Label → MachineData → Nat
  | "build_bottom_up", _ => 2 ^ 21
  | ".LB110", t => 2 ^ 20 + 2 + (mArg s - t.regs.rax.toNat)
  | ".LB109", _ => 2 ^ 20 + 1
  | ".LB115", _ => 2 ^ 20
  | ".LB114", t => (nArg s - t.regs.rsi.toNat) * 512 + (stOf t.dmem (bS s)).pending + 2
  | ".LB111", _ | ".LB116", _ | ".LB122", _ | ".LB117", _ | ".LB118", _ => 1
  | _, _ => 0

end


section
variable {s : MachineData} {ra : Int64}

-- The entry block jumps to `.LB110`.
theorem at110_entry {t : MachineData} (h : Fm s ra t.dmem ∧ H012 (s := s) t.dmem) (hrg : Rg s t)
    (hdi : t.regs.rdi.toBitVec = rdi s) (hsi : t.regs.rsi.toBitVec = srcArg s)
    (h8 : t.regs.r8.toBitVec = dstArg s) (hax : t.regs.rax.toNat = 0) (hm : 0 < mArg s)
    (hu : Mem.UnchangedOutside [frame topF s] s.dmem t.dmem) :
    At110 s ra t :=
  ⟨h.1, hrg, hdi, hsi, h8, by omega, h.2, by rw [hax]; intro j hj; omega, hu⟩

-- The entry block jumps to `.LB109`.
theorem at109_entry (hp : TopPre s) {t : MachineData} (h : Fm s ra t.dmem ∧ H012 (s := s) t.dmem)
    (hrg : Rg s t) (hm : mArg s = 0) (hsi : t.regs.rsi.toBitVec = rsi s) : At109 s ra t :=
  ⟨h.1, hrg, hm, hsi, st0_of hp h.2 (by rw [hm]; intro j hj; omega)⟩

end
end TopProof
end Bbu

namespace Bbu
namespace TopProof

-- The registers and the arguments as `s.regs.r.toBitVec`.
macro "top_nrm" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [bS, rsp, rdi,
  rsi, rdx, rcx, r8, rax, srcArg, dstArg, tgtArg, splArg, mArg, nArg, wordAt, STACK, DEST,
  Reg64s.get64_rsp, Reg64s.get64_rdi, Reg64s.get64_rsi, Reg64s.get64_rdx, Reg64s.get64_rcx,
  Reg64s.get64_r8, Reg64s.get64_r9, Reg64s.get64_rax, Nat.reduceMul, Nat.reduceAdd] $(loc)?)

section
variable (s : MachineData) (ra : Int64)

/-! ## The memory after the entry block, in the form of the `kvcgen64` goals -/

abbrev eR : Addr := s.regs.rsp.toBitVec
abbrev eS : Addr := eR s - 8#64 - 8#64 - 8#64 - 4168#64

def eM3 : Mem 64 :=
  ((s.dmem.storeInt (eR s - 8#64) 8 ra.toBitVec.toInt).storeInt (eR s - 8#64 - 8#64) 8
    s.regs.rbp.toBitVec.toInt).storeInt (eR s - 8#64 - 8#64 - 8#64) 8 s.regs.rbx.toBitVec.toInt

def eM9 : Mem 64 :=
  ((((((eM3 s ra).storeInt (eS s) 8 s.regs.rdi.toBitVec.toInt).storeInt (eS s + 8#64) 8
    (s.regs.rsi.toBitVec - s.regs.rdi.toBitVec).toInt).storeInt (eS s + 16#64) 8 0).storeInt
    (eS s + 24#64) 8 s.regs.rsi.toBitVec.toInt).storeInt (eS s + 32#64) 8
    s.regs.rcx.toBitVec.toInt).storeInt (eS s + 40#64) 8 s.regs.r9.toBitVec.toInt

def eM10 : Mem 64 :=
  (eM9 s ra).storeInt (eS s + 48#64) 8 (BitVec.toInt (rd (eM9 s ra) (eS s + 4192#64)))

def eM : Mem 64 :=
  (eM10 s ra).storeInt (eS s + 56#64) 8 (BitVec.toInt (rd (eM10 s ra) (eS s + 4200#64)))
end

section
variable {s : MachineData} {ra : Int64}

theorem eS_eq : eS s = bS s := by simp only [eS, eR, bS, rsp, Reg64s.get64_rsp]; bv_omega

-- The memory after one round of the copy loop, in the form of the `kvcgen64` goals.
def cpM (m : Mem 64) (R SI R8 A : Addr) : Mem 64 :=
  (m.storeInt (R + A * 8#64 + 64#64) 8 (BitVec.toInt (rd m (SI + A * 8#64)))).storeInt
    (R + A * 8#64 + 2112#64) 8
    (BitVec.toInt (rd (m.storeInt (R + A * 8#64 + 64#64) 8 (BitVec.toInt (rd m (SI + A * 8#64))))
      (R8 + A * 8#64)))

-- A load in the frame or in the stack arguments succeeds.
theorem ent_isSome (hp : TopPre s) {a : Addr}
    (h : (a - (s.regs.rsp.toBitVec - 5008#64)).toNat + 8 ≤ 5008
      ∨ (a - s.regs.rsp.toBitVec).toNat + 8 ≤ 16) : (s.dmem.loadInt a 8).isSome := by
  rcases h with h | h
  · exact hp.mapped.loadInt_isSome (Or.inl h)
  · exact hp.mapped.loadInt_isSome (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem and4_of {a b c d : Prop} (h : a ∧ b ∧ c) (hd : d) : a ∧ b ∧ c ∧ d := ⟨h.1, h.2.1, h.2.2, hd⟩

set_option maxHeartbeats 1000000 in
theorem copy_step (hp : TopPre s) {m : Mem 64} (h : Fm s ra m) (h0 : H012 (s := s) m)
    {i : Nat} (hc : Copied (s := s) m i) (hu : Mem.UnchangedOutside [frame topF s] s.dmem m)
    {R SI R8 A : Addr} (hR : R = bS s) (hSI : SI = srcArg s)
    (h8 : R8 = dstArg s) (hA : A.toNat = i) (hi : i < mArg s) :
    Fm s ra (cpM m R SI R8 A) ∧ H012 (s := s) (cpM m R SI R8 A)
      ∧ Copied (s := s) (cpM m R SI R8 A) (i + 1)
      ∧ Mem.UnchangedOutside [frame topF s] s.dmem (cpM m R SI R8 A) := by
  subst hR hSI h8 hA
  have hge := hp.rsp_ge
  have hml := hp.m_le
  have hnl := hp.n_le
  top_nrm at hge hml hnl hi
  -- The source and dest words are not in the frame.
  have hsrc : rd m (srcArg s + A * 8#64) = rd s.dmem (wordAt (srcArg s) A.toNat) := by
    rw [rd_congr hu fun y hy hl => hp.disj_frame y hl (inside_append.mpr (.inr (Or.inl (by
      simp only [Mem.Blocks.Inside, or_false] at hy ⊢; top_nrm at hy ⊢; bv_omega))))]
    refine congrArg (rd s.dmem) ?_
    top_nrm; bv_omega
  have hdst : rd m (dstArg s + A * 8#64) = rd s.dmem (wordAt (dstArg s) A.toNat) := by
    rw [rd_congr hu fun y hy hl => hp.disj_frame y hl (inside_append.mpr (.inr (Or.inr (Or.inl (by
      simp only [Mem.Blocks.Inside, or_false] at hy ⊢; top_nrm at hy ⊢; bv_omega)))))]
    refine congrArg (rd s.dmem) ?_
    top_nrm; bv_omega
  have hdis : ∀ v, rd (m.storeInt (bS s + A * 8#64 + 64#64) 8 v) (dstArg s + A * 8#64)
      = rd m (dstArg s + A * 8#64) := fun v =>
    rd_storeInt_of_disjoint fun y hy1 hy2 => hp.disj_frame y
      (by simp only [Mem.Blocks.Inside, or_false, topF, finishF, Nat.reduceAdd] at hy1 ⊢
          top_nrm at hy1 ⊢; bv_omega)
      (inside_append.mpr (.inr (Or.inr (Or.inl (by
        simp only [Mem.Blocks.Inside, or_false] at hy2 ⊢; top_nrm at hy2 ⊢; bv_omega)))))
  have hcp : cpM m (bS s) (srcArg s) (dstArg s) A
      = (m.storeInt (bS s + A * 8#64 + 64#64) 8 (rd m (srcArg s + A * 8#64)).toInt).storeInt
        (bS s + A * 8#64 + 2112#64) 8 (rd m (dstArg s + A * 8#64)).toInt := by
    simp only [cpM, hdis]
  rw [hcp]
  refine and4_of ?_ ((hu.storeInt ?_ _).storeInt ?_ _)
  rotate_left
  · simp only [Mem.Blocks.Inside, or_false, topF, finishF, Nat.reduceAdd]; top_nrm; bv_omega
  · simp only [Mem.Blocks.Inside, or_false, topF, finishF, Nat.reduceAdd]; top_nrm; bv_omega
  clear hcp hdis hu
  have hc' := fun j hj => hc j hj
  obtain ⟨e0, e1, e2⟩ := h0
  simp only [Copied, H012] at *
  top_nrm at *
  have h1 := h.store hp (a := s.regs.rsp.toBitVec - 4192#64 + A * 8#64 + 64#64)
    (by simp only [Mem.Blocks.Inside, or_false]; top_nrm; bv_omega)
    (BitVec.toInt (rd m (s.regs.rdx.toBitVec + A * 8#64)))
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · exact h1.store hp (by simp only [Mem.Blocks.Inside, or_false]; top_nrm; bv_omega) _
  · bbu_rd
    exact ⟨e0, e1, e2⟩
  · by_cases hj' : j < A.toNat
    · obtain ⟨c1, c2⟩ := hc' j hj'
      bbu_rd
      exact ⟨c1, c2⟩
    · have hjA : j = A.toNat := by omega
      subst hjA
      bbu_rd
      exact ⟨hsrc, hdst⟩

section
variable {t t' : MachineData}

-- The memory after one round of the copy loop at `.LB110`.
theorem at110_mem (hp : TopPre s) (h : At110 s ra t)
    (hm : t'.dmem = cpM t.dmem t.regs.rsp.toBitVec t.regs.rsi.toBitVec t.regs.r8.toBitVec
      t.regs.rax.toBitVec) :
    Fm s ra t'.dmem ∧ H012 (s := s) t'.dmem ∧ Copied (s := s) t'.dmem (t.regs.rax.toNat + 1)
      ∧ Mem.UnchangedOutside [frame topF s] s.dmem t'.dmem := by
  obtain ⟨hfm, hrg, -, hsi, h8, hax, h012, hcp, hu⟩ := h
  rw [hm]; exact copy_step hp hfm h012 hcp hu hrg.rsp hsi h8 rfl hax

theorem at110_next (hp : TopPre s) (h : At110 s ra t)
    (hm : t'.dmem = cpM t.dmem t.regs.rsp.toBitVec t.regs.rsi.toBitVec t.regs.r8.toBitVec
      t.regs.rax.toBitVec) (hrg : Rg s t') (hdi : t'.regs.rdi.toBitVec = rdi s)
    (hsi : t'.regs.rsi.toBitVec = srcArg s) (h8 : t'.regs.r8.toBitVec = dstArg s)
    (hax : t'.regs.rax.toNat = t.regs.rax.toNat + 1) (hlt : t'.regs.rax.toNat < mArg s) :
    At110 s ra t' := by
  obtain ⟨c1, c2, c3, c4⟩ := at110_mem hp h hm
  exact ⟨c1, hrg, hdi, hsi, h8, hlt, c2, hax ▸ c3, c4⟩

theorem at115_next (hp : TopPre s) (h : At110 s ra t)
    (hm : t'.dmem = cpM t.dmem t.regs.rsp.toBitVec t.regs.rsi.toBitVec t.regs.r8.toBitVec
      t.regs.rax.toBitVec) (hrg : Rg s t') (hax : t.regs.rax.toNat + 1 = mArg s)
    (hn : 0 < nArg s) : At115 s ra t' := by
  obtain ⟨c1, c2, c3, -⟩ := at110_mem hp h hm
  exact ⟨c1, hrg, hn, st0_of hp c2 (hax ▸ c3)⟩

-- `.LB115` jumps to `.LB114` with `t = 0`.
theorem at114_init (hp : TopPre s) (h : At115 s ra t) (hm : t'.dmem = t.dmem) (hrg : Rg s t')
    (hbp : t'.regs.rbp.toBitVec = bS s) (hsi : t'.regs.rsi.toNat = 0) :
    At114 s ra t' ∧ (nArg s - t'.regs.rsi.toNat) * 512 + (stOf t'.dmem (bS s)).pending + 2 < 2 ^ 20 := by
  obtain ⟨hfm, -, hn, hst⟩ := h
  unfold At114; rw [hm]
  obtain ⟨h1, h2⟩ := hfm.init_loop hp hst
  have hnl := hp.n_le
  rw [hsi]
  refine ⟨⟨hfm, hrg, hbp, hn, h2, h1⟩, ?_⟩
  rw [hst]; simp only [st0]; omega

-- The loads of the copy loop succeed.
theorem at110_some (hp : TopPre s) (h : At110 s ra t) {a : Addr}
    (ha : a = t.regs.rsi.toBitVec + t.regs.rax.toBitVec * 8#64
      ∨ a = t.regs.r8.toBitVec + t.regs.rax.toBitVec * 8#64
      ∨ a = t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 64#64
      ∨ a = t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 2112#64) :
    (t.dmem.loadInt a 8).isSome := by
  obtain ⟨hfm, hrg, -, hsi, h8, hax, -, -, -⟩ := h
  have hmap := hfm.hd.map_all hp hfm.map
  have hge := hp.rsp_ge
  have hml := hp.m_le
  have hnl := hp.n_le
  have hr := hrg.rsp
  have hax' : t.regs.rax.toBitVec.toNat < mArg s := hax
  top_nrm at hge hml hnl hr hax' hsi h8
  rcases ha with rfl | rfl | rfl | rfl
  · exact hmap.loadInt_isSome (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      top_nrm; bv_omega))))))
  · exact hmap.loadInt_isSome (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      top_nrm; bv_omega)))))))
  all_goals exact hmap.loadInt_isSome (Or.inl (by
    simp only [topF, finishF, Nat.reduceAdd]; top_nrm; bv_omega))
end

-- The entry block writes only in the frame.
set_option maxHeartbeats 1000000 in
theorem ent_un (hp : TopPre s) : Mem.UnchangedOutside [frame topF s] s.dmem (eM s ra) := by
  have hge := hp.rsp_ge
  simp only [rsp, Reg64s.get64_rsp] at hge
  simp only [eM, eM10, eM9, eM3]
  repeat (refine Mem.UnchangedOutside.storeInt ?_ (by
    simp only [Mem.Blocks.Inside, topF, finishF, rsp, Reg64s.get64_rsp, Nat.reduceAdd,
      or_false, eS, eR]
    bv_omega) _)
  exact fun _ _ => rfl

set_option maxHeartbeats 1000000 in
theorem ent_fm (hp : TopPre s) : Fm s ra (eM s ra) ∧ H012 (s := s) (eM s ra) := by
  have hge := hp.rsp_ge
  simp only [rsp, Reg64s.get64_rsp] at hge
  refine Fm.mk0 hp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ent_un hp
  · simp only [eM, eM10, eM9, eM3]
    repeat (refine Mem.Mapped.storeInt ?_ _ _ _)
    exact fun x hx => hp.mapped x (inside_head hx)
  all_goals
    simp only [eM, eM10, eM9, eM3, eS, eR, wordAt, bS, rsp, Reg64s.get64_rsp, Nat.reduceMul,
      BitVec.add_zero, opsArg, blkArg, tgtArg, splArg]
    bbu_rd
  all_goals first
    | (simp only [rdi, rsi, rcx, Reg64s.get64_rdi, Reg64s.get64_rsi, Reg64s.get64_rcx,
        Reg64s.get64_r9]; done)
    | (refine congrArg (rd s.dmem) ?_; bv_omega)

end

end TopProof
end Bbu

namespace Bbu
namespace TopProof

/-! ## The call to `step` at `.LB114` -/

section
variable (s : MachineData) (ra : Int64)

-- The state `u` after the call to `step` at `.LB114` in `t`.
structure Aft (t u : MachineData) : Prop where
  at114 : At114 s ra t
  fm : Fm s ra u.dmem
  rg : Rg s u
  rbp : u.regs.rbp.toBitVec = bS s
  env : envOf u.dmem (bS s) = envOf t.dmem (bS s)
  res : Res (bS s) (step (envOf t.dmem (bS s)) (stOf t.dmem (bS s)) t.regs.rsi.toNat)
    (fun r => rax u = encNext r.2 ∧ stOf u.dmem (bS s) = r.1) u
end

section
variable {s : MachineData} {ra : Int64} {t c u u' : MachineData}

theorem Res.imp {α : Type} {S : Addr} {r : M α} {Q Q' : α → Prop} {t : MachineData}
    (h : Res S r Q t) (hq : ∀ a, Q a → Q' a) : Res S r Q' t := by
  cases r with
  | error e => cases e <;> exact h
  | ok a => exact hq a h

theorem Rg.of_regs (h : Rg s u) (hr : u'.regs = u.regs) : Rg s u' :=
  ⟨by rw [hr]; exact h.rsp, by rw [hr]; exact h.rbx, by rw [hr]; exact h.r12, by rw [hr]; exact h.r13,
    by rw [hr]; exact h.r14, by rw [hr]; exact h.r15⟩

-- The precondition of `step` at `.LB114`.
theorem at114_pre (hp : TopPre s) (h : At114 s ra t) (hc : c.dmem = t.dmem)
    (hrsp : c.regs.rsp.toBitVec = bS s) (hdi : c.regs.rdi.toBitVec = bS s)
    (hsi : c.regs.rsi = t.regs.rsi) : Pre stepF stepA c := by
  obtain ⟨hfm, -, -, hlt, hinv, -⟩ := h
  have hn := hfm.env_n
  have hdi' : rdi c = bS s := hdi
  have hsi' : (rsi c).toNat = t.regs.rsi.toNat := by simp only [rsi, Reg64s.get64_rsi, hsi]; rfl
  refine Fm.pre hp hfm (by decide) hc hrsp hdi ?_
  have hl := hinv.lt (by rw [hn]; exact hlt)
  unfold stepA env st cap
  rw [hc, hdi', hsi', hn, hfm.hd.nOf_eq]
  rw [hn] at hl
  exact ⟨hlt, hl.1, hl.2⟩

theorem aft_mk (hpost : Post stepF stepR c u) (hag : (mod stepF c).Agree c u) (hp : TopPre s)
    (h : At114 s ra t) (hc : c.dmem = t.dmem) (hrg : Rg s c)
    (hbp : c.regs.rbp = t.regs.rbp) (hdi : c.regs.rdi.toBitVec = bS s)
    (hsi : c.regs.rsi = t.regs.rsi) : Aft s ra t u := by
  have hpre := at114_pre hp h hc hrg.rsp hdi hsi
  have hdi' : rdi c = bS s := hdi
  have hsi' : (rsi c).toNat = t.regs.rsi.toNat := by simp only [rsi, Reg64s.get64_rsi, hsi]; rfl
  have hreg : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] →
      u.regs.get64 q = c.regs.get64 q := fun q hq => hag.1 q hq
  refine ⟨h, Fm.call hp h.1 (by decide) hc hrg.rsp hdi' hpre hpost hag, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · have := hreg .rsp (by simp); simp only [Reg64s.get64_rsp] at this; rw [this]; exact hrg.rsp
  · have := hreg .rbx (by simp); simp only [Reg64s.get64_rbx] at this; rw [this]; exact hrg.rbx
  · have := hreg .r12 (by simp); simp only [Reg64s.get64_r12] at this
    exact (UInt64.toBitVec_inj.mp this).trans hrg.r12
  · have := hreg .r13 (by simp); simp only [Reg64s.get64_r13] at this
    exact (UInt64.toBitVec_inj.mp this).trans hrg.r13
  · have := hreg .r14 (by simp); simp only [Reg64s.get64_r14] at this
    exact (UInt64.toBitVec_inj.mp this).trans hrg.r14
  · have := hreg .r15 (by simp); simp only [Reg64s.get64_r15] at this
    exact (UInt64.toBitVec_inj.mp this).trans hrg.r15
  · have := hreg .rbp (by simp); simp only [Reg64s.get64_rbp] at this; rw [this, hbp]
    exact h.2.2.1
  · have : envOf u.dmem (rdi c) = envOf c.dmem (rdi c) := (Post.env hpre hag).1
    rw [hdi', hc] at this; exact this
  · have := hpost.2.2
    simp only [stepR, env, st] at this
    rw [hdi', hc, hsi'] at this
    refine Res.imp this fun a ha => ?_
    simp only [Ok, st'] at ha
    rw [hdi'] at ha; exact ha

-- `step` returned `.next t'`: `rax` is `t'`.
theorem aft_next_of (h : Aft s ra t u) {st' : St} {t' : Nat}
    (hstp : step (envOf t.dmem (bS s)) (stOf t.dmem (bS s)) t.regs.rsi.toNat = .ok (st', .next t')) :
    u.regs.rax.toNat = t' ∧ stOf u.dmem (bS s) = st' ∧ Inv (envOf t.dmem (bS s)) st' t' := by
  obtain ⟨⟨hfm0, -, -, hlt, hinv, -⟩, -, -, -, -, hres⟩ := h
  have hn := hfm0.env_n
  have hlt' : t.regs.rsi.toNat < (envOf t.dmem (bS s)).n := by rw [hn]; exact hlt
  have hi := step_inv hinv hlt' hstp
  have h1 := hi.t_le
  have h2 := hi.n_le
  rw [hstp] at hres
  obtain ⟨hr, hst⟩ := hres
  refine ⟨?_, hst, hi⟩
  simp only [encNext, rax] at hr
  show u.regs.rax.toBitVec.toNat = t'
  rw [show u.regs.rax.toBitVec = BitVec.ofNat 64 t' from hr, BitVec.toNat_ofNat]
  omega

-- `step` returned `finish`: the jump to `.LB122`.
theorem aft_finish (h : Aft s ra t u) (hax : u.regs.rax.toBitVec = -3#64)
    (hr : u'.regs = u.regs) (hm : u'.dmem = u.dmem) : At122 s ra u' := by
  have hnx := @aft_next_of _ _ _ _ h
  obtain ⟨⟨hfm0, -, -, hlt, hinv, hloop⟩, hfm, hrg, -, -, hres⟩ := h
  have hn := hfm0.env_n
  have hlt' : t.regs.rsi.toNat < (envOf t.dmem (bS s)).n := by rw [hn]; exact hlt
  unfold At122
  rw [hm]
  refine ⟨hfm, hrg.of_regs hr, ?_⟩
  generalize hstp : step (envOf t.dmem (bS s)) (stOf t.dmem (bS s)) t.regs.rsi.toNat = r at hres hnx
  rcases r with err | ⟨st', t' | _⟩
  · have hra : u.regs.rax.toBitVec = -1#64 ∨ u.regs.rax.toBitVec = -2#64 := by
      rcases err with ⟨pos, ex⟩ | _
      · exact .inl hres.1
      · exact .inr hres
    rw [hax] at hra; exact absurd hra (by decide)
  · obtain ⟨h1, -, hi⟩ := hnx rfl
    have := hi.n_le
    have := hi.t_le
    rw [hn] at this
    have h3 : u.regs.rax.toBitVec.toNat = t' := h1
    rw [hax] at h3; simp at h3; omega
  · obtain ⟨-, hst⟩ := hres
    obtain ⟨rfl, hpd⟩ := step_finish hstp
    rw [hst, ← hloop, loop_finish hlt' hstp, hn]
    have := hinv.finish hpd
    rw [hn] at this
    exact ⟨rfl, this⟩

-- `step` returned an error: the jump to `.LB108`.
theorem aft_err (h : Aft s ra t u) (hne : u.regs.rax.toBitVec ≠ -3#64)
    (hms : u.regs.rax.toBitVec.msb = true) (hr : u'.regs = u.regs) (hm : u'.dmem = u.dmem) :
    At108 s ra u' := by
  have hnx := @aft_next_of _ _ _ _ h
  obtain ⟨⟨hfm0, -, -, hlt, -, hloop⟩, hfm, hrg, -, -, hres⟩ := h
  have hn := hfm0.env_n
  have hlt' : t.regs.rsi.toNat < (envOf t.dmem (bS s)).n := by rw [hn]; exact hlt
  have hax : rax u' = rax u := by simp only [rax, hr]
  unfold At108 Out
  rw [hm, hax]
  refine ⟨hfm, hrg.of_regs hr, ?_⟩
  generalize hstp : step (envOf t.dmem (bS s)) (stOf t.dmem (bS s)) t.regs.rsi.toNat = r at hres hnx
  rcases r with err | ⟨st', t' | _⟩
  · rw [← hloop, loop_error hlt' hstp]
    rcases err with ⟨pos, ex⟩ | _
    · obtain ⟨h1, h2, h3⟩ := hres
      rw [show blkOf u.dmem (bS s) = blkArg s from hfm.hd.blk] at h2 h3
      exact ⟨h1, h2, h3⟩
    · exact hres
  · obtain ⟨h1, -, hi⟩ := hnx rfl
    have := hi.n_le
    have := hi.t_le
    have h3 : u.regs.rax.toBitVec.toNat = t' := h1
    rw [BitVec.msb_eq_decide] at hms
    simp only [decide_eq_true_eq] at hms
    omega
  · exact absurd hres.1 hne

-- `step` returned `.next t'` with `t' < n`: the jump back to `.LB114`.
theorem aft_next (h : Aft s ra t u) (hlt : u.regs.rax.toNat < nArg s) (hrg : Rg s u')
    (hbp : u'.regs.rbp = u.regs.rbp) (hsi : u'.regs.rsi = u.regs.rax) (hm : u'.dmem = u.dmem) :
    At114 s ra u' ∧ (nArg s - u'.regs.rsi.toNat) * 512 + (stOf u'.dmem (bS s)).pending + 2
      < (nArg s - t.regs.rsi.toNat) * 512 + (stOf t.dmem (bS s)).pending + 2 := by
  have hnx := @aft_next_of _ _ _ _ h
  obtain ⟨⟨hfm0, -, -, hlt0, hinv, hloop⟩, hfm, -, hbp0, henv, hres⟩ := h
  have hn := hfm0.env_n
  have hlt' : t.regs.rsi.toNat < (envOf t.dmem (bS s)).n := by rw [hn]; exact hlt0
  unfold At114
  rw [hm, hsi, henv]
  generalize hstp : step (envOf t.dmem (bS s)) (stOf t.dmem (bS s)) t.regs.rsi.toNat = r at hres hnx
  rcases r with err | ⟨st', t' | _⟩
  · have hra : u.regs.rax.toBitVec = -1#64 ∨ u.regs.rax.toBitVec = -2#64 := by
      rcases err with ⟨pos, ex⟩ | _
      · exact .inl hres.1
      · exact .inr hres
    have h3 : u.regs.rax.toBitVec.toNat < nArg s := hlt
    have := hinv.n_le; rw [hn] at this
    rcases hra with hra | hra <;> rw [hra] at h3 <;> simp at h3 <;> omega
  · obtain ⟨h1, h2, hi⟩ := hnx rfl
    rw [h1, h2]
    have hl := hi.len_pending
    rw [hn] at hl
    refine ⟨⟨hfm, hrg, by rw [hbp]; exact hbp0, by rw [← h1]; exact hlt, hi,
      by rw [← hloop, loop_next hlt' hstp]⟩, ?_⟩
    have := hinv.n_le; rw [hn] at this
    rcases step_progress hstp with h4 | ⟨h4, h5⟩ <;> omega
  · have h3 : u.regs.rax.toBitVec.toNat < nArg s := hlt
    have := hinv.n_le; rw [hn] at this
    rw [show u.regs.rax.toBitVec = -3#64 from hres.1] at h3
    simp at h3; omega

theorem aft_next_V (h : Aft s ra t u) (hlt : u.regs.rax.toNat < nArg s) (hrg : Rg s u')
    (hbp : u'.regs.rbp = u.regs.rbp) (hsi : u'.regs.rsi = u.regs.rax) (hm : u'.dmem = u.dmem) :
    V s ".LB114" u' < V s ".LB114" t :=
  (aft_next h hlt hrg hbp hsi hm).2

-- `step` returned `.next t'` with `n ≤ t'`: the fall through to `.LB111`.
theorem aft_done (h : Aft s ra t u) (hne : u.regs.rax.toBitVec ≠ -3#64)
    (hms : u.regs.rax.toBitVec.msb = false) (hge : ¬ u.regs.rax.toNat < nArg s)
    (hrg' : Rg s u') (hm : u'.dmem = u.dmem) : At111 s ra u' := by
  have hnx := @aft_next_of _ _ _ _ h
  obtain ⟨⟨hfm0, -, -, hlt0, -, hloop⟩, hfm, -, -, henv, hres⟩ := h
  have hn := hfm0.env_n
  have hlt' : t.regs.rsi.toNat < (envOf t.dmem (bS s)).n := by rw [hn]; exact hlt0
  unfold At111
  rw [hm]
  refine ⟨hfm, hrg', ?_⟩
  generalize hstp : step (envOf t.dmem (bS s)) (stOf t.dmem (bS s)) t.regs.rsi.toNat = r at hres hnx
  rcases r with err | ⟨st', t' | _⟩
  · rcases err with ⟨pos, ex⟩ | _
    · rw [show u.regs.rax.toBitVec = -1#64 from hres.1] at hms; exact absurd hms (by decide)
    · rw [show u.regs.rax.toBitVec = -2#64 from hres] at hms; exact absurd hms (by decide)
  · obtain ⟨h1, h2, -⟩ := hnx rfl
    rw [h2, ← hloop, loop_next hlt' hstp, loop_ge (by rw [hn, ← h1]; exact hge), hn]
  · exact absurd hres.1 hne

theorem sfT (v : Word) (r) : CondCode.s.interp (StatusFlags.from_result (v &&& v) r) = v.msb := by
  simp [CondCode.interp, StatusFlags.from_result]

-- A word in the frame is mapped.
theorem fm_some {m : Mem 64} (h : Fm s ra m) {a : Addr}
    (ha : (a - (s.regs.rsp.toBitVec - 5008#64)).toNat + 8 ≤ 5008) : (m.loadInt a 8).isSome :=
  h.map.loadInt_isSome (Or.inl ha)

/-! ## The blocks after the loop -/

-- A callee keeps `Rg`.
theorem Rg.call {F : Nat} (h : Rg s c) (hag : (mod F c).Agree c u) : Rg s u := by
  have hreg : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] →
      u.regs.get64 q = c.regs.get64 q := fun q hq => hag.1 q hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hreg .rsp (by simp); simp only [Reg64s.get64_rsp] at this; rw [this]; exact h.rsp
  · have := hreg .rbx (by simp); simp only [Reg64s.get64_rbx] at this; rw [this]; exact h.rbx
  · have := hreg .r12 (by simp); simp only [Reg64s.get64_r12] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r12
  · have := hreg .r13 (by simp); simp only [Reg64s.get64_r13] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r13
  · have := hreg .r14 (by simp); simp only [Reg64s.get64_r14] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r14
  · have := hreg .r15 (by simp); simp only [Reg64s.get64_r15] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r15

theorem len_rd {m : Mem 64} : (stOf m (bS s)).len = (rd m (bS s)).toNat := by
  rw [len_stOf]; simp [wordAt]

-- `cmp rbx, (rsp)`: `len = n`.
theorem len_eq_iff {m : Mem 64} (h : Rg s t) :
    (stOf m (bS s)).len = nArg s ↔ rd m t.regs.rsp.toBitVec = t.regs.rbx.toBitVec := by
  rw [len_rd, h.rsp, h.rbx]
  exact ⟨BitVec.eq_of_toNat_eq, congrArg BitVec.toNat⟩

-- The ops in the struct are the ops in the buffer.
theorem ops_topOp {m : Mem 64} (h : Hd s m) (hu : u.dmem = m) :
    (List.range (stOf m (bS s)).ops.length).map (topOp s u) = (stOf m (bS s)).ops := by
  rw [nops_stOf]
  show (List.range (rd m (wordAt (bS s) 2)).toNat).map (topOp s u)
    = (List.range (rd m (wordAt (bS s) 2)).toNat).map (opOf m (bS s))
  refine List.map_congr_left fun i _ => ?_
  simp only [topOp, opOf, opsOf, h.ops, hu]

theorem Out.congr (h : Out s t) (hm : u.dmem = t.dmem) (hax : u.regs.rax = t.regs.rax) :
    Out s u := by
  have ho : topOp s u = topOp s t := by funext i; simp only [topOp, hm]
  have hr : rax u = rax t := by simp only [rax, Reg64s.get64_rax, hax]
  unfold Out at *
  rw [ho, hr, hm]
  exact h

theorem at111_err (h : At111 s ra t) (hne : rd t.dmem t.regs.rsp.toBitVec ≠ t.regs.rbx.toBitVec)
    (hr : u'.regs = t.regs) (hm : u'.dmem = t.dmem) : AtErr s ra u' := by
  obtain ⟨hfm, hrg, hif⟩ := h
  refine ⟨by rw [hm]; exact hfm, hrg.of_regs hr, ?_⟩
  rw [← hif, ite_eq_right fun he => hne ((len_eq_iff hrg).mp he)]

theorem at111_ok (h : At111 s ra t) (heq : rd t.dmem t.regs.rsp.toBitVec = t.regs.rbx.toBitVec)
    (hr : u'.regs = t.regs) (hm : u'.dmem = t.dmem) : At116 s ra u' := by
  obtain ⟨hfm, hrg, hif⟩ := h
  refine ⟨by rw [hm]; exact hfm, hrg.of_regs hr, ?_⟩
  rw [← hif, ite_eq_left ((len_eq_iff hrg).mpr heq), hm]

theorem at116_next (h : At116 s ra t) (hm : u'.dmem = t.dmem)
    (hax : u'.regs.rax.toBitVec = rd t.dmem (t.regs.rsp.toBitVec + 16#64)) (hrg : Rg s u') :
    At108 s ra u' := by
  obtain ⟨hfm, hrg0, hres⟩ := h
  refine ⟨by rw [hm]; exact hfm, hrg, ?_⟩
  unfold Out
  rw [hres]
  refine ⟨?_, ops_topOp hfm.hd hm⟩
  rw [nops_stOf]
  show u'.regs.rax.toBitVec = _
  rw [hax, hrg0.rsp]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]

theorem at122_err (h : At122 s ra t) (hne : rd t.dmem t.regs.rsp.toBitVec ≠ t.regs.rbx.toBitVec)
    (hr : u'.regs = t.regs) (hm : u'.dmem = t.dmem) : AtErr s ra u' := by
  obtain ⟨hfm, hrg, hif, -, -⟩ := h
  refine ⟨by rw [hm]; exact hfm, hrg.of_regs hr, ?_⟩
  rw [← hif, ite_eq_right fun he => hne ((len_eq_iff hrg).mp he)]

theorem at122_pre (hp : TopPre s) (h : At122 s ra t) (hc : c.dmem = t.dmem)
    (hrsp : c.regs.rsp.toBitVec = bS s) (hdi : c.regs.rdi.toBitVec = bS s) :
    Pre finishF finishA c := by
  obtain ⟨hfm, -, -, hperm, hle⟩ := h
  have hdi' : rdi c = bS s := hdi
  refine Fm.pre hp hfm (Nat.le_refl _) hc hrsp hdi' ?_
  unfold finishA st cap
  rw [hc, hdi', hfm.hd.nOf_eq]
  exact ⟨hperm, hle⟩

theorem at122_fin (hpost : Post finishF finishR c u) (hag : (mod finishF c).Agree c u)
    (hp : TopPre s) (h : At122 s ra t)
    (heq : rd t.dmem t.regs.rsp.toBitVec = t.regs.rbx.toBitVec) (hc : c.dmem = t.dmem)
    (hrg : Rg s c) (hdi : c.regs.rdi.toBitVec = bS s) : At108 s ra u := by
  have hpre := at122_pre hp h hc hrg.rsp hdi
  obtain ⟨hfm, hrg0, hif, -, -⟩ := h
  have hdi' : rdi c = bS s := hdi
  have hfm' := Fm.call hp hfm (Nat.le_refl _) hc hrg.rsp hdi' hpre hpost hag
  refine ⟨hfm', hrg.call hag, ?_⟩
  have hres := hpost.2.2
  simp only [finishR, st, st'] at hres
  rw [hdi', hc] at hres
  unfold Out
  rw [← hif, ite_eq_left ((len_eq_iff hrg0).mpr heq)]
  generalize finish (stOf t.dmem (bS s)) = r at hres ⊢
  rcases r with (⟨pos, ex⟩ | _) | ops
  · obtain ⟨h1, h2, h3⟩ := hres
    rw [show blkOf u.dmem (bS s) = blkArg s from hfm'.hd.blk] at h2 h3
    exact ⟨h1, h2, h3⟩
  · exact hres
  · obtain ⟨h1, h2⟩ := hres
    refine ⟨h1, ?_⟩
    rw [← h2]; exact ops_topOp hfm'.hd rfl

theorem atErr_next (h : AtErr s ra t) (hm : u'.dmem = t.dmem) (hax : u'.regs.rax.toBitVec = -2#64)
    (hrg : Rg s u') : At108 s ra u' := by
  obtain ⟨hfm, -, hres⟩ := h
  refine ⟨by rw [hm]; exact hfm, hrg, ?_⟩
  unfold Out
  rw [hres]
  exact hax

theorem at109_nArg (h : At109 s ra t) : nArg s = t.regs.rsi.toNat := by
  rw [show t.regs.rsi.toNat = t.regs.rsi.toBitVec.toNat from rfl, h.2.2.2.1]

theorem at109_115 (h : At109 s ra t) (hnz : t.regs.rsi.toBitVec ≠ 0#64) (hr : u'.regs = t.regs)
    (hm : u'.dmem = t.dmem) : At115 s ra u' := by
  have hn := at109_nArg h
  obtain ⟨hfm, hrg, -, -, hst⟩ := h
  refine ⟨by rw [hm]; exact hfm, hrg.of_regs hr, ?_, by rw [hm]; exact hst⟩
  rw [hn]
  show 0 < t.regs.rsi.toBitVec.toNat
  have : t.regs.rsi.toBitVec.toNat ≠ 0 := fun h0 => hnz (BitVec.eq_of_toNat_eq h0)
  omega

theorem at109_116 (hp : TopPre s) (h : At109 s ra t) (hz : t.regs.rsi.toBitVec = 0#64)
    (hr : u'.regs = t.regs) (hm : u'.dmem = t.dmem) : At116 s ra u' := by
  have hn := at109_nArg h
  rw [show t.regs.rsi.toNat = 0 by show t.regs.rsi.toBitVec.toNat = 0; rw [hz]; rfl] at hn
  obtain ⟨hfm, hrg, hm0, -, hst⟩ := h
  refine ⟨by rw [hm]; exact hfm, hrg.of_regs hr, ?_⟩
  rw [hm]
  obtain ⟨h1, -⟩ := hfm.init_loop hp hst
  rw [← h1, loop_ge (by rw [hfm.env_n, hn]; omega), ite_eq_left]
  rw [hst, hfm.env_n, hn]
  simp [st0, St.len, topSource, topDests, hm0]

theorem fm_retAddr (hp : TopPre s) (h : Fm s ra t.dmem)
    (hsp : t.regs.rsp.toBitVec = rsp s - 8#64) : t.retAddr = some ra := by
  have hge := hp.rsp_ge
  simp only [rsp, Reg64s.get64_rsp] at hge
  have hs : (t.dmem.loadInt (rsp s - 8#64) 8).isSome = true :=
    fm_some h (by simp only [rsp, Reg64s.get64_rsp]; bv_omega)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  have hra := h.ra
  rw [rd, hv, Option.get!_some] at hra
  rw [MachineData.retAddr, show t.regs.get64 .rsp = rsp s - 8#64 from hsp, hv, Option.map_some, hra,
    Int64.ofBitVec_toBitVec]

theorem fm_retAddr_isSome (hp : TopPre s) (h : Fm s ra t.dmem)
    (hsp : t.regs.rsp.toBitVec = rsp s - 8#64) : t.retAddr.isSome = true := by
  rw [fm_retAddr hp h hsp]; rfl

-- `.LB108`: the pops and `ret` give the postcondition.
theorem at108_ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    {t' : MachineData} (hp : TopPre s) (h : At108 s ra t) (hm' : t'.dmem = t.dmem)
    (hsp' : t'.regs.rsp.toBitVec = 4168#64 + t.regs.rsp.toBitVec + 8#64 + 8#64)
    (hu : u.dmem = t.dmem)
    (husp : u.regs.rsp.toBitVec = 4168#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64)
    (hax : u.regs.rax = t.regs.rax)
    (hbx : u.regs.rbx.toBitVec = rd t.dmem (4168#64 + t.regs.rsp.toBitVec))
    (hbp : u.regs.rbp.toBitVec = rd t.dmem (4168#64 + t.regs.rsp.toBitVec + 8#64))
    (h12 : u.regs.r12 = t.regs.r12) (h13 : u.regs.r13 = t.regs.r13)
    (h14 : u.regs.r14 = t.regs.r14) (h15 : u.regs.r15 = t.regs.r15) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ TopPost s t ∧ (topMod s).Agree s t) t'.retAddr.get! u := by
  obtain ⟨hfm, hrg, hout⟩ := h
  have hge := hp.rsp_ge
  have hr := hrg.rsp
  simp only [bS, rsp, Reg64s.get64_rsp] at hge hr
  have hra : t'.retAddr = some ra :=
    fm_retAddr hp (by rw [hm']; exact hfm) (by rw [hsp']; simp only [rsp, Reg64s.get64_rsp]; bv_omega)
  have hsp : u.regs.rsp.toBitVec = s.regs.rsp.toBitVec := by rw [husp]; bv_omega
  have hb : u.regs.rbx.toBitVec = s.regs.rbx.toBitVec := by
    rw [hbx, show 4168#64 + t.regs.rsp.toBitVec = rsp s - 24#64 by
      simp only [rsp, Reg64s.get64_rsp]; bv_omega]
    exact hfm.rbx
  have hb' : u.regs.rbp.toBitVec = s.regs.rbp.toBitVec := by
    rw [hbp, show 4168#64 + t.regs.rsp.toBitVec + 8#64 = rsp s - 16#64 by
      simp only [rsp, Reg64s.get64_rsp]; bv_omega]
    exact hfm.rbp
  refine Or.inr ⟨⟨by simp [hra], ⟨?_, (hout.congr hu hax : Out s u)⟩, fun q hq => ?_, ?_⟩,
    fun _ _ _ => ?_⟩
  · rw [hu]; exact fun x hx => hfm.map x (hx.elim Or.inl False.elim)
  · cases q <;> first | (exfalso; apply hq; simp [topMod]; done) | skip
    all_goals simp only [Reg64s.get64_rbx, Reg64s.get64_rsp, Reg64s.get64_rbp, Reg64s.get64_r12,
      Reg64s.get64_r13, Reg64s.get64_r14, Reg64s.get64_r15]
    · exact hb
    · exact hsp
    · exact hb'
    · rw [h12, hrg.r12]
    · rw [h13, hrg.r13]
    · rw [h14, hrg.r14]
    · rw [h15, hrg.r15]
  · rw [hu]; exact hfm.hd.un
  · apply MachineData.stackBelow_of_add_eight
    simp only [MachineData.pushRa, Reg64s.get64_set64, reduceIte]
    rw [show u.regs.get64 .rsp = rsp s from hsp]
    exact BitVec.sub_add_cancel _ _
end

end TopProof
end Bbu

set_option experimental.vcgen true

local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))


set_option hygiene false in
-- A load of the entry block succeeds.
local macro "ent_some" : tactic => `(tactic| (
  repeat (apply loadInt_isSome_store)
  apply ent_isSome hp
  first | (left; bv_omega) | (right; bv_omega)))

set_option hygiene false in
-- The stack goal of a jump: `rsp` is below the entry `rsp`.
local macro "cfg_stk" : tactic => `(tactic| (
  apply MachineData.stackAtOrBelow_of_toNat_lt
  simp only [Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp]
  bv_omega))
namespace Bbu
open TopProof

set_option maxHeartbeats 4000000 in
theorem buildBottomUp_body [Host] [FunDecls]
    (hstep : Spec "step" stepF stepA stepR) (hfin : Spec "finish" finishF finishA finishR) :
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ TopPre s ⦄ buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ TopPost s t ∧ (topMod s).Agree s t ⦄ := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hp⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t | .label "build_bottom_up", t => t = s.pushRa ra
      | .label ".LB110", t => At110 s ra t
      | .label ".LB115", t => At115 s ra t
      | .label ".LB114", t => At114 s ra t
      | .label ".LB111", t => At111 s ra t
      | .label ".LB116", t => At116 s ra t
      | .label ".LB108", t => At108 s ra t
      | .label ".LB122", t => At122 s ra t
      | .label ".LB117", t | .label ".LB118", t => AtErr s ra t
      | .label ".LB109", t => At109 s ra t
      | _, _ => False)
    (V s) ?_ rfl
  cfg_cases
  case left t ht => subst ht; kvcgen64
  case right.left t ht =>
    subst ht
    have hge := hp.rsp_ge
    simp only [rsp, Reg64s.get64_rsp] at hge
    clear hstep hfin
    kvcgen64
    all_goals bbu_norm at *
    case vc13 _ hz _ =>
      bbu_flags at hz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp]
        bv_omega
      · refine at109_entry hp ?_ ⟨?_, rfl, rfl, rfl, rfl, rfl⟩ ?_ rfl
        · exact ent_fm hp
        · simp only [bS, rsp, Reg64s.get64_rsp]; bv_omega
        · simp only [mArg, rdi, Reg64s.get64_rdi, BitVec.and_self] at hz ⊢; bv_omega
      · left; show 2 ^ 20 + 1 < 2 ^ 21; omega
    case vc14 _ hz _ =>
      bbu_flags at hz
      refine at110_entry ?_ ⟨?_, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl ?_ ?_
      · exact ent_fm hp
      · simp only [bS, rsp, Reg64s.get64_rsp]; bv_omega
      · simp only [mArg, rdi, Reg64s.get64_rdi, BitVec.and_self] at hz ⊢; bv_omega
      · exact ent_un hp
    case vc15 =>
      left; have := hp.m_le; have := hp.n_le
      show 2 ^ 20 + 2 + (mArg s - _) < 2 ^ 21
      simp only [mArg, nArg] at *; omega
    all_goals ent_some
  case right.right.left t ht =>
    have h110 := ht
    obtain ⟨hfm, hrg, hdi, hsi, h8, hax, h012, hcp, -⟩ := ht
    have hax' : t.regs.rax.toBitVec.toNat < mArg s := hax
    have hge := hp.rsp_ge
    have hml := hp.m_le
    have hr := hrg.rsp
    have hrb := hrg.rbx
    top_nrm at hax' hge hml hr hrb hdi
    clear hstep hfin
    kvcgen64
    all_goals bbu_norm at *
    case vc1 => exact at110_some hp h110 (Or.inl rfl)
    case vc2 => exact at110_some hp h110 (Or.inr (Or.inr (Or.inl rfl)))
    case vc3 =>
      apply loadInt_isSome_store; exact at110_some hp h110 (Or.inr (Or.inl rfl))
    case vc4 =>
      apply loadInt_isSome_store; exact at110_some hp h110 (Or.inr (Or.inr (Or.inr rfl)))
    case vc5 _ hz _ =>
      bbu_flags at hz
      have h1 : (1#64 + t.regs.rax.toBitVec).toNat = t.regs.rax.toBitVec.toNat + 1 := by bv_omega
      cfg_goto
      · cfg_stk
      · refine at110_next hp h110 rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6⟩ hdi hsi h8 h1 ?_
        show (1#64 + t.regs.rax.toBitVec).toNat < _
        top_nrm; bv_omega
      · left
        show 2 ^ 20 + 2 + (mArg s - (1#64 + t.regs.rax.toBitVec).toNat)
          < 2 ^ 20 + 2 + (mArg s - t.regs.rax.toBitVec.toNat)
        simp only [mArg, rdi, Reg64s.get64_rdi]; omega
    case vc6 _ _ hz _ =>
      bbu_flags at hz
      simp only [BitVec.and_self] at hz
      exfalso; bv_omega
    case vc7 hz' _ hz _ =>
      bbu_flags at hz hz'
      simp only [BitVec.and_self] at hz
      exact at115_next hp h110 rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6⟩
        (by show t.regs.rax.toBitVec.toNat + 1 = _; top_nrm; bv_omega) (by top_nrm; bv_omega)
    case vc8 => left; show 2 ^ 20 < 2 ^ 20 + 2 + _; omega
  case right.right.right.left t ht =>
    have hge := hp.rsp_ge
    have hrg := ht.2.1
    have hr := hrg.rsp
    top_nrm at hge hr
    clear hstep hfin
    kvcgen64
    all_goals bbu_norm at *
    case vc1 => exact And.left (at114_init hp ht rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6⟩ hr rfl)
    case vc2 =>
      left
      exact (at114_init (t' := { t with regs := { t.regs with rsi := ⟨0#64⟩, rbp := ⟨t.regs.rsp.toBitVec⟩ } }) hp ht rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6⟩ hr rfl).2
  case right.right.right.right.left t ht =>
    have h114 := ht
    obtain ⟨hfm, hrg, hbp, hsi, hinv, hloop⟩ := ht
    have hge := hp.rsp_ge
    have hr := hrg.rsp
    have hbp' := hbp
    top_nrm at hge hr hbp'
    clear hfin
    kvcgen64 [hstep]
    all_goals bbu_norm at *
    case vc1 => exact fm_some hfm (by bv_omega)
    case vc2 => exact at114_pre hp h114 rfl hrg.rsp hbp rfl
    case vc3 u hpost hag hz _ =>
      have ha := aft_mk hpost hag hp h114 rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6⟩ rfl hbp rfl
      have hur := ha.rg.rsp
      top_nrm at hur
      bbu_flags at hz
      cfg_goto
      · cfg_stk
      · exact aft_finish ha (by bv_omega) rfl rfl
      · left; show 1 < (nArg s - t.regs.rsi.toNat) * 512 + (stOf t.dmem (bS s)).pending + 2; omega
    case vc4 u hpost hag hz _ hs _ =>
      have ha := aft_mk hpost hag hp h114 rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6⟩ rfl hbp rfl
      have hur := ha.rg.rsp
      top_nrm at hur
      bbu_flags at hz
      rw [sfT] at hs
      cfg_goto
      · cfg_stk
      · exact aft_err ha (by bv_omega) hs rfl rfl
      · left; show 0 < (nArg s - t.regs.rsi.toNat) * 512 + (stOf t.dmem (bS s)).pending + 2; omega
    case vc5 u hpost hag hz _ hs hc _ =>
      have ha := aft_mk hpost hag hp h114 rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6⟩ rfl hbp rfl
      have hur := ha.rg.rsp
      have hub := ha.rg.rbx
      top_nrm at hur hub
      bbu_flags at hc
      have hlt : u.regs.rax.toNat < nArg s := by
        have := (borrow_iff _ _).mp hc; rw [hub] at this; exact this
      have hrg' := ha.rg
      cfg_goto
      · cfg_stk
      · exact And.left (aft_next ha hlt ⟨hrg'.1, hrg'.2, hrg'.3, hrg'.4, hrg'.5, hrg'.6⟩ rfl rfl rfl)
      · left; exact aft_next_V ha hlt ⟨hrg'.1, hrg'.2, hrg'.3, hrg'.4, hrg'.5, hrg'.6⟩ rfl rfl rfl
    case vc6 u hpost hag hz _ hs hc _ =>
      have ha := aft_mk hpost hag hp h114 rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6⟩ rfl hbp rfl
      have hub := ha.rg.rbx
      top_nrm at hub
      bbu_flags at hz hc
      rw [sfT] at hs
      have hge : ¬ u.regs.rax.toNat < nArg s := by
        have := (no_borrow_iff _ _).mp hc; rw [hub] at this; show ¬ u.regs.rax.toBitVec.toNat < s.regs.rsi.toBitVec.toNat; omega
      have hrg' := ha.rg
      exact aft_done ha (by bv_omega) hs hge ⟨hrg'.1, hrg'.2, hrg'.3, hrg'.4, hrg'.5, hrg'.6⟩ rfl
    case vc7 => left; show 1 < (nArg s - t.regs.rsi.toNat) * 512 + (stOf t.dmem (bS s)).pending + 2; omega
  case right.right.right.right.right.left t ht =>
    have hrg := ht.2.1
    have hfm := ht.1
    have hge := hp.rsp_ge
    have hr := hrg.rsp
    top_nrm at hge hr
    clear hstep hfin
    kvcgen64
    all_goals bbu_norm at *
    case vc1 => exact hfm.wf.isSome_struct (by simp only [WORDS, bS, rsp, Reg64s.get64_rsp]; bv_omega)
    case vc2 _ hz =>
      bbu_flags at hz
      cfg_goto
      · cfg_stk
      · exact at111_err ht (by bv_omega) rfl rfl
      · right; exact ⟨rfl, by decide⟩
    case vc3 _ hz =>
      bbu_flags at hz
      exact at111_ok ht (by bv_omega) rfl rfl
    case vc4 => right; exact ⟨rfl, by decide⟩
  case right.right.right.right.right.right.left t ht =>
    have hrg := ht.2.1
    have hfm := ht.1
    have hge := hp.rsp_ge
    have hr := hrg.rsp
    top_nrm at hge hr
    clear hstep hfin
    kvcgen64
    all_goals bbu_norm at *
    case vc1 => exact hfm.wf.isSome_struct (by simp only [WORDS, bS, rsp, Reg64s.get64_rsp]; bv_omega)
    case vc2 => exact at116_next ht rfl rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6⟩
    case vc3 => left; show 0 < 1; decide
  case right.right.right.right.right.right.right.left t ht =>
    have hrg := ht.2.1
    have hfm := ht.1
    have hge := hp.rsp_ge
    have hr := hrg.rsp
    top_nrm at hge hr
    clear hstep hfin
    kvcgen64
    all_goals bbu_norm at *
    case vc1 => exact fm_some hfm (by bv_omega)
    case vc2 => exact fm_some hfm (by bv_omega)
    case vc3 => exact fm_retAddr_isSome hp hfm (by simp only [rsp, Reg64s.get64_rsp]; bv_omega)
    case vc4 => exact at108_ret hp ht rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  case right.right.right.right.right.right.right.right.left t ht =>
    have hrg := ht.2.1
    have hfm := ht.1
    have hge := hp.rsp_ge
    have hr := hrg.rsp
    top_nrm at hge hr
    clear hstep
    kvcgen64 [hfin]
    all_goals bbu_norm at *
    case vc1 => exact hfm.wf.isSome_struct (by simp only [WORDS, bS, rsp, Reg64s.get64_rsp]; bv_omega)
    case vc2 _ hz =>
      bbu_flags at hz
      cfg_goto
      · cfg_stk
      · exact at122_err ht (by bv_omega) rfl rfl
      · right; exact ⟨rfl, by decide⟩
    case vc3 => exact fm_some hfm (by bv_omega)
    case vc4 => exact at122_pre hp ht rfl hrg.rsp hrg.rsp
    case vc5 u _ hz hpost hag =>
      bbu_flags at hz
      have h108 := at122_fin hpost hag hp ht (by bv_omega) rfl
        ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6⟩ hrg.rsp
      have hur := h108.2.1.rsp
      top_nrm at hur
      cfg_goto
      · cfg_stk
      · exact h108
      · left; show 0 < 1; decide
  case right.right.right.right.right.right.right.right.right.left t ht =>
    have hge := hp.rsp_ge
    have hr := ht.2.1.rsp
    top_nrm at hge hr
    clear hstep hfin
    kvcgen64
    all_goals bbu_norm at *
    cfg_goto
    · cfg_stk
    · exact atErr_next ht rfl rfl ⟨ht.2.1.1, ht.2.1.2, ht.2.1.3, ht.2.1.4, ht.2.1.5, ht.2.1.6⟩
    · left; show 0 < 1; decide
  case right.right.right.right.right.right.right.right.right.right.left t ht =>
    have hge := hp.rsp_ge
    have hr := ht.2.1.rsp
    top_nrm at hge hr
    clear hstep hfin
    kvcgen64
    all_goals bbu_norm at *
    cfg_goto
    · cfg_stk
    · exact atErr_next ht rfl rfl ⟨ht.2.1.1, ht.2.1.2, ht.2.1.3, ht.2.1.4, ht.2.1.5, ht.2.1.6⟩
    · left; show 0 < 1; decide
  case right.right.right.right.right.right.right.right.right.right.right t ht =>
    have hge := hp.rsp_ge
    have hr := ht.2.1.rsp
    top_nrm at hge hr
    clear hstep hfin
    kvcgen64
    all_goals bbu_norm at *
    case vc1 _ hz _ =>
      simp only [BitVec.and_self] at hz
      bbu_flags at hz
      cfg_goto
      · cfg_stk
      · exact at109_115 ht hz rfl rfl
      · left; show 2 ^ 20 < 2 ^ 20 + 1; omega
    case vc2 _ hz _ =>
      simp only [BitVec.and_self] at hz
      bbu_flags at hz
      cfg_goto
      · cfg_stk
      · exact at109_116 hp ht hz rfl rfl
      · left; show 1 < 2 ^ 20 + 1; omega

end Bbu
