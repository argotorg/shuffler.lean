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
  spills := fun i => UInt8.ofBitVec (rdb s.dmem (splArg s + BitVec.ofNat 64 i))

def topSource : List Word := (List.range (mArg s)).map fun i => rd s.dmem (wordAt (srcArg s) i)

def topDests : List Nat :=
  (List.range (mArg s)).map fun i => (rd s.dmem (wordAt (dstArg s) i)).toNat

-- The spilled bytes of the variables in the target.
def topSpl : List (Addr × Nat) :=
  (List.range (nArg s)).filterMap fun d =>
    let v := (rd s.dmem (wordAt (tgtArg s) d)).toNat
    if 2 ≤ v ∧ v % 2 = 0 then some (splArg s + BitVec.ofNat 64 ((v - 2) / 2), 1) else none

-- The locals of `build_bottom_up` after `subq`: the struct and 8 bytes of padding.
def topLocals : Nat := 8 * WORDS + 8
-- The frame: the return address, the locals and the frame of `buildBottomUp`.
def topF : Nat := 8 + topLocals + loopF
theorem topF_eq : topF = 20688 := rfl

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
  n_le : nArg s ≤ MAX_N
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

-- The struct: at the bottom of the locals (`8 + topLocals` bytes below `rsp`).
abbrev bS : Addr := rsp s - 16464#64

def topRes : M (List Op) := buildBottomUp (topEnv s) (topSource s) (topDests s)

def st0 : St := ⟨List.zipWith Slot.mk (topSource s) (topDests s), nArg s - mArg s, []⟩
end

section
variable {s : MachineData}

theorem _root_.Bbu.TopPre.rsp_ge (hp : TopPre s) : 20688 ≤ (rsp s).toNat := by
  have := hp.rsp_le; simp only [topF_eq] at this; omega

-- `n_le` with the value of `MAX_N`, for `omega`.
theorem _root_.Bbu.TopPre.n_le' (hp : TopPre s) : nArg s ≤ 1024 := hp.n_le

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

-- The struct lies in the frame.
theorem struct_in_frame (hp : TopPre s) :
    ∀ x, Mem.Blocks.Inside x 1 [(bS s, 8 * WORDS)] → Mem.Blocks.Inside x 1 [frame topF s] := by
  intro x hx
  have := hp.rsp_ge
  simp only [Mem.Blocks.Inside, or_false, WORDS_eq, topF_eq, bS, rsp] at *
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
    have := hp.tgt_lt; have := hp.n_le'
    simp only [Mem.Blocks.Inside, or_false, wordAt] at hy ⊢; bv_omega)

theorem Hd.nOf_eq (h : Hd s m) : nOf m (bS s) = nArg s := by unfold nOf; rw [h.n]

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
  · left; simp only [Mem.Blocks.Inside, or_false, WORDS_eq, bS, rsp] at *; bv_omega
  · left; simp only [Mem.Blocks.Inside, or_false, WORDS_eq, STACK, MAX_N, bS, rsp] at *; bv_omega
  · exact .inr (Or.inl hx)
  · exact .inr (Or.inr (Or.inl hx))
  · exact hx.elim

theorem Hd.r_sub (hp : TopPre s) (h : Hd s m) {x : Addr}
    (hx : Mem.Blocks.Inside x 1 (readable m (bS s))) :
    Mem.Blocks.Inside x 1 [(bS s, 8 * WORDS)] ∨ Mem.Blocks.Inside x 1 (topRd s) := by
  have := hp.rsp_ge
  simp only [readable, nOf, tgtOf, h.n, h.tgt, h.spl_eq hp] at hx
  rcases hx with hx | hx | hx
  · left; simp only [Mem.Blocks.Inside, or_false, WORDS_eq, bS, rsp] at *; bv_omega
  · exact .inr (Or.inl hx)
  · exact .inr hx.tail

theorem Hd.map_all (hp : TopPre s) (h : Hd s m) (hmap : Mem.Mapped (frame topF s :: topOut s) m) :
    Mem.Mapped (frame topF s :: topOut s ++ topIn s) m :=
  Mapped.of_unchanged hp.mapped h.un hmap

theorem Hd.wf (hp : TopPre s) (h : Hd s m) (hmap : Mem.Mapped (frame topF s :: topOut s) m)
    (hlen : (rd m (wordAt (bS s) 0)).toNat ≤ MAX_N) (hnops : (rd m (wordAt (bS s) 2)).toNat ≤ 6 * nArg s) :
    Wf m (bS s) := by
  have hge := hp.rsp_ge
  have hst := struct_in_frame hp
  have hsp := h.spl_eq hp
  simp only [splBlocks] at hsp
  refine ⟨fun x hx => h.map_all hp hmap x ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlen, ?_, ?_⟩
  · rcases inside_append.mp hx with hx | hx
    · rcases h.w_sub hp hx with hx | hx
      · exact inside_of_mem List.mem_cons_self (hst x hx)
      · exact (inside_append.mpr (.inl hx)).tail
    · rcases h.r_sub hp hx with hx | hx
      · exact inside_of_mem List.mem_cons_self (hst x hx)
      · exact (inside_append.mpr (.inr (topRd_in hx))).tail
  · simp only [WORDS_eq, bS, rsp] at *; bv_omega
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

/-! ## The memory at the call -/

section
variable (s : MachineData) (ra : Int64)

-- The memory `m` at the call of `buildBottomUp`: the return address, the struct
-- and the frame.
structure Fm (m : Mem 64) : Prop where
  hd : Hd s m
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  map : Mem.Mapped (frame topF s :: topOut s) m
  wf : Wf m (bS s)
end

section
variable {s : MachineData} {ra : Int64} {m m' : Mem 64} {i : Nat}

-- The precondition of `buildBottomUp` with the struct at `rsp`.
theorem Fm.pre {A : MachineData → Prop} {c : MachineData} (hp : TopPre s)
    (h : Fm s ra m) (hc : c.dmem = m) (hrsp : rsp c = bS s)
    (hrdi : rdi c = bS s) (hA : A c) : Pre loopF A c := by
  have hge := hp.rsp_ge
  refine ⟨by rw [hc, hrdi]; exact h.wf, ⟨?_, fun x hx => ?_, ?_⟩, hA⟩
  · rw [hrsp]; simp only [loopF_eq, bS, rsp] at *; bv_omega
  · rw [hc]
    refine h.map x (inside_of_mem List.mem_cons_self ?_)
    simp only [Mem.Blocks.Inside, or_false, hrsp, topF_eq, loopF_eq, bS, rsp] at *; bv_omega
  · rw [hc, hrdi]
    intro x hx hwr
    have hx' : Mem.Blocks.Inside x 1 [frame topF s] := by
      simp only [Mem.Blocks.Inside, or_false, hrsp, topF_eq, loopF_eq, bS, rsp] at *; bv_omega
    rcases inside_append.mp hwr with hw | hr
    · rcases h.hd.w_sub hp hw with hw | hw
      · simp only [Mem.Blocks.Inside, or_false, hrsp, WORDS_eq, loopF_eq, bS, rsp] at *; bv_omega
      · exact topOut_frame hp x hw hx'
    · rcases h.hd.r_sub hp hr with hr | hr
      · simp only [Mem.Blocks.Inside, or_false, hrsp, WORDS_eq, loopF_eq, bS, rsp] at *; bv_omega
      · exact topRd_out hp x hr (inside_of_mem List.mem_cons_self hx')

-- `buildBottomUp` with the struct at `rsp` keeps `Fm`.
theorem Fm.call {A : MachineData → Prop} {R : MachineData → MachineData → Prop}
    {c t : MachineData} (hp : TopPre s) (h : Fm s ra m) (hc : c.dmem = m)
    (hrsp : rsp c = bS s) (hrdi : rdi c = bS s) (hpre : Pre loopF A c) (hpost : Post loopF R c t)
    (hag : (mod loopF c).Agree c t) : Fm s ra t.dmem := by
  have hge := hp.rsp_ge
  have hu : Mem.UnchangedOutside (frame loopF c :: writable m (bS s)) m t.dmem := by
    have := hag.2; simp only [mod, hc, hrdi] at this; exact this
  have hdr : ∀ {k}, 3 ≤ k → k < 8 → rd t.dmem (wordAt (bS s) k) = rd m (wordAt (bS s) k) :=
    fun hk3 hk => by have := hdr_congr hag.2 hpre.disj hk3 hk; rwa [hrdi, hc] at this
  have hwr : writable t.dmem (bS s) = writable m (bS s) := by
    have := (Post.env hpre hag).2.2; rwa [hrdi, hc] at this
  -- The callee frame lies in the frame.
  have hcf : ∀ x, Mem.Blocks.Inside x 1 [frame loopF c] → Mem.Blocks.Inside x 1 [frame topF s] := by
    intro x hx; simp only [Mem.Blocks.Inside, or_false, hrsp, topF_eq, loopF_eq, bS, rsp] at *; bv_omega
  -- The return address lies in neither the callee frame nor `writable`.
  have hra : rd t.dmem (rsp s - 8#64) = rd m (rsp s - 8#64) :=
    rd_congr hu fun x hx hl => by
      have hxf : Mem.Blocks.Inside x 1 [frame topF s] := by
        simp only [Mem.Blocks.Inside, or_false, topF_eq, rsp] at *; bv_omega
      rcases hl with hl | hl
      · simp only [Mem.Blocks.Inside, or_false, hrsp, loopF_eq, bS, rsp] at *; bv_omega
      · rcases h.hd.w_sub hp hl with hl | hl
        · simp only [Mem.Blocks.Inside, or_false, WORDS_eq, bS, rsp] at *; bv_omega
        · exact topOut_frame hp x hl hxf
  have hun : ∀ x, ¬ Mem.Blocks.Inside x 1 (frame topF s :: topOut s) → t.dmem.get? x = m.get? x :=
    fun x hx => hu x fun hl => by
      rcases hl with hl | hl
      · exact hx (inside_of_mem List.mem_cons_self (hcf x (Or.inl hl)))
      · rcases h.hd.w_sub hp hl with hl | hl
        · exact hx (inside_of_mem List.mem_cons_self (struct_in_frame hp x hl))
        · exact hx hl.tail
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hdr (by omega) (by omega)]; exact h.hd.n
  · rw [hdr (by omega) (by omega)]; exact h.hd.tgt
  · rw [hdr (by omega) (by omega)]; exact h.hd.spl
  · rw [hdr (by omega) (by omega)]; exact h.hd.ops
  · rw [hdr (by omega) (by omega)]; exact h.hd.blk
  · intro x hx; rw [hun x hx]; exact h.hd.un x hx
  · rw [hra]; exact h.ra
  · refine Mapped.of_unchanged h.map hu fun x hx => ?_
    rcases hx with hx | hx
    · exact hpost.2.1 x (Or.inl hx)
    · exact hpost.1.mapped x (inside_append.mpr (.inl (by rw [hrdi, hwr]; exact hx)))
  · rw [← hrdi]; exact hpost.1

/-! ## The model at the start -/

theorem Fm.env_n (h : Fm s ra m) : (envOf m (bS s)).n = nArg s :=
  n_envOf.trans h.hd.nOf_eq

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

end

/-! ## The memory before the call -/

section
variable (s : MachineData) (ra : Int64)

-- The first `i` stack and dest words are copies of the inputs.
def Copied (m : Mem 64) (i : Nat) : Prop :=
  ∀ j < i, rd m (wordAt (bS s) (STACK + j)) = rd s.dmem (wordAt (srcArg s) j)
    ∧ rd m (wordAt (bS s) (DEST + j)) = rd s.dmem (wordAt (dstArg s) j)

-- The memory `m` in the copy loop: only the frame changed, the return address
-- and the header words 0, 3, 4 and 5 are set, and `i` slots are copied.
structure Cp (m : Mem 64) (i : Nat) : Prop where
  un : Mem.UnchangedOutside [frame topF s] s.dmem m
  map : Mem.Mapped [frame topF s] m
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  w0 : rd m (wordAt (bS s) 0) = rdi s
  w3 : rd m (wordAt (bS s) 3) = rsi s
  w4 : rd m (wordAt (bS s) 4) = tgtArg s
  w5 : rd m (wordAt (bS s) 5) = splArg s
  cp : Copied s m i
end

section
variable {s : MachineData} {ra : Int64} {m m' : Mem 64} {i : Nat}

-- The words at `rsp` are outside the frame.
theorem Cp.arg (hp : TopPre s) (h : Cp s ra m i) {k : Nat} (hk : k ≤ 8) :
    rd m (rsp s + BitVec.ofNat 64 k) = rd s.dmem (rsp s + BitVec.ofNat 64 k) := by
  have hge := hp.rsp_ge
  refine rd_congr h.un fun y hy hf => ?_
  simp only [Mem.Blocks.Inside, or_false, topF_eq, rsp] at *; bv_omega

-- The `Fm` at the call and the start state in the struct.
theorem Cp.fm (hp : TopPre s) (h : Cp s ra m (mArg s))
    (hu : Mem.UnchangedOutside [frame topF s] m m') (hmap : Mem.Mapped [frame topF s] m')
    (hra : rd m' (rsp s - 8#64) = ra.toBitVec)
    (h0 : rd m' (wordAt (bS s) 0) = rdi s) (h1 : rd m' (wordAt (bS s) 1) = rsi s - rdi s)
    (h2 : rd m' (wordAt (bS s) 2) = 0#64) (h3 : rd m' (wordAt (bS s) 3) = rsi s)
    (h4 : rd m' (wordAt (bS s) 4) = tgtArg s) (h5 : rd m' (wordAt (bS s) 5) = splArg s)
    (h6 : rd m' (wordAt (bS s) 6) = opsArg s) (h7 : rd m' (wordAt (bS s) 7) = blkArg s)
    (hc : Copied s m' (mArg s)) :
    Fm s ra m' ∧ stOf m' (bS s) = st0 s := by
  have hu' : Mem.UnchangedOutside [frame topF s] s.dmem m' := fun x hx => by
    rw [hu x hx]; exact h.un x hx
  have hun : Mem.UnchangedOutside (frame topF s :: topOut s) s.dmem m' :=
    fun x hx => hu' x fun h => hx (inside_of_mem List.mem_cons_self h)
  have hd : Hd s m' := ⟨h3, h4, h5, h6, h7, hun⟩
  have hm : Mem.Mapped (frame topF s :: topOut s) m' :=
    Mapped.of_unchanged (fun x hx => hp.mapped x (by
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact (inside_append.mpr (.inl hx)).tail)) hu' hmap
  have hml := hp.m_le
  have hnl := hp.n_le'
  refine ⟨⟨hd, hra, hm, hd.wf hp hm ?_ ?_⟩, ?_⟩
  · rw [h0]; simp only [mArg, nArg, MAX_N] at *; omega
  · rw [h2]; simp
  · simp only [stOf, st0, h0, h1, h2]
    congr 1
    · apply List.ext_getElem (by simp [topSource, topDests, mArg, rdi])
      intro j h1 h2
      simp only [List.length_map, List.length_range] at h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, topSource, topDests,
        slotOf, (hc j h1).1, (hc j h1).2]
    · simp only [mArg, nArg] at hml ⊢; bv_omega

end

end TopProof
end Bbu

namespace Bbu
namespace TopProof

/-! ## The invariants -/

section
variable (s : MachineData) (ra : Int64)

-- The registers at the labels after the entry block.
structure Rg (t : MachineData) : Prop where
  rsp : t.regs.rsp.toBitVec = bS s
  rbx : t.regs.rbx = s.regs.rbx
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

-- `.LB114`: the copy loop at the index `i` in `rax`.
def At114 (t : MachineData) : Prop :=
  Cp s ra t.dmem t.regs.rax.toNat ∧ Rg s t ∧ t.regs.rdi.toBitVec = rdi s
    ∧ t.regs.rsi.toBitVec = rsi s ∧ t.regs.rdx.toBitVec = srcArg s
    ∧ t.regs.r8.toBitVec = dstArg s ∧ t.regs.rax.toNat < mArg s

-- `.LB113`: all the slots are copied.
def At113 (t : MachineData) : Prop :=
  Cp s ra t.dmem (mArg s) ∧ Rg s t ∧ t.regs.rdi.toBitVec = rdi s ∧ t.regs.rsi.toBitVec = rsi s

-- The variant.
def V : Label → MachineData → Nat
  | "build_bottom_up", _ => 2 ^ 12
  | ".LB114", t => 2 + (mArg s - t.regs.rax.toNat)
  | ".LB113", _ => 1
  | _, _ => 0

end

end TopProof
end Bbu

namespace Bbu
namespace TopProof

-- The registers and the arguments as `s.regs.r.toBitVec`.
macro "top_nrm" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [bS, rsp, rdi,
  rsi, rdx, rcx, r8, rax, srcArg, dstArg, tgtArg, splArg, mArg, nArg, wordAt, STACK, DEST_eq, MAX_N,
  Reg64s.get64_rsp, Reg64s.get64_rdi, Reg64s.get64_rsi, Reg64s.get64_rdx, Reg64s.get64_rcx,
  Reg64s.get64_r8, Reg64s.get64_r9, Reg64s.get64_rax, Nat.reduceMul, Nat.reduceAdd] $(loc)?)

/-! ## The block `.LB113` -/

-- The memory at the call, in the form of the `kvcgen64` goals.
def cM2 (m : Mem 64) (R SI DI : Addr) : Mem 64 :=
  (m.storeInt (R + 8#64) 8 (SI - DI).toInt).storeInt (R + 16#64) 8 0

def cM3 (m : Mem 64) (R SI DI : Addr) : Mem 64 :=
  (cM2 m R SI DI).storeInt (R + 48#64) 8 (BitVec.toInt (rd (cM2 m R SI DI) (R + 16464#64)))

def cM (m : Mem 64) (R SI DI : Addr) : Mem 64 :=
  (cM3 m R SI DI).storeInt (R + 56#64) 8 (BitVec.toInt (rd (cM3 m R SI DI) (R + 16472#64)))

section
variable {s : MachineData} {ra : Int64} {m : Mem 64} {i : Nat} {t c u : MachineData}

-- A load in the frame or in the stack arguments succeeds.
theorem Cp.isSome (hp : TopPre s) (h : Cp s ra m i) {a : Addr}
    (ha : (a - (s.regs.rsp.toBitVec - 20688#64)).toNat + 8 ≤ 20688
      ∨ (a - s.regs.rsp.toBitVec).toNat + 8 ≤ 16) : (m.loadInt a 8).isSome := by
  have hm := Mapped.of_unchanged hp.mapped h.un h.map
  rcases ha with ha | ha
  · exact hm.loadInt_isSome (Or.inl ha)
  · exact hm.loadInt_isSome (Or.inr (Or.inr (Or.inr (Or.inl ha))))

set_option maxHeartbeats 1000000 in
-- The `Fm` at the call and the start state in the struct.
theorem at113_fm (hp : TopPre s) (h : At113 s ra t) :
    Fm s ra (cM t.dmem t.regs.rsp.toBitVec t.regs.rsi.toBitVec t.regs.rdi.toBitVec)
      ∧ stOf (cM t.dmem t.regs.rsp.toBitVec t.regs.rsi.toBitVec t.regs.rdi.toBitVec) (bS s) = st0 s := by
  obtain ⟨hcp, hrg, hdi, hsi⟩ := h
  have hge := hp.rsp_ge
  have hml := hp.m_le
  have hnl := hp.n_le'
  have h6 := hcp.arg hp (k := 0) (by omega)
  have h7 := hcp.arg hp (k := 8) (by omega)
  have c0 := hcp.w0
  have c3 := hcp.w3
  have c4 := hcp.w4
  have c5 := hcp.w5
  have cra := hcp.ra
  rw [hrg.rsp, hdi, hsi]
  top_nrm at hge hml hnl h6 h7 c0 c3 c4 c5 cra ⊢
  refine hcp.fm hp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [cM, cM3, cM2]
    repeat (refine Mem.UnchangedOutside.storeInt ?_ (by
      simp only [Mem.Blocks.Inside, topF_eq, or_false]; top_nrm; bv_omega) _)
    exact fun _ _ => rfl
  · simp only [cM, cM3, cM2]
    repeat (refine Mem.Mapped.storeInt ?_ _ _ _)
    exact hcp.map
  all_goals simp only [cM, cM3, cM2, wordAt]; top_nrm
  all_goals bbu_rd
  case refine_3 => exact cra
  case refine_4 => exact c0
  case refine_7 => exact c3
  case refine_8 => exact c4
  case refine_9 => exact c5
  · rw [show s.regs.rsp.toBitVec - 16464#64 + 16464#64 = s.regs.rsp.toBitVec + 0#64 by bv_omega, h6]
    simp only [opsArg, rsp, Reg64s.get64_rsp, BitVec.add_zero]
  · rw [show s.regs.rsp.toBitVec - 16464#64 + 16472#64 = s.regs.rsp.toBitVec + 8#64 by bv_omega, h7]
    simp only [blkArg, rsp, Reg64s.get64_rsp]
  · intro j hj
    have hc := hcp.cp j hj
    simp only [wordAt] at hc ⊢
    top_nrm at hc hj ⊢
    bbu_rd
    exact hc

-- A callee keeps `Rg`.
theorem Rg.call {F : Nat} (h : Rg s c) (hag : (mod F c).Agree c u) : Rg s u := by
  have hreg : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] →
      u.regs.get64 q = c.regs.get64 q := fun q hq => hag.1 q hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hreg .rsp (by simp); simp only [Reg64s.get64_rsp] at this; rw [this]; exact h.rsp
  · have := hreg .rbx (by simp); simp only [Reg64s.get64_rbx] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.rbx
  · have := hreg .rbp (by simp); simp only [Reg64s.get64_rbp] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.rbp
  · have := hreg .r12 (by simp); simp only [Reg64s.get64_r12] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r12
  · have := hreg .r13 (by simp); simp only [Reg64s.get64_r13] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r13
  · have := hreg .r14 (by simp); simp only [Reg64s.get64_r14] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r14
  · have := hreg .r15 (by simp); simp only [Reg64s.get64_r15] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r15

-- The precondition of `buildBottomUp` at `.LB113`.
theorem at113_pre (hp : TopPre s) (h : At113 s ra t)
    (hc : c.dmem = cM t.dmem t.regs.rsp.toBitVec t.regs.rsi.toBitVec t.regs.rdi.toBitVec)
    (hrsp : c.regs.rsp.toBitVec = bS s) (hdi : c.regs.rdi.toBitVec = bS s) : Pre loopF loopA c := by
  obtain ⟨hfm, hst⟩ := at113_fm hp h
  have hdi' : rdi c = bS s := hdi
  refine Fm.pre hp hfm hc hrsp hdi' ?_
  unfold loopA env st
  rw [hc, hdi']
  exact (hfm.init_loop hp hst).2

-- The state `u` after the call at `.LB113`.
theorem at113_aft (hp : TopPre s) (h : At113 s ra t)
    (hc : c.dmem = cM t.dmem t.regs.rsp.toBitVec t.regs.rsi.toBitVec t.regs.rdi.toBitVec)
    (hrg : Rg s c) (hdi : c.regs.rdi.toBitVec = bS s)
    (hpost : Post loopF loopR c u) (hag : (mod loopF c).Agree c u) :
    Fm s ra u.dmem ∧ Rg s u
      ∧ Res (bS s) (topRes s) (fun ops => rax u = 0#64 ∧ (stOf u.dmem (bS s)).trace = ops) u := by
  have hpre := at113_pre hp h hc hrg.rsp hdi
  obtain ⟨hfm, hst⟩ := at113_fm hp h
  have hdi' : rdi c = bS s := hdi
  refine ⟨Fm.call hp hfm hc hrg.rsp hdi' hpre hpost hag, hrg.call hag, ?_⟩
  have hres := hpost.2.2
  unfold loopR env st st' at hres
  rw [hdi', hc, (hfm.init_loop hp hst).1] at hres
  exact hres

-- The return address is at `rsp s - 8`.
theorem fm_retAddr (hp : TopPre s) (h : Fm s ra t.dmem)
    (hsp : t.regs.rsp.toBitVec = rsp s - 8#64) : t.retAddr = some ra := by
  have hge := hp.rsp_ge
  simp only [rsp, Reg64s.get64_rsp] at hge
  have hs : (t.dmem.loadInt (rsp s - 8#64) 8).isSome = true :=
    h.map.loadInt_isSome (Or.inl (by simp only [topF_eq, rsp, Reg64s.get64_rsp]; bv_omega))
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  have hra := h.ra
  rw [rd, hv, Option.get!_some] at hra
  rw [MachineData.retAddr, show t.regs.get64 .rsp = rsp s - 8#64 from hsp, hv, Option.map_some, hra,
    Int64.ofBitVec_toBitVec]

theorem fm_retAddr_isSome (hp : TopPre s) (h : Fm s ra t.dmem)
    (hsp : t.regs.rsp.toBitVec = rsp s - 8#64) : t.retAddr.isSome = true := by
  rw [fm_retAddr hp h hsp]; rfl

-- The ops in the struct are the ops in the buffer.
theorem ops_topOp {m : Mem 64} (h : Hd s m) (hu : u.dmem = m) :
    (List.range (stOf m (bS s)).trace.length).map (topOp s u) = (stOf m (bS s)).trace := by
  rw [nops_stOf]
  show (List.range (rd m (wordAt (bS s) 2)).toNat).map (topOp s u)
    = (List.range (rd m (wordAt (bS s) 2)).toNat).map (opOf m (bS s))
  refine List.map_congr_left fun i _ => ?_
  simp only [topOp, opOf, opsOf, h.ops, hu]

-- `testq %rax, %rax; cmove 16(%rsp), %rax`: the result of the model.
theorem topPost_of {v : MachineData} (hfm : Fm s ra u.dmem) (hrg : Rg s u)
    (hres : Res (bS s) (topRes s) (fun ops => rax u = 0#64 ∧ (stOf u.dmem (bS s)).trace = ops) u)
    (hv : v.dmem = u.dmem)
    (hax : v.regs.rax.toBitVec = if u.regs.rax.toBitVec = 0#64
      then rd u.dmem (u.regs.rsp.toBitVec + 16#64) else u.regs.rax.toBitVec) :
    TopPost s v := by
  refine ⟨by rw [hv]; exact fun x hx => hfm.map x (hx.elim Or.inl False.elim), ?_⟩
  have hb : blkOf u.dmem (bS s) = blkArg s := hfm.hd.blk
  change (match topRes s with
    | .ok ops => rax v = BitVec.ofNat 64 ops.length ∧ (List.range ops.length).map (topOp s v) = ops
    | .error (.blocked pos excess) =>
      rax v = -1#64 ∧ rd v.dmem (blkArg s) = BitVec.ofNat 64 pos
        ∧ rd v.dmem (wordAt (blkArg s) 1) = BitVec.ofNat 64 excess
    | .error .assertion => rax v = -2#64)
  unfold Res at hres
  simp only [rax, Reg64s.get64_rax] at hres ⊢
  rw [hax, hv, hrg.rsp]
  generalize topRes s = r at hres ⊢
  rcases r with (⟨pos, ex⟩ | _) | ops
  · obtain ⟨h1, h2, h3⟩ := hres
    rw [hb] at h2 h3
    rw [h1]
    exact ⟨by simp, h2, h3⟩
  · rw [hres]; simp
  · obtain ⟨h1, h2⟩ := hres
    subst h2
    dsimp only
    rw [h1]
    simp only [↓reduceIte]
    refine ⟨?_, ops_topOp hfm.hd hv⟩
    rw [nops_stOf]
    simp [wordAt]

-- `addq $16456, %rsp; ret` gives the postcondition.
theorem at113_ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    {t' v : MachineData} {b : Bool} (hp : TopPre s) (hfm : Fm s ra u.dmem) (hrg : Rg s u)
    (hres : Res (bS s) (topRes s) (fun ops => rax u = 0#64 ∧ (stOf u.dmem (bS s)).trace = ops) u)
    (hm' : t'.dmem = u.dmem) (hsp' : t'.regs.rsp.toBitVec = 16456#64 + u.regs.rsp.toBitVec)
    (hv : v.dmem = u.dmem) (hvsp : v.regs.rsp.toBitVec = 16456#64 + u.regs.rsp.toBitVec + 8#64)
    (hax : v.regs.rax.toBitVec = if CondCode.z.interp (StatusFlags.from_result
        (u.regs.rax.toBitVec &&& u.regs.rax.toBitVec) { cf := false, af := b, of := false }) = true
      then rd u.dmem (u.regs.rsp.toBitVec + 16#64) else u.regs.rax.toBitVec)
    (hbx : v.regs.rbx = u.regs.rbx) (hbp : v.regs.rbp = u.regs.rbp)
    (h12 : v.regs.r12 = u.regs.r12) (h13 : v.regs.r13 = u.regs.r13)
    (h14 : v.regs.r14 = u.regs.r14) (h15 : v.regs.r15 = u.regs.r15) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ TopPost s t ∧ (topMod s).Agree s t) t'.retAddr.get! v := by
  have hge := hp.rsp_ge
  have hr := hrg.rsp
  simp only [bS, rsp, Reg64s.get64_rsp] at hge hr
  have hra : t'.retAddr = some ra :=
    fm_retAddr hp (by rw [hm']; exact hfm) (by rw [hsp', hr]; simp only [rsp, Reg64s.get64_rsp]; bv_omega)
  have hsp : v.regs.rsp.toBitVec = s.regs.rsp.toBitVec := by rw [hvsp, hr]; bv_omega
  have hax' : v.regs.rax.toBitVec = if u.regs.rax.toBitVec = 0#64
      then rd u.dmem (u.regs.rsp.toBitVec + 16#64) else u.regs.rax.toBitVec := by
    rw [hax]; bbu_flags; simp only [BitVec.and_self]
  refine Or.inr ⟨⟨by simp [hra], topPost_of hfm hrg hres hv hax', fun q hq => ?_, ?_⟩,
    fun _ _ _ => ?_⟩
  · cases q <;> first | (exfalso; apply hq; simp [topMod]; done) | skip
    all_goals simp only [Reg64s.get64_rbx, Reg64s.get64_rsp, Reg64s.get64_rbp, Reg64s.get64_r12,
      Reg64s.get64_r13, Reg64s.get64_r14, Reg64s.get64_r15]
    · rw [hbx, hrg.rbx]
    · exact hsp
    · rw [hbp, hrg.rbp]
    · rw [h12, hrg.r12]
    · rw [h13, hrg.r13]
    · rw [h14, hrg.r14]
    · rw [h15, hrg.r15]
  · rw [hv]; exact hfm.hd.un
  · exact Kit.stackBelow_pushRa hsp

/-! ## The entry block and the copy loop -/

-- The memory after the entry block.
def eM (s : MachineData) (ra : Int64) : Mem 64 :=
  ((((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 16456#64 + 32#64) 8 s.regs.rcx.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 16456#64 + 24#64) 8 s.regs.rsi.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 16456#64 + 40#64) 8 s.regs.r9.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 16456#64) 8 s.regs.rdi.toBitVec.toInt

-- The memory after one round of the copy loop, in the form of the `kvcgen64` goals.
def cpM (m : Mem 64) (R SI R8 A : Addr) : Mem 64 :=
  (m.storeInt (R + A * 8#64 + 64#64) 8 (BitVec.toInt (rd m (SI + A * 8#64)))).storeInt
    (R + A * 8#64 + 8256#64) 8
    (BitVec.toInt (rd (m.storeInt (R + A * 8#64 + 64#64) 8 (BitVec.toInt (rd m (SI + A * 8#64))))
      (R8 + A * 8#64)))

-- A load of the entry block succeeds.
theorem ent_isSome (hp : TopPre s) {a : Addr}
    (h : (a - (s.regs.rsp.toBitVec - 20688#64)).toNat + 8 ≤ 20688
      ∨ (a - s.regs.rsp.toBitVec).toNat + 8 ≤ 16) : (s.dmem.loadInt a 8).isSome := by
  rcases h with h | h
  · exact hp.mapped.loadInt_isSome (Or.inl h)
  · exact hp.mapped.loadInt_isSome (Or.inr (Or.inr (Or.inr (Or.inl h))))

set_option maxHeartbeats 1000000 in
-- The entry block starts the copy loop.
theorem ent_cp (hp : TopPre s) : Cp s ra (eM s ra) 0 := by
  have hge := hp.rsp_ge
  top_nrm at hge
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  · simp only [eM]
    repeat (refine Mem.UnchangedOutside.storeInt ?_ (by
      simp only [Mem.Blocks.Inside, topF_eq, or_false]; top_nrm; bv_omega) _)
    exact fun _ _ => rfl
  · simp only [eM]
    repeat (refine Mem.Mapped.storeInt ?_ _ _ _)
    exact fun x hx => hp.mapped x (inside_of_mem List.mem_cons_self hx)
  all_goals simp only [eM, wordAt]; top_nrm; bbu_rd

-- The loads of the copy loop succeed.
theorem at114_some (hp : TopPre s) (h : At114 s ra t) {a : Addr}
    (ha : a = t.regs.rdx.toBitVec + t.regs.rax.toBitVec * 8#64
      ∨ a = t.regs.r8.toBitVec + t.regs.rax.toBitVec * 8#64
      ∨ a = t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 64#64
      ∨ a = t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 8256#64) :
    (t.dmem.loadInt a 8).isSome := by
  obtain ⟨hcp, hrg, -, -, hdx, h8, hax⟩ := h
  have hmap := Mapped.of_unchanged hp.mapped hcp.un hcp.map
  have hge := hp.rsp_ge
  have hml := hp.m_le
  have hnl := hp.n_le'
  have hr := hrg.rsp
  have hax' : t.regs.rax.toBitVec.toNat < mArg s := hax
  top_nrm at hge hml hnl hr hax' hdx h8
  rcases ha with rfl | rfl | rfl | rfl
  · exact hmap.loadInt_isSome (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      top_nrm; bv_omega))))))
  · exact hmap.loadInt_isSome (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      top_nrm; bv_omega)))))))
  all_goals exact hmap.loadInt_isSome (Or.inl (by
    simp only [topF_eq]; top_nrm; bv_omega))

set_option maxHeartbeats 1000000 in
-- One round of the copy loop copies slot `i`.
theorem copy_step (hp : TopPre s) (h : Cp s ra m i)
    {R SI R8 A : Addr} (hR : R = bS s) (hSI : SI = srcArg s)
    (h8 : R8 = dstArg s) (hA : A.toNat = i) (hi : i < mArg s) :
    Cp s ra (cpM m R SI R8 A) (i + 1) := by
  subst hR hSI h8 hA
  have hge := hp.rsp_ge
  have hml := hp.m_le
  have hnl := hp.n_le'
  top_nrm at hge hml hnl hi
  have hu := h.un
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
      (by simp only [Mem.Blocks.Inside, or_false, topF_eq] at hy1 ⊢
          top_nrm at hy1 ⊢; bv_omega)
      (inside_append.mpr (.inr (Or.inr (Or.inl (by
        simp only [Mem.Blocks.Inside, or_false] at hy2 ⊢; top_nrm at hy2 ⊢; bv_omega)))))
  have hcp : cpM m (bS s) (srcArg s) (dstArg s) A
      = (m.storeInt (bS s + A * 8#64 + 64#64) 8 (rd m (srcArg s + A * 8#64)).toInt).storeInt
        (bS s + A * 8#64 + 8256#64) 8 (rd m (dstArg s + A * 8#64)).toInt := by
    simp only [cpM, hdis]
  rw [hcp]
  clear hcp hdis
  obtain ⟨-, hmap, cra, c0, c3, c4, c5, hc⟩ := h
  refine ⟨(hu.storeInt ?_ _).storeInt ?_ _, (hmap.storeInt _ _ _).storeInt _ _ _,
    ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · simp only [Mem.Blocks.Inside, or_false, topF_eq]; top_nrm; bv_omega
  · simp only [Mem.Blocks.Inside, or_false, topF_eq]; top_nrm; bv_omega
  all_goals simp only [Copied, wordAt] at *
  all_goals top_nrm at *
  · bbu_rd; exact cra
  · bbu_rd; exact c0
  · bbu_rd; exact c3
  · bbu_rd; exact c4
  · bbu_rd; exact c5
  · by_cases hj' : j < A.toNat
    · obtain ⟨c1, c2⟩ := hc j hj'
      bbu_rd
      exact ⟨c1, c2⟩
    · have hjA : j = A.toNat := by omega
      subst hjA
      bbu_rd
      exact ⟨hsrc, hdst⟩

section
variable {t' : MachineData}

theorem at114_mem (hp : TopPre s) (h : At114 s ra t)
    (hm : t'.dmem = cpM t.dmem t.regs.rsp.toBitVec t.regs.rdx.toBitVec t.regs.r8.toBitVec
      t.regs.rax.toBitVec) : Cp s ra t'.dmem (t.regs.rax.toNat + 1) := by
  obtain ⟨hcp, hrg, -, -, hdx, h8, hax⟩ := h
  rw [hm]; exact copy_step hp hcp hrg.rsp hdx h8 rfl hax

-- `.LB114` jumps back to `.LB114`.
theorem at114_next (hp : TopPre s) (h : At114 s ra t)
    (hm : t'.dmem = cpM t.dmem t.regs.rsp.toBitVec t.regs.rdx.toBitVec t.regs.r8.toBitVec
      t.regs.rax.toBitVec) (hrg : Rg s t') (hdi : t'.regs.rdi.toBitVec = rdi s)
    (hsi : t'.regs.rsi.toBitVec = rsi s) (hdx : t'.regs.rdx.toBitVec = srcArg s)
    (h8 : t'.regs.r8.toBitVec = dstArg s) (hax : t'.regs.rax.toNat = t.regs.rax.toNat + 1)
    (hlt : t'.regs.rax.toNat < mArg s) : At114 s ra t' :=
  ⟨hax ▸ at114_mem hp h hm, hrg, hdi, hsi, hdx, h8, hlt⟩

-- `.LB114` falls through to `.LB113`.
theorem at113_of114 (hp : TopPre s) (h : At114 s ra t)
    (hm : t'.dmem = cpM t.dmem t.regs.rsp.toBitVec t.regs.rdx.toBitVec t.regs.r8.toBitVec
      t.regs.rax.toBitVec) (hrg : Rg s t') (hdi : t'.regs.rdi.toBitVec = rdi s)
    (hsi : t'.regs.rsi.toBitVec = rsi s) (hax : t.regs.rax.toNat + 1 = mArg s) : At113 s ra t' :=
  ⟨hax ▸ at114_mem hp h hm, hrg, hdi, hsi⟩

-- The entry block jumps to `.LB113` for `m = 0`.
theorem at113_ent (hp : TopPre s) (hm : t.dmem = eM s ra) (hrg : Rg s t)
    (hdi : t.regs.rdi.toBitVec = rdi s) (hsi : t.regs.rsi.toBitVec = rsi s) (h0 : mArg s = 0) :
    At113 s ra t :=
  ⟨by rw [hm, h0]; exact ent_cp hp, hrg, hdi, hsi⟩

-- The entry block falls through to `.LB114` for `0 < m`.
theorem at114_ent (hp : TopPre s) (hm : t.dmem = eM s ra) (hrg : Rg s t)
    (hdi : t.regs.rdi.toBitVec = rdi s) (hsi : t.regs.rsi.toBitVec = rsi s)
    (hdx : t.regs.rdx.toBitVec = srcArg s) (h8 : t.regs.r8.toBitVec = dstArg s)
    (hax : t.regs.rax.toNat = 0) (h0 : 0 < mArg s) : At114 s ra t :=
  ⟨by rw [hm, hax]; exact ent_cp hp, hrg, hdi, hsi, hdx, h8, hax ▸ h0⟩

end

end

end TopProof
end Bbu

/-! ## The `vcgen` spec of `cmove 16(%rsp), %rax` -/

namespace Program.WP

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

-- `cmovcc disp(%b), %rd`: the load happens for both values of the condition.
@[spec] theorem cmov_load_spec (cc : CondCode) (rd b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 rd (if cc.interp s.status
            then BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get! else s.regs.get64 rd) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmovcc cc (.low rd .W64) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.load,
    MachineData.setReg, Reg64s.set_low_W64, Reg64s.get_low_W64, AddrExpr.zeroExtend_interp_base_disp,
    Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

end Program.WP

set_option experimental.vcgen true

local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

-- The stack goal of a jump: `rsp` is below the entry `rsp`.
local macro "cfg_stk" : tactic => `(tactic| (
  apply MachineData.stackAtOrBelow_of_toNat_lt
  simp only [Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp]
  bv_omega))

namespace Bbu
open TopProof

set_option maxHeartbeats 4000000 in
theorem buildBottomUp_body [Host] [FunDecls] (hloop : Spec "buildBottomUp" loopF loopA loopR) :
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ TopPre s ⦄ buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ TopPost s t ∧ (topMod s).Agree s t ⦄ := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hp⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (fun
      | .entry, t | .label "build_bottom_up", t => t = s.pushRa ra
      | .label ".LB114", t => At114 s ra t
      | .label ".LB113", t => At113 s ra t
      | _, _ => False)
    (V s) ?_ rfl
  cfg_cases
  case left t ht => subst ht; kvcgen64
  case right.left t ht =>
    subst ht
    have hge := hp.rsp_ge
    simp only [rsp, Reg64s.get64_rsp] at hge
    clear hloop
    kvcgen64
    all_goals bbu_norm at *
    case vc5 _ hz _ =>
      bbu_flags at hz
      simp only [BitVec.and_self] at hz
      cfg_goto
      · cfg_stk
      · exact at113_ent hp rfl ⟨by top_nrm; bv_omega, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
          (by top_nrm; rw [hz]; rfl)
      · left; show 1 < 2 ^ 12; omega
    case vc6 _ hz _ =>
      bbu_flags at hz
      simp only [BitVec.and_self] at hz
      exact at114_ent hp rfl ⟨by top_nrm; bv_omega, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
        (by top_nrm; bv_omega)
    case vc7 =>
      left
      have h1 := hp.m_le
      have h2 := hp.n_le'
      show 2 + (mArg s - (0#64 : BitVec 64).toNat) < 2 ^ 12
      simp only [BitVec.toNat_zero, Nat.sub_zero]
      omega
    all_goals
      repeat (apply loadInt_isSome_store)
      apply ent_isSome hp
      first | (left; bv_omega) | (right; bv_omega)
  case right.right.left t ht =>
    have h114 := ht
    obtain ⟨hcp, hrg, hdi, hsi, hdx, h8, hax⟩ := ht
    have hge := hp.rsp_ge
    have hr := hrg.rsp
    have hax' : t.regs.rax.toBitVec.toNat < mArg s := hax
    top_nrm at hge hr hdi hsi hdx h8 hax'
    clear hloop
    kvcgen64
    all_goals bbu_norm at *
    case vc1 => exact at114_some hp h114 (Or.inl rfl)
    case vc2 => exact at114_some hp h114 (Or.inr (Or.inr (Or.inl rfl)))
    case vc3 =>
      apply loadInt_isSome_store; exact at114_some hp h114 (Or.inr (Or.inl rfl))
    case vc4 =>
      apply loadInt_isSome_store; exact at114_some hp h114 (Or.inr (Or.inr (Or.inr rfl)))
    case vc5 hz _ =>
      bbu_flags at hz
      have h1 : (1#64 + t.regs.rax.toBitVec).toNat = t.regs.rax.toBitVec.toNat + 1 := by bv_omega
      cfg_goto
      · cfg_stk
      · refine at114_next hp h114 rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6, hrg.7⟩
          hdi hsi hdx h8 h1 ?_
        show (1#64 + t.regs.rax.toBitVec).toNat < _
        top_nrm; bv_omega
      · left
        show 2 + (mArg s - (1#64 + t.regs.rax.toBitVec).toNat)
          < 2 + (mArg s - t.regs.rax.toBitVec.toNat)
        simp only [mArg, rdi, Reg64s.get64_rdi]; omega
    case vc6 hz _ =>
      bbu_flags at hz
      exact at113_of114 hp h114 rfl ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6, hrg.7⟩ hdi hsi
        (by show t.regs.rax.toBitVec.toNat + 1 = _; top_nrm; bv_omega)
    case vc7 => left; show 1 < 2 + _; omega
  case right.right.right t ht =>
    have h113 := ht
    obtain ⟨hcp, hrg, hdi, hsi⟩ := ht
    have hge := hp.rsp_ge
    have hr := hrg.rsp
    top_nrm at hge hr
    kvcgen64 [hloop]
    all_goals bbu_norm at *
    all_goals first
      | ((repeat apply loadInt_isSome_store); exact hcp.isSome hp (by
          rw [hr]; first | (left; bv_omega) | (right; bv_omega)); done)
      | skip
    case vc8 => exact at113_pre hp h113 rfl hrg.rsp hrg.rsp
    all_goals
      rename_i u hpost hag _ _
      obtain ⟨hfm, hrgu, hres⟩ :=
        at113_aft hp h113 (by exact rfl)
          (by exact ⟨hrg.1, hrg.2, hrg.3, hrg.4, hrg.5, hrg.6, hrg.7⟩) (by exact hrg.rsp) hpost hag
      have hru := hrgu.rsp
      top_nrm at hru
    case vc9 =>
      exact hfm.wf.isSome_struct (by rw [hru]; simp only [WORDS_eq]; top_nrm; bv_omega)
    case vc10 =>
      exact fm_retAddr_isSome hp hfm (by dsimp only; rw [hru]; top_nrm; bv_omega)
    case vc11 =>
      exact at113_ret hp hfm hrgu hres rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end Bbu
