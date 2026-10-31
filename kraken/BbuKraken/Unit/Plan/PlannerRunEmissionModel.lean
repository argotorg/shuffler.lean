import BbuKraken.Unit.Plan.PlannerRunEmissionLayout
import BbuKraken.Unit.Plan.PlannerRunEmissionDefs
import BbuKraken.Unit.Plan.PlannerRunSafeCtor

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

theorem ctorP_data (data old target : Vector StackSlot MAX_N) (m n : Word)
    (M : Flat.Mapping) (spills : BitVec 32 → BitVec 8) (u : Flat.Uninit) :
    Flat.ctorP data m target n M spills u =
      { Flat.ctorP old m target n M spills u with data := data } := by
  simp only [Flat.ctorP, Flat.pend_fold]

theorem mapping_copy_eq {m n : Word} (u M : Flat.Mapping)
    (hm : m.toNat ≤ MAX_N) (hn : n.toNat ≤ MAX_N)
    (hd : ∀ p, p < m → get u.dest p = get M.dest p)
    (hp : ∀ p, p < n → get u.pos p = get M.pos p) :
    u.copy M m n = u := by
  have copy_eq (v w : Vector Word MAX_N) (k : Word) (hk : k.toNat ≤ MAX_N)
      (he : ∀ p, p < k → get v p = get w p) :
      (offsets k).foldl (fun v p => put v p (get w p)) v = v := by
    apply Vector.ext
    intro i hi
    rw [Flat.copy_get _ _ _ hk hi]
    split
    · rename_i hik
      have hh := he (BitVec.ofNat 64 i) (ofNat_lt_word hk hik)
      simpa only [get_ofNat _ hi] using hh.symm
    · rfl
  cases u
  simp only [Flat.Mapping.copy, copy_eq _ _ _ hm hd, copy_eq _ _ _ hn hp]

theorem unmapped_range (st : Flat.St) (hn : st.targetSize.toNat ≤ MAX_N)
    (i : Nat) (hi : i ≤ st.targetSize.toNat) (c : Word) :
    Flat.unmappedFrom st (BitVec.ofNat 64 i) c =
      c + BitVec.ofNat 64 ((List.range' i (st.targetSize.toNat - i)).countP
        (fun j => get st.pos (BitVec.ofNat 64 j) = NONE)) := by
  by_cases hit : i < st.targetSize.toNat
  · have hiw : BitVec.ofNat 64 i < st.targetSize := ofNat_lt_word hn hit
    rw [RunU.unmapped_step hiw]
    have hs : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
      simp only [BitVec.ofNat_add]
    rw [hs, unmapped_range st hn (i + 1) (by omega)]
    have hc : st.targetSize.toNat - i = (st.targetSize.toNat - (i + 1)) + 1 := by omega
    rw [hc, List.range'_succ]
    by_cases hz : get st.pos (BitVec.ofNat 64 i) = NONE
    · simp only [hz, ↓reduceIte, List.countP_cons, decide_true, Bool.toNat_true,
        BitVec.ofNat_add]
      bv_omega
    · simp only [List.countP_cons, hz, decide_false, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero]
  · have he : i = st.targetSize.toNat := by omega
    have hw : BitVec.ofNat 64 i = st.targetSize := by
      rw [he, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [hw, RunU.unmapped_end]
    simp only [he, Nat.sub_self, List.range'_zero, List.countP_nil,
      BitVec.add_zero]
termination_by st.targetSize.toNat - i
decreasing_by omega

theorem unmapped_offsets (st : Flat.St) (hn : st.targetSize.toNat ≤ MAX_N) :
    Flat.unmappedFrom st 0#64 0#64 =
      BitVec.ofNat 64 ((offsets st.targetSize).countP (fun d => get st.pos d = NONE)) := by
  rw [unmapped_range st hn 0 (Nat.zero_le _)]
  simp only [Nat.sub_zero, BitVec.zero_add, offsets, List.countP_map,
    List.range_eq_range']
  rfl

theorem unmapped_congr {st a : Flat.St} (hn : a.targetSize = st.targetSize)
    (hp : ∀ p, p < st.targetSize → get a.pos p = get st.pos p) (i c : Word) :
    Flat.unmappedFrom a i c = Flat.unmappedFrom st i c := by
  conv =>
    lhs
    rw [Flat.unmappedFrom, hn]
  conv =>
    rhs
    rw [Flat.unmappedFrom]
  split
  · rename_i hi
    rw [hp i hi]
    exact unmapped_congr hn hp (i + 1) _
  · rfl
termination_by (st.targetSize - i).toNat
decreasing_by exact Flat.sub_succ_lt ‹i < st.targetSize›

theorem ctorP_unmapped (data target : Vector StackSlot MAX_N) (m n : Word)
    (M : Flat.Mapping) (spills : BitVec 32 → BitVec 8) (u : Flat.Uninit)
    (hn : n.toNat ≤ MAX_N) :
    let C := (⟨u.dest, u.pos⟩ : Flat.Mapping).copy M m n
    let st : Flat.St :=
      { target := target, targetSize := n, spills := spills, data := data, size := m,
        trace := [], dest := C.dest, pos := C.pos, pend := 0,
        blockedOffset := u.blockedOffset, blockedExcess := u.blockedExcess }
    Flat.ctorP data m target n M spills u =
      { st with pend := Flat.unmappedFrom st 0#64 0#64 } := by
  dsimp only
  rw [Flat.ctorP, Flat.pend_fold, unmapped_offsets _ hn]
  dsimp only
  congr 1
  bv_omega

theorem local_word_eq {locals : List Word} {i : Nat} {w : Word}
    (hi : i < locals.length) (h : locals[i]? = some w) : locals[i] = w := by
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

theorem CtorHeader.localHdr {g : PlannerRunG} {locals : List Word}
    (h : CtorHeader g locals) (hl : locals.length = 4121) :
    let a := localEmissionHdr locals hl
    a.tgt = g.p.tgt ∧ a.n = g.p.n ∧ a.spl = g.p.spl ∧ a.data = g.dataPtr ∧
      a.len = g.p.m ∧ a.ops = g.opsPtr ∧ a.nops = 0#64 :=
  ⟨local_word_eq (by omega) h.1, local_word_eq (by omega) h.2.1,
    local_word_eq (by omega) h.2.2.1, local_word_eq (by omega) h.2.2.2.1,
    local_word_eq (by omega) h.2.2.2.2.1, local_word_eq (by omega) h.2.2.2.2.2.1,
    local_word_eq (by omega) h.2.2.2.2.2.2⟩

theorem WordPrefix.localHdr_dest {locals : List Word} (hl : locals.length = 4121)
    {v : Vector Word MAX_N} {m : Word} (hm : m.toNat ≤ MAX_N)
    (h : WordPrefix locals 2067 v m.toNat) {p : Word} (hp : p < m) :
    get (localEmissionHdr locals hl).dest p = get v p := by
  have hpN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hm
  rw [get_eq _ hpN]
  change ((locals.drop 2067).take 1024)[p.toNat]'(by
    simp only [List.length_take, List.length_drop, hl]
    change p.toNat < 1024 at hpN
    omega) = _
  rw [List.getElem_take, List.getElem_drop]
  have he := h p.toNat (BitVec.lt_def.mp hp)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at he
  exact local_word_eq (by change p.toNat < 1024 at hpN; omega) he

theorem WordPrefix.localHdr_pos {locals : List Word} (hl : locals.length = 4121)
    {v : Vector Word MAX_N} {n : Word} (hn : n.toNat ≤ MAX_N)
    (h : WordPrefix locals 3091 v n.toNat) {p : Word} (hp : p < n) :
    get (localEmissionHdr locals hl).pos p = get v p := by
  have hpN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hn
  rw [get_eq _ hpN]
  change ((locals.drop 3091).take 1024)[p.toNat]'(by
    simp only [List.length_take, List.length_drop, hl]
    change p.toNat < 1024 at hpN
    omega) = _
  rw [List.getElem_take, List.getElem_drop]
  have he := h p.toNat (BitVec.lt_def.mp hp)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at he
  exact local_word_eq (by change p.toNat < 1024 at hpN; omega) he

def localCtorState (g : PlannerRunG) (h : Hdr) : Flat.St where
  target := g.p.fl.target
  targetSize := g.p.n
  spills := g.spills
  data := g.data.map StackSlot.ofWord
  size := g.p.m
  trace := []
  dest := h.dest
  pos := h.pos
  pend := h.pend
  blockedOffset := h.blkOff
  blockedExcess := h.blkExc

theorem EmitCountLI.ctorP {P : Addr} {g : PlannerRunG} {M : Flat.Mapping}
    {F : MProp 64} {s t : MachineData} {ra : Int64} {lo locals : List Word}
    (h : EmitCountLI P g M F s ra lo locals t) (hok : g.Ok)
    (hpending : locals[4115]? = some (Flat.unmappedFrom (countState g M) 0 0)) :
    let a := localEmissionHdr locals h.localLength
    Flat.ctorP (g.data.map StackSlot.ofWord) g.p.m g.p.fl.target g.p.n M g.spills
      ⟨a.dest, a.pos, a.blkOff, a.blkExc⟩ = localCtorState g a := by
  let a := localEmissionHdr locals h.localLength
  have hd : ∀ p, p < g.p.m → get a.dest p = get M.dest p :=
    fun _ hp => h.dest.localHdr_dest h.localLength hok.planner.m hp
  have hp : ∀ p, p < g.p.n → get a.pos p = get M.pos p :=
    fun _ hp => h.pos.localHdr_pos h.localLength hok.planner.n hp
  have hc := mapping_copy_eq (⟨a.dest, a.pos⟩ : Flat.Mapping) M
    hok.planner.m hok.planner.n hd hp
  have hcount : Flat.unmappedFrom ({localCtorState g a with pend := 0}) 0#64 0#64 =
      a.pend := by
    have he := unmapped_congr (st := countState g M)
      (a := {localCtorState g a with pend := 0}) rfl hp 0#64 0#64
    exact he.trans (local_word_eq (by rw [h.localLength]; decide) hpending).symm
  change Flat.ctorP (g.data.map StackSlot.ofWord) g.p.m g.p.fl.target g.p.n M g.spills
    ⟨a.dest, a.pos, a.blkOff, a.blkExc⟩ = localCtorState g a
  rw [ctorP_unmapped _ _ _ _ _ _ _ hok.planner.n]
  change {localCtorState g a with
    dest := ((⟨a.dest, a.pos⟩ : Flat.Mapping).copy M g.p.m g.p.n).dest
    pos := ((⟨a.dest, a.pos⟩ : Flat.Mapping).copy M g.p.m g.p.n).pos
    pend := Flat.unmappedFrom
      {localCtorState g a with
        dest := ((⟨a.dest, a.pos⟩ : Flat.Mapping).copy M g.p.m g.p.n).dest
        pos := ((⟨a.dest, a.pos⟩ : Flat.Mapping).copy M g.p.m g.p.n).pos
        pend := 0} 0#64 0#64} = _
  rw [hc]
  change {localCtorState g a with pend := Flat.unmappedFrom ({localCtorState g a with pend := 0}) 0#64 0#64} = _
  rw [hcount]
  rfl

end Bbu.Unit.PlannerRunU
