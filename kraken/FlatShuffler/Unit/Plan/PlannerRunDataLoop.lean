module

public import FlatShuffler.Unit.Plan.PlannerRunDataFrame
import all FlatShuffler.Unit.Plan.PlannerRunDataFrame
public import FlatShuffler.Unit.Plan.PlannerRunBlockedLoop
import all FlatShuffler.Unit.Plan.PlannerRunBlockedLoop

@[expose] public section

namespace FlatShuffler.Flat

set_option maxRecDepth 4096

local macro "data_norm" : tactic => `(tactic|
  (try simp_all only [restoreData_size, restoreData_targetSize, restoreData_target,
    restoreData_pos, restoreData_dest, restoreData_pend, restoreData_spills,
    restoreData_isFinal, restoreData_isSwapReachable, restoreData_isDupReachable,
    restoreData_depthOf, BitVec.ofNat_eq_ofNat,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not,
    Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte]))

-- Restore the data tail in each return or continuation of the bottom-up loop.
def restoreNext (cap : Nat) (old : Vector StackSlot MAX_N) : Next → Next
  | .ret r => .ret (r.1, restoreData cap old r.2)
  | .cont st t => .cont (restoreData cap old st) t

@[simp] theorem restoreData_isFinal (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (p : Word) : isFinal (restoreData cap old st) p = isFinal st p := by
  simp only [isFinal, restoreData_dest]

@[simp] theorem restoreData_isSpilled (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (slot : StackSlot) : isSpilled (restoreData cap old st) slot = isSpilled st slot := by
  simp only [isSpilled, restoreData_spills]

@[simp] theorem restoreData_depthOf (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (p : Word) : depthOf (restoreData cap old st) p = depthOf st p := by
  simp only [depthOf, restoreData_size]

@[simp] theorem restoreData_isSwapReachable (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (p : Word) :
    isSwapReachable (restoreData cap old st) p = isSwapReachable st p := by
  simp only [isSwapReachable, restoreData_depthOf]

@[simp] theorem restoreData_isDupReachable (cap : Nat) (old : Vector StackSlot MAX_N)
    (st : St) (p : Word) :
    isDupReachable (restoreData cap old st) p = isDupReachable st p := by
  simp only [isDupReachable, restoreData_depthOf]

section
variable (cap : Nat) (old : Vector StackSlot MAX_N)

theorem restoreData_produce (st : St) (t : Word)
    (hs : st.size.toNat < cap) :
    produce (restoreData cap old st) t =
      let r := produce st t
      (r.1, restoreData cap old r.2) := by
  have hcopy := restoreData_shallowestCopyPosition cap old st (get st.target t) (Nat.le_of_lt hs)
  have hfin (r : Status × St) :
      Unit.ProduceProof.fin (r.1, restoreData cap old r.2) t =
        let out := Unit.ProduceProof.fin r t
        (out.1, restoreData cap old out.2) := by
    unfold Unit.ProduceProof.fin
    simp only [restoreData_pos, restoreData_size]
    split
    · rfl
    · split
      · rfl
      · unfold restoreData
        rfl
  have hact : Unit.ProduceProof.act (restoreData cap old st)
      (get st.target t) (shallowestCopyPosition st (get st.target t)) t =
      let r := Unit.ProduceProof.act st (get st.target t)
        (shallowestCopyPosition st (get st.target t)) t
      (r.1, restoreData cap old r.2) := by
    unfold Unit.ProduceProof.act Unit.ProduceProof.tail
    simp only [restoreData_isDupReachable, restoreData_isSpilled]
    split
    · exact restoreData_push cap old st _ t hs
    · split
      · rename_i hd
        have hc : (shallowestCopyPosition st (get st.target t)).toNat < cap :=
          Nat.lt_trans (BitVec.lt_def.mp (Unit.PlannerRunU.shallowestCopy_lt hd.1)) hs
        exact restoreData_dup cap old st _ t hs hc
      · split
        · exact restoreData_push cap old st _ t hs
        · split
          · exact restoreData_blockDupUnreachable cap old st _
          · rfl
  rw [Unit.ProduceProof.produce_eq, Unit.ProduceProof.produce_eq]
  simp only [restoreData_target, hcopy, hact]
  exact hfin _

theorem restoreData_generate (st : St) (t : Word) (hf : FInv st)
    (hp : st.pend ≠ 0) (hcap : st.targetSize.toNat ≤ cap) :
    generate (restoreData cap old st) t =
      let r := generate st t
      (r.1, restoreData cap old r.2) := by
  have hs : st.size.toNat < cap :=
    Nat.lt_of_lt_of_le (BitVec.lt_def.mp (hf.size_lt hp)) hcap
  unfold generate
  simp only [restoreData_targetSize]
  split
  · data_norm <;> rfl
  · rename_i ht
    have ht' : t < st.targetSize := Decidable.not_not.mp ht
    rw [restoreData_produce cap old st t hs]
    dsimp only
    split
    · data_norm <;> rfl
    · rename_i hd
      have hdone : (produce st t).1 = .done := Decidable.not_not.mp hd
      obtain ⟨out, hg, he⟩ := produce_grow hdone
      have hsout : (produce st t).2.size.toNat ≤ cap := by
        rw [he]
        change out.size.toNat ≤ cap
        rw [hg.size]
        have hm := hf.n
        have hsN := hf.size_le
        have hN : MAX_N = 1024 := rfl
        rw [hN] at hm
        bv_omega
      simp only [restoreData_size, restoreData_isFinal]
      split
      · rename_i hmid
        have htcap : t.toNat < cap := by
          have htN := BitVec.lt_def.mp ht'
          omega
        have htop : ((produce st t).2.size - 1).toNat < cap := by
          have htN := BitVec.lt_def.mp ht'
          have hn := hf.n
          have hsN := hf.size_le
          have hsz : (produce st t).2.size = st.size + 1 := by rw [he]; exact hg.size
          rw [hsz]
          simp only [BitVec.add_sub_cancel]
          exact hs
        rw [restoreData_get cap old _ t htcap,
          restoreData_get cap old _ _ htop]
        split
        · rw [restoreData_swapDestinations]
        · simp only [restoreData_isSwapReachable]
          split
          · data_norm <;> exact restoreData_swapWith cap old _ t hsout
          · data_norm <;> rfl
      · data_norm <;> rfl

theorem restoreData_urgentFrom (st : St) (t o u : Word) (hs : st.size.toNat ≤ cap) :
    urgentFrom (restoreData cap old st) t o u =
      (urgentFrom st t o u).mapError (fun r => (r.1, restoreData cap old r.2)) := by
  conv => lhs; rw [urgentFrom]
  conv => rhs; rw [urgentFrom]
  simp only [restoreData_targetSize, restoreData_pos, restoreData_target,
    restoreData_shallowestCopyPosition cap old st _ hs, restoreData_isSpilled,
    restoreData_isDupReachable, restoreData_depthOf]
  split
  · split
    · data_norm <;> exact restoreData_urgentFrom st t (o + 1) u hs
    · split
      · data_norm <;> exact restoreData_urgentFrom st t (o + 1) u hs
      · split
        · split
          · simp_all [restoreData_blockDupUnreachable, Except.mapError]
          · data_norm <;> exact restoreData_urgentFrom st t (o + 1) _ hs
        · data_norm <;> exact restoreData_urgentFrom st t (o + 1) u hs
  · data_norm <;> rfl
termination_by (st.targetSize - o).toNat
decreasing_by all_goals exact sub_succ_lt ‹o < st.targetSize›

theorem restoreData_placeTop (st : St) (t : Word) (hs : st.size.toNat ≤ cap) :
    placeTop (restoreData cap old st) t = restoreNext cap old (placeTop st t) := by
  unfold placeTop
  simp only [restoreData_size, restoreData_isFinal, restoreData_isSwapReachable]
  split
  · data_norm <;> rfl
  · split
    · data_norm <;> rfl
    · split
      · split
        · simp_all [restoreData_blockSwapUnreachable, restoreNext, BitVec.ofNat_eq_ofNat]
        · rw [restoreData_swapWith cap old st t hs]
          dsimp only
          split <;> data_norm <;> rfl
      · data_norm <;> rfl

theorem restoreData_candidateFrom (st : St) (slot : StackSlot) (source candidate : Word)
    (hs : st.size.toNat ≤ cap) (hc : candidate < st.size) :
    candidateFrom (restoreData cap old st) slot source candidate =
      candidateFrom st slot source candidate := by
  conv => lhs; rw [candidateFrom]
  conv => rhs; rw [candidateFrom]
  rw [restoreData_get cap old st candidate (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hc) hs)]
  simp only [restoreData_isFinal]
  split
  · split
    · data_norm <;> rfl
    · data_norm
      apply restoreData_candidateFrom st slot source (candidate - 1) hs
      bv_omega
  · data_norm <;> rfl
termination_by candidate.toNat
decreasing_by bv_omega

theorem restoreData_kBoundSw (st : St) (t p : Word) (hs : st.size.toNat ≤ cap) :
    kBoundSw (restoreData cap old st) t p = restoreNext cap old (kBoundSw st t p) := by
  unfold kBoundSw
  simp only [restoreData_size, restoreData_isSwapReachable]
  split
  · data_norm <;> rfl
  · split
    · split
      · simp_all [restoreData_blockSwapUnreachable, restoreNext, BitVec.ofNat_eq_ofNat]
      · rw [restoreData_swapWith cap old st p hs]
        dsimp only
        split
        · data_norm <;> rfl
        · rename_i hd
          data_norm
          rw [restoreData_placeTop cap old _ t]
          rw [swapWith_size]
          exact hs
    · data_norm <;> exact restoreData_placeTop cap old st t hs

 theorem restoreData_bound (st : St) (t : Word) (hf : FInv st)
    (ht : t < st.targetSize) (hcap : st.targetSize.toNat ≤ cap) :
    bound (restoreData cap old st) t = restoreNext cap old (bound st t) := by
  rw [bound_eq, bound_eq]
  simp only [restoreData_pos, restoreData_size]
  split
  · data_norm <;> rfl
  · rename_i hp
    have hp' : get st.pos t ≠ NONE ∧ get st.pos t ≥ t := Decidable.not_not.mp hp
    have hb := Unit.PlannerRunU.bound_pos_lt hf ht hp'.1
    have hs := Nat.le_trans hf.size_le hcap
    have htb : t.toNat < cap := Nat.lt_of_lt_of_le (BitVec.lt_def.mp (show t < st.size by bv_omega)) hs
    have hbb := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hb) hs
    rw [restoreData_get cap old st t htb, restoreData_get cap old st (get st.pos t) hbb]
    have htop : st.size - 1 < st.size := by bv_omega
    rw [restoreData_candidateFrom cap old st _ _ _ hs htop]
    let p := if get st.data t = get st.data (get st.pos t) then t
      else candidateFrom st (get st.data (get st.pos t)) (get st.pos t) (st.size - 1)
    have hpb : p.toNat < cap := Nat.lt_of_lt_of_le
      (BitVec.lt_def.mp (Unit.PlannerRunU.bound_candidate_lt hf ht hp')) hs
    change kB (restoreData cap old st) t (get st.pos t) p = restoreNext cap old (kB st t (get st.pos t) p)
    unfold kB
    rw [restoreData_get cap old st p hpb, restoreData_get cap old st (get st.pos t) hbb]
    split
    · data_norm <;> rfl
    · rw [restoreData_swapDestinations]
      data_norm <;> exact restoreData_kBoundSw cap old _ t p hs

theorem restoreData_kGenAt (st : St) (t u : Word) (hf : FInv st)
    (hp : st.pend ≠ 0) (hcap : st.targetSize.toNat ≤ cap) :
    kGenAt (restoreData cap old st) t u = restoreNext cap old (kGenAt st t u) := by
  unfold kGenAt
  rw [restoreData_generate cap old st u hf hp hcap]
  dsimp only
  split <;> data_norm <;> rfl

theorem restoreData_kGenT (st : St) (t : Word) (hf : FInv st)
    (hp : st.pend ≠ 0) (hcap : st.targetSize.toNat ≤ cap) :
    kGenT (restoreData cap old st) t = restoreNext cap old (kGenT st t) := by
  unfold kGenT
  rw [restoreData_generate cap old st t hf hp hcap]
  dsimp only
  split
  · data_norm <;> rfl
  · rename_i hd
    have hdone := Decidable.not_not.mp hd
    have hs : (generate st t).2.size.toNat ≤ cap := by
      have hfn := (hf.generate hp hdone).1.size_le
      rw [(generate_done hdone).1] at hfn
      exact Nat.le_trans hfn hcap
    simp only [restoreData_size, restoreData_isFinal]
    split
    · data_norm <;> rfl
    · split
      · data_norm <;> rfl
      · data_norm <;> exact restoreData_placeTop cap old _ t hs

theorem restoreData_kU3 (st : St) (t : Word) (hf : FInv st)
    (hp : st.pend ≠ 0) (ht : t < st.targetSize) (hcap : st.targetSize.toNat ≤ cap) :
    kU3 (restoreData cap old st) t = restoreNext cap old (kU3 st t) := by
  unfold kU3
  simp only [restoreData_pos]
  split
  · exact restoreData_bound cap old st t hf ht hcap
  · exact restoreData_kGenT cap old st t hf hp hcap

theorem restoreData_kU2 (st : St) (t u : Word) (hf : FInv st)
    (hp : st.pend ≠ 0) (ht : t < st.targetSize) (hcap : st.targetSize.toNat ≤ cap) :
    kU2 (restoreData cap old st) t u = restoreNext cap old (kU2 st t u) := by
  unfold kU2
  simp only [restoreData_size, restoreData_targetSize, restoreData_pos]
  split
  · exact restoreData_kGenAt cap old st t st.size hf hp hcap
  · exact restoreData_kU3 cap old st t hf hp ht hcap

theorem restoreData_kU (st : St) (t u : Word) (hf : FInv st)
    (hp : st.pend ≠ 0) (ht : t < st.targetSize) (hcap : st.targetSize.toNat ≤ cap) :
    kU (restoreData cap old st) t u = restoreNext cap old (kU st t u) := by
  unfold kU
  simp only [restoreData_size]
  split
  · exact restoreData_kGenAt cap old st t u hf hp hcap
  · exact restoreData_kU2 cap old st t u hf hp ht hcap

theorem restoreData_body (st : St) (t : Word) (hf : FInv st)
    (ht : t < st.targetSize) (hcap : st.targetSize.toNat ≤ cap)
    (hperm : st.size = st.targetSize →
      permuteMapping (restoreData cap old st) =
        let r := permuteMapping st; (r.1, restoreData cap old r.2)) :
    body (restoreData cap old st) t = restoreNext cap old (body st t) := by
  conv => lhs; rw [body_eq]
  conv => rhs; rw [body_eq]
  simp only [restoreData_size, restoreData_isFinal]
  split
  · data_norm <;> rfl
  · unfold kPend
    simp only [restoreData_pend, restoreData_size, restoreData_targetSize]
    split
    · split
      · data_norm <;> rfl
      · rename_i he
        simp only [hperm (Decidable.not_not.mp he), restoreNext]
    · rename_i hp
      rw [restoreData_urgentFrom cap old st t t NONE (Nat.le_trans hf.size_le hcap)]
      cases he : urgentFrom st t t NONE with
      | error r => rfl
      | ok u =>
        simp only [Except.mapError, kUE]
        data_norm <;> exact restoreData_kU cap old st t u hf hp ht hcap

theorem restoreData_loop (st : St) (t : Word) (hf : FInv st)
    (hcap : st.targetSize.toNat ≤ cap)
    (hperm : ∀ st : St, FInv st → st.size = st.targetSize → st.targetSize.toNat ≤ cap →
      permuteMapping (restoreData cap old st) =
        let r := permuteMapping st; (r.1, restoreData cap old r.2)) :
    loop (restoreData cap old st) t =
      let r := loop st t; (r.1, restoreData cap old r.2) := by
  by_cases ht : t < st.targetSize
  · have htr : t < (restoreData cap old st).targetSize := by
      simpa only [restoreData_targetSize] using ht
    rw [loop_lt htr, restoreData_body cap old st t hf ht hcap
      (fun hs => hperm st hf hs hcap), loop_lt ht]
    cases he : body st t with
    | ret r => rfl
    | cont st' t' =>
      have hf' := Unit.PlannerRunU.body_finv_cont hf ht he
      have hn := (body_cont he).1
      have hcap' : st'.targetSize.toNat ≤ cap := by rw [hn]; exact hcap
      change loop (restoreData cap old st') (t' + 1) =
        let r := loop st' (t' + 1); (r.1, restoreData cap old r.2)
      exact restoreData_loop st' (t' + 1) hf' hcap' hperm
  · have htr : ¬t < (restoreData cap old st).targetSize := by
      simpa only [restoreData_targetSize] using ht
    rw [loop_ge htr, loop_ge ht]
    simp only [restoreData_size, restoreData_targetSize]
    split <;> rfl
termination_by ((st.targetSize - t).toNat, st.pend.toNat)
decreasing_by
  obtain ⟨hn, h' | ⟨h', hp⟩⟩ := body_cont he
  · subst h'
    rw [hn]
    exact Prod.Lex.left _ _ (by bv_omega)
  · subst h'
    rw [hn, BitVec.sub_add_cancel]
    exact Prod.Lex.right _ hp

theorem restoreData_buildBottomUp (st : St) (hf : FInv st)
    (hcap : st.targetSize.toNat ≤ cap)
    (hperm : ∀ st : St, FInv st → st.size = st.targetSize → st.targetSize.toNat ≤ cap →
      permuteMapping (restoreData cap old st) =
        let r := permuteMapping st; (r.1, restoreData cap old r.2)) :
    buildBottomUp (restoreData cap old st) =
      let r := buildBottomUp st; (r.1, restoreData cap old r.2) :=
  restoreData_loop cap old st 0#64 hf hcap hperm

end
end FlatShuffler.Flat
