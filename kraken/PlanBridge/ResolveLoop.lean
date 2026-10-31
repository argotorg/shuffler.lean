import PlanBridge.Resolve

/-!
The loops of the flat `resolve` and of PR31 `Planner.resolve` (`resolve_corr`).

The candidates loop and the pick loop are pure folds, so `candidates_corr` and `pick_eq` give
equations. The pass loop can stop early or fail, so `pass_corr` gives a relation (`PassR`).
-/

open Shuffler Shuffler.Planner BbuBridge PlanBridge
open Bbu.Flat (get put optOf NONE isVariable spillIsSpilled spillAdd listEnv)

namespace PlanBridge

-- The flat candidates `cand` below `count` are the PR31 candidates `L`.
def CandR {s : Nat} (L : List (Fin s)) (cand : Vector Bbu.Word Bbu.MAX_N) (count : Bbu.Word) :
    Prop :=
  count.toNat = L.length ∧ ∀ i (h : i < L.length), get cand (.ofNat 64 i) = .ofNat 64 L[i].val

theorem ofNat_toNat (w : Bbu.Word) : BitVec.ofNat 64 w.toNat = w := by
  simp

theorem candR_snoc {s : Nat} {L : List (Fin s)} {cand : Vector Bbu.Word Bbu.MAX_N}
    {count : Bbu.Word} (h : CandR L cand count) (hl : L.length < Bbu.MAX_N) (x : Fin s) :
    CandR (L ++ [x]) (put cand count (.ofNat 64 x.val)) (count + 1) := by
  obtain ⟨hc, hg⟩ := h
  have hcn : count = .ofNat 64 L.length := by rw [← hc, ofNat_toNat]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hcn, Bbu.Flat.ofNat_succ, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold Bbu.MAX_N at hl; omega)]; simp
  · simp only [List.length_append, List.length_singleton] at hi
    rw [hcn, get_put _ hl (by omega)]
    by_cases hi' : i = L.length
    · subst hi'; simp
    · rw [ite_eq_right hi', hg i (by omega), List.getElem_append_left (by omega)]

-- The PR31 candidates step: the source position of the destination of `pos`.
def candStep {s t cs : Nat} (P : Mapping s t) (Pc : Mapping cs t) (acc : List (Fin s))
    (pos : Fin cs) : List (Fin s) :=
  acc ++ ((Pc pos).bind P.symm).toList

theorem candidates_corr {s t cs : Nat} (hs : s ≤ Bbu.MAX_N) (ht : t ≤ Bbu.MAX_N)
    {csW : Bbu.Word} (hcs : csW.toNat = cs) (hcsN : cs ≤ Bbu.MAX_N)
    {M : Bbu.Flat.Mapping} {P : Mapping s t} (hR : MapR M P)
    {C : Bbu.Flat.Mapping} {Pc : Mapping cs t} (hC : MapR C Pc) :
    ∀ j k (acc : List (Fin s)) cand count, k + j = cs → acc.length ≤ k → CandR acc cand count →
      (∀ x ∈ acc, (P x).isSome) →
      ∃ cand' count',
        Bbu.Flat.candidatesFrom M C csW (.ofNat 64 k) cand count = some (cand', count') ∧
        CandR (((List.finRange cs).drop k).foldl (candStep P Pc) acc) cand' count' ∧
        ∀ x ∈ ((List.finRange cs).drop k).foldl (candStep P Pc) acc, (P x).isSome := by
  intro j
  induction j with
  | zero =>
    intro k acc cand count hk _ hcr hret
    rw [List.drop_of_length_le (by simp; omega), List.foldl_nil]
    refine ⟨cand, count, ?_, hcr, hret⟩
    rw [Bbu.Flat.candidatesFrom, dite_eq_right (by rw [Bbu.Flat.ofNat_lt_iff (by omega)]; omega)]
  | succ j ih =>
    intro k acc cand count hk hl hcr hret
    rw [finRange_drop (by omega), List.foldl_cons, Bbu.Flat.candidatesFrom,
      dite_eq_left (by rw [Bbu.Flat.ofNat_lt_iff (by omega)]; omega), Bbu.Flat.ofNat_succ]
    simp only [candStep]
    have hdC := hC.dest ⟨k, by omega⟩
    cases hp : Pc ⟨k, by omega⟩ with
    | none =>
      rw [hp, Option.map_none, Bbu.Flat.optOf_eq_none] at hdC
      simp only [Option.bind_none, Option.toList_none, List.append_nil]
      rw [hdC, ite_eq_right (fun h => h.1 rfl)]
      exact ih (k + 1) acc cand count (by omega) (by omega) hcr hret
    | some d =>
      rw [hp, Option.map_some] at hdC
      have hdC' := optOf_eq_some hdC
      have hpM := hR.pos d
      simp only [Option.bind_some]
      rw [hdC']
      cases hq : P.symm d with
      | none =>
        rw [hq, Option.map_none, Bbu.Flat.optOf_eq_none] at hpM
        simp only [Option.toList_none, List.append_nil]
        rw [hpM, ite_eq_right (fun h => h.2 rfl)]
        exact ih (k + 1) acc cand count (by omega) (by omega) hcr hret
      | some x =>
        rw [hq, Option.map_some] at hpM
        have hpM' := optOf_eq_some hpM
        have hPx : P x = some d := (PEquiv.eq_some_iff P).mp hq
        have hdM := hR.dest x
        rw [hPx, Option.map_some] at hdM
        have hdM' := optOf_eq_some hdM
        have hne : ∀ {v : Nat}, v < Bbu.MAX_N → BitVec.ofNat 64 v ≠ NONE := fun hv =>
          Bbu.Flat.ne_none (by rw [Bbu.Flat.toNat_ofNat_lt hv]; exact hv)
        simp only [Option.toList_some]
        rw [hpM', ite_eq_left ⟨hne (by omega), hne (by omega)⟩, hdM',
          ite_eq_right (hne (by omega))]
        exact ih (k + 1) (acc ++ [x]) _ _ (by omega) (by simp; omega)
          (candR_snoc hcr (by omega) x) (by
            intro y hy
            rcases List.mem_append.mp hy with hy | hy
            · exact hret y hy
            · rw [List.mem_singleton.mp hy, hPx]; rfl)


end PlanBridge

namespace Bbu.Flat

-- One step of `pickFrom` at the candidate `offset`.
def pickStep (pl : Planner) (sp : BitVec 32 → BitVec 8) (M : Mapping)
    (dn : Vector (BitVec 8) MAX_N) (offset : Word) (w : Word × BitVec 8) : Word × BitVec 8 :=
  if get dn offset ≠ 0 then w
  else
    let cls := classify pl sp M dn offset
    if cls = NOCLASS then w
    else if w.1 = NONE || cls < w.2 || (cls == w.2 && get M.dest offset > get M.dest w.1) then
      (offset, cls)
    else w

theorem pickFrom_eq (pl : Planner) (sp : BitVec 32 → BitVec 8) (M : Mapping)
    (dn : Vector (BitVec 8) MAX_N) (cand : Vector Word MAX_N) (count i best : Word)
    (bestClass : BitVec 8) :
    pickFrom pl sp M dn cand count i best bestClass =
      if i < count then
        pickFrom pl sp M dn cand count (i + 1)
          (pickStep pl sp M dn (get cand i) (best, bestClass)).1
          (pickStep pl sp M dn (get cand i) (best, bestClass)).2
      else (best, bestClass) := by
  rw [pickFrom]
  by_cases h : i < count
  · rw [dite_eq_left h, ite_eq_left h]; simp only [pickStep]; split_ifs <;> rfl
  · rw [dite_eq_right h, ite_eq_right h]

end Bbu.Flat

namespace PlanBridge

def finOpt {s : Nat} (w : Bbu.Word) : Option (Fin s) :=
  if h : w.toNat < s then some ⟨w.toNat, h⟩ else none

-- The PR31 `best` and `bestClass` of the flat ones.
def absPick {s : Nat} (w : Bbu.Word × BitVec 8) : Option (Fin s) × Nat := (finOpt w.1, w.2.toNat)

-- The flat `best` is `NONE` or a retained offset.
def PInv {s t : Nat} (P : Mapping s t) (w : Bbu.Word × BitVec 8) : Prop :=
  w.1 = NONE ∨ ∃ x : Fin s, w.1 = .ofNat 64 x.val ∧ (P x).isSome

theorem pick_eq {ε : Type} {s t : Nat} {P : Mapping s t} {L : List (Fin s)}
    {cand : Vector Bbu.Word Bbu.MAX_N} {count : Bbu.Word} (hcr : CandR L cand count)
    (hL : L.length ≤ Bbu.MAX_N)
    (g : Bbu.Word → Bbu.Word × BitVec 8 → Bbu.Word × BitVec 8)
    (f : Fin s → Option (Fin s) × Nat → Except ε (ForInStep (Option (Fin s) × Nat)))
    (hstep : ∀ x ∈ L, ∀ w, PInv P w →
      f x (absPick w) = pure (.yield (absPick (g (.ofNat 64 x.val) w))))
    (hinv : ∀ x ∈ L, ∀ w, PInv P w → PInv P (g (.ofNat 64 x.val) w))
    (F : Bbu.Word → Bbu.Word × BitVec 8 → Bbu.Word × BitVec 8)
    (hF : ∀ i w, F i w = if i < count then F (i + 1) (g (get cand i) w) else w)
    (w : Bbu.Word × BitVec 8) (hw : PInv P w) :
    forIn L (absPick w) f = pure (absPick (F 0 w)) ∧ PInv P (F 0 w) := by
  suffices h : ∀ j i w, i + j = L.length → PInv P w →
      forIn (L.drop i) (absPick w) f = pure (absPick (F (.ofNat 64 i) w)) ∧
        PInv P (F (.ofNat 64 i) w) by
    simpa using h L.length 0 w (by omega) hw
  intro j
  induction j with
  | zero =>
    intro i w hi hw
    have hc := hcr.1
    rw [hF, ite_eq_right (by rw [Bbu.Flat.ofNat_lt_iff (by omega)]; omega),
      List.drop_of_length_le (by omega)]
    exact ⟨rfl, hw⟩
  | succ j ih =>
    intro i w hi hw
    have hc := hcr.1
    have hx : L[i] ∈ L := List.getElem_mem _
    rw [hF, ite_eq_left (by rw [Bbu.Flat.ofNat_lt_iff (by omega)]; omega),
      List.drop_eq_getElem_cons (by omega), List.forIn_cons, hcr.2 i (by omega), hstep _ hx w hw,
      Bbu.Flat.ofNat_succ]
    exact ih (i + 1) _ (by omega) (hinv _ hx w hw)

theorem pick_inv {s t : Nat} {P : Mapping s t} {L : List (Fin s)}
    {cand : Vector Bbu.Word Bbu.MAX_N} {count : Bbu.Word} (hcr : CandR L cand count)
    (hL : L.length ≤ Bbu.MAX_N)
    (g : Bbu.Word → Bbu.Word × BitVec 8 → Bbu.Word × BitVec 8)
    (hinv : ∀ x ∈ L, ∀ w, PInv P w → PInv P (g (.ofNat 64 x.val) w))
    (F : Bbu.Word → Bbu.Word × BitVec 8 → Bbu.Word × BitVec 8)
    (hF : ∀ i w, F i w = if i < count then F (i + 1) (g (get cand i) w) else w)
    (w : Bbu.Word × BitVec 8) (hw : PInv P w) : PInv P (F 0 w) := by
  suffices h : ∀ j i w, i + j = L.length → PInv P w → PInv P (F (.ofNat 64 i) w) by
    simpa using h L.length 0 w (by omega) hw
  intro j
  induction j with
  | zero =>
    intro i w hi hw
    have hc := hcr.1
    rw [hF, ite_eq_right (by rw [Bbu.Flat.ofNat_lt_iff (by omega)]; omega)]
    exact hw
  | succ j ih =>
    intro i w hi hw
    have hc := hcr.1
    have hx : L[i] ∈ L := List.getElem_mem _
    rw [hF, ite_eq_left (by rw [Bbu.Flat.ofNat_lt_iff (by omega)]; omega), hcr.2 i (by omega),
      Bbu.Flat.ofNat_succ]
    exact ih (i + 1) _ (by omega) (hinv _ hx w hw)

end PlanBridge

namespace Bbu.Flat

-- One pass of `passFrom`: the resolution if it stops there, and the state.
def passStep (pl : Planner) (M : Mapping) (cand : Vector Word MAX_N) (count : Word) (s : RState) :
    Option Resolution × RState :=
  let r := pickFrom pl s.spills M s.droppedNow cand count 0 NONE 0
  if r.1 = NONE then (some .stuck, s)
  else
    let a := spillAdd s.spills (get pl.source r.1)
    if r.2 = SPILL ∧ a.1 ≠ .done then (some .assertionFailed, s)
    else (none, ⟨if r.2 = SPILL then a.2 else s.spills, put s.dropped r.1 1, put s.droppedNow r.1 1⟩)

theorem passFrom_eq (pl : Planner) (M : Mapping) (cand : Vector Word MAX_N)
    (count excess k : Word) (s : RState) :
    passFrom pl M cand count excess k s =
      if k < excess then
        match passStep pl M cand count s with
        | (some res, s') => (res, s')
        | (none, s') => passFrom pl M cand count excess (k + 1) s'
      else (.dropped, s) := by
  rw [passFrom]
  by_cases h : k < excess
  · rw [dite_eq_left h, ite_eq_left h]; simp only [passStep]; split_ifs <;> rfl
  · rw [dite_eq_right h, ite_eq_right h]

end Bbu.Flat

namespace PlanBridge

open Bbu.Flat (Resolution RState)

-- A flat pass and a PR31 pass: both go on with related states, both stop with related states,
-- or both fail.
def PStepR {σ D ε : Type} (SR : (BitVec 32 → BitVec 8) → Vector (BitVec 8) Bbu.MAX_N → σ → Prop)
    (DR : Vector (BitVec 8) Bbu.MAX_N → D → Prop) :
    Option Resolution × RState → Except ε (ForInStep (Option (Bool × σ) × σ × D)) → Prop
  | (none, rs), .ok (.yield b) => b.1 = none ∧ SR rs.spills rs.dropped b.2.1 ∧ DR rs.droppedNow b.2.2
  | (some .stuck, rs), .ok (.done b) => b.1 = some (false, b.2.1) ∧ SR rs.spills rs.dropped b.2.1
  | (some .assertionFailed, _), .error _ => True
  | _, _ => False

-- The flat passes and the PR31 loop.
def PassR {σ D ε : Type} (SR : (BitVec 32 → BitVec 8) → Vector (BitVec 8) Bbu.MAX_N → σ → Prop) :
    Resolution × RState → Except ε (Option (Bool × σ) × σ × D) → Prop
  | (.dropped, rs), .ok b => b.1 = none ∧ SR rs.spills rs.dropped b.2.1
  | (.stuck, rs), .ok b => b.1 = some (false, b.2.1) ∧ SR rs.spills rs.dropped b.2.1
  | (.assertionFailed, _), .error _ => True
  | _, _ => False

-- The flat `resolve` and the PR31 `resolve`.
def RslvR {σ ε : Type} (SR : (BitVec 32 → BitVec 8) → Vector (BitVec 8) Bbu.MAX_N → σ → Prop) :
    Resolution × (BitVec 32 → BitVec 8) × Vector (BitVec 8) Bbu.MAX_N → Except ε (Bool × σ) → Prop
  | (.dropped, sp, d), .ok (b, st) => b = true ∧ SR sp d st
  | (.stuck, sp, d), .ok (b, st) => b = false ∧ SR sp d st
  | (.assertionFailed, _), .error _ => True
  | _, _ => False

theorem pass_corr {σ D ε : Type} {e : Nat}
    (SR : (BitVec 32 → BitVec 8) → Vector (BitVec 8) Bbu.MAX_N → σ → Prop)
    (DR : Vector (BitVec 8) Bbu.MAX_N → D → Prop)
    (step : RState → Option Resolution × RState)
    (f : Fin e → Option (Bool × σ) × σ × D → Except ε (ForInStep (Option (Bool × σ) × σ × D)))
    (hstep : ∀ k (hk : k < e) rs b, b.1 = none → SR rs.spills rs.dropped b.2.1 →
      DR rs.droppedNow b.2.2 → PStepR SR DR (step rs) (f ⟨k, hk⟩ b))
    (F : Bbu.Word → RState → Resolution × RState)
    (hF : ∀ k rs, k ≤ e → F (.ofNat 64 k) rs =
      if k < e then
        match step rs with
        | (some res, s') => (res, s')
        | (none, s') => F (.ofNat 64 (k + 1)) s'
      else (.dropped, rs))
    (rs : RState) (b : Option (Bool × σ) × σ × D) (h1 : b.1 = none)
    (h2 : SR rs.spills rs.dropped b.2.1) (h3 : DR rs.droppedNow b.2.2) :
    PassR SR (F 0 rs) (forIn (List.finRange e) b f) := by
  suffices h : ∀ j k rs b, k + j = e → b.1 = none → SR rs.spills rs.dropped b.2.1 →
      DR rs.droppedNow b.2.2 → PassR SR (F (.ofNat 64 k) rs) (forIn ((List.finRange e).drop k) b f) by
    simpa using h e 0 rs b (by omega) h1 h2 h3
  intro j
  induction j with
  | zero =>
    intro k rs b hk h1 h2 _
    rw [hF k rs (by omega), ite_eq_right (by omega), List.drop_of_length_le (by simp; omega)]
    obtain ⟨b1, b2, b3⟩ := b
    exact ⟨h1, h2⟩
  | succ j ih =>
    intro k rs b hk h1 h2 h3
    rw [hF k rs (by omega), ite_eq_left (by omega), finRange_drop (by omega), List.forIn_cons]
    have hs := hstep k (by omega) rs b h1 h2 h3
    revert hs
    generalize step rs = r
    generalize f ⟨k, by omega⟩ b = x
    rcases r with ⟨_ | (_ | _ | _), rs'⟩ <;> rcases x with _ | (b' | b') <;>
      simp only [PStepR, PassR, false_imp_iff, Bind.bind, Except.bind, pure, Except.pure]
    · exact fun ⟨h1, h2, h3⟩ => ih (k + 1) rs' b' (by omega) h1 h2 h3
    · exact id
    · exact id


theorem forIn_yield_eq {α β ε : Type} (l : List α) (b : β) (f : α → β → Except ε (ForInStep β))
    (h : β → α → β) (hf : ∀ a b, f a b = pure (.yield (h b a))) :
    forIn l b f = pure (l.foldl h b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, hf, List.foldl_cons, ← ih]; rfl

theorem rslv_of_pass {σ D ε : Type}
    {SR : (BitVec 32 → BitVec 8) → Vector (BitVec 8) Bbu.MAX_N → σ → Prop}
    {r : Resolution × RState} {x : Except ε (Option (Bool × σ) × σ × D)} (h : PassR SR r x)
    (K : Option (Bool × σ) × σ × D → Except ε (Bool × σ))
    (hK1 : ∀ c st d, K (some c, st, d) = pure c) (hK2 : ∀ st d, K (none, st, d) = pure (true, st)) :
    RslvR SR (r.1, r.2.spills, r.2.dropped) (x >>= K) := by
  rcases r with ⟨_ | _ | _, rs⟩ <;> rcases x with _ | ⟨_ | c, st, d⟩ <;>
    simp only [PassR, reduceCtorEq, false_and, Option.some.injEq] at h
  · rw [except_ok_bind, hK2]; exact ⟨rfl, h.2⟩
  · rw [except_ok_bind, hK1, h.1]; exact ⟨rfl, h.2⟩
  · trivial

theorem zeroFrom_get (m : Bbu.Word) (hm : m.toNat ≤ Bbu.MAX_N) :
    ∀ j k (dn : Vector (BitVec 8) Bbu.MAX_N), k + j = m.toNat → ∀ i, i < m.toNat →
      (i < k → get dn (.ofNat 64 i) = 0) →
      get (Bbu.Flat.zeroFrom m (.ofNat 64 k) dn) (.ofNat 64 i) = 0 := by
  intro j
  induction j with
  | zero =>
    intro k dn hk i hi h
    rw [Bbu.Flat.zeroFrom, dite_eq_right (by rw [Bbu.Flat.ofNat_lt_iff (by omega)]; omega)]
    exact h (by omega)
  | succ j ih =>
    intro k dn hk i hi h
    rw [Bbu.Flat.zeroFrom, dite_eq_left (by rw [Bbu.Flat.ofNat_lt_iff (by omega)]; omega),
      Bbu.Flat.ofNat_succ]
    refine ih (k + 1) _ (by omega) i hi (fun hik => ?_)
    rw [get_put _ (by omega) (by omega)]
    by_cases hik' : i = k
    · rw [ite_eq_left hik']
    · rw [ite_eq_right hik']; exact h (by omega)

theorem ofNat_lt_toNat {k : Nat} {w : Bbu.Word} (hk : k ≤ w.toNat) :
    BitVec.ofNat 64 k < w ↔ k < w.toNat := by
  have := w.isLt
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem foldl_candStep_length {s t cs : Nat} (P : Mapping s t) (Pc : Mapping cs t)
    (l : List (Fin cs)) : ∀ acc, (l.foldl (candStep P Pc) acc).length ≤ acc.length + l.length := by
  induction l with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons]
    have := ih (candStep P Pc acc a)
    have h1 : (candStep P Pc acc a).length ≤ acc.length + 1 := by
      unfold candStep; rw [List.length_append]; cases (Pc a).bind P.symm <;> simp
    simp only [List.length_cons]; omega

theorem finOpt_none {s : Nat} (hs : s ≤ Bbu.MAX_N) : finOpt (s := s) NONE = none := by
  unfold finOpt
  rw [dite_eq_right (by unfold NONE Bbu.MAX_N at *; simp; omega)]

theorem finOpt_ofNat {s : Nat} (hs : s ≤ Bbu.MAX_N) (y : Fin s) :
    finOpt (s := s) (.ofNat 64 y.val) = some y := by
  unfold finOpt
  have : (BitVec.ofNat 64 y.val).toNat = y.val := Bbu.Flat.toNat_ofNat_lt (by omega)
  rw [dite_eq_left (by omega)]
  simp only [this]

theorem dnR_set {k : Nat} (hk : k ≤ Bbu.MAX_N) {dn : Vector Byte k}
    {fdn : Vector (BitVec 8) Bbu.MAX_N} (h : DnR dn fdn) (y : Nat) (hy : y < k) :
    DnR (dn.set y 1 hy) (put fdn (.ofNat 64 y) 1) := by
  intro i
  rw [Fin.getElem_fin, Vector.getElem_set, get_put _ (by omega) (by omega)]
  by_cases hi : i.val = y
  · rw [ite_eq_left hi.symm, ite_eq_left hi]; rfl
  · rw [ite_eq_right (Ne.symm hi), ite_eq_right hi, ← Fin.getElem_fin, h i]

section
variable {pl : Bbu.Flat.Planner}

-- The PR31 planner state and the flat spill bytes `sp` and dropped bytes `d`.
def SRpl (pl : Bbu.Flat.Planner) (sp : BitVec 32 → BitVec 8) (d : Vector (BitVec 8) Bbu.MAX_N)
    (st : State (srcOf pl.source pl.m) (srcOf pl.target pl.n)) : Prop :=
  st.spills = pSpills (pl.source.toList.take pl.m.toNat) pl.n.toNat pl.target sp ∧
    st.spillingAllowed = pl.allowed ∧ DnR st.dropped d

theorem dnR_replicate (hm : pl.m.toNat ≤ Bbu.MAX_N) (dn : Vector (BitVec 8) Bbu.MAX_N) :
    DnR (Vector.replicate (srcOf pl.source pl.m).length (0 : Byte))
      (Bbu.Flat.zeroFrom pl.m 0 dn) := by
  intro i
  have hi := src_lt hm i
  rw [Fin.getElem_fin, Vector.getElem_replicate, show (0 : Bbu.Word) = .ofNat 64 0 from rfl,
    zeroFrom_get pl.m hm pl.m.toNat 0 dn (by omega) i hi (fun h => absurd h (by omega))]
  rfl

theorem resolve_corr (hm : pl.m.toNat ≤ Bbu.MAX_N) (hn : pl.n.toNat ≤ Bbu.MAX_N)
    (ok : SlotsOk (pl.source.toList.take pl.m.toNat ++ pl.target.toList.take pl.n.toNat))
    {init : State (srcOf pl.source pl.m) (srcOf pl.target pl.n)} {sp : BitVec 32 → BitVec 8}
    {dropped : Vector (BitVec 8) Bbu.MAX_N} (hinit : SRpl pl sp dropped init)
    {P : Mapping (srcOf pl.source pl.m).length (srcOf pl.target pl.n).length}
    {M : Bbu.Flat.Mapping} (hR : MapR M P)
    {cs : Nat} {current : Mapping cs (srcOf pl.target pl.n).length} {C : Bbu.Flat.Mapping}
    (hC : MapR C current) {csW : Bbu.Word} (hcs : csW.toNat = cs) (hcsN : cs ≤ Bbu.MAX_N)
    {blocked : Blocked} (hbl : blocked.offset < cs) {boW exW : Bbu.Word}
    (hbo : boW.toNat = blocked.offset) (hex : exW.toNat = blocked.excess)
    (u : Bbu.Flat.ResolveU) :
    RslvR (SRpl pl) (Bbu.Flat.resolve pl sp dropped M boW exW C csW u)
      (resolve init P blocked current) := by
  have hsl := srcOf_length (v := pl.source) hm
  have htl := srcOf_length (v := pl.target) hn
  unfold resolve Bbu.Flat.resolve
  dsimp only
  have hb1 : boW + 1 = BitVec.ofNat 64 (blocked.offset + 1) := by
    rw [← Bbu.Flat.ofNat_succ, ← hbo, ofNat_toNat]
  rw [hb1, forIn_yield_eq _ _ _ (candStep P current) (fun pos acc => by
    unfold Mapping.destinationOf Mapping.positionOf candStep
    rcases current pos with _ | d
    · simp
    · simp only [Option.bind_some]
      split
      · rename_i x hx; simp [hx]
      · rename_i hx
        rw [show P.symm d = none from Option.eq_none_iff_forall_ne_some.mpr (fun x h => hx x h)]
        simp)]
  obtain ⟨cand, count, hcf, hcr, hret⟩ := candidates_corr (by rw [hsl]; exact hm)
    (by rw [htl]; exact hn) hcs hcsN hR hC (cs - (blocked.offset + 1)) (blocked.offset + 1) []
    u.candidates 0 (by omega) (by simp) ⟨rfl, fun i h => absurd h (by simp)⟩ (by simp)
  rw [hcf]
  dsimp only
  rw [pure_bind, show (∅ : List (Fin (srcOf pl.source pl.m).length)) = [] from rfl]
  have hLn := foldl_candStep_length P current (List.drop (blocked.offset + 1) (List.finRange cs)) []
  simp only [List.length_nil, List.length_drop, List.length_finRange] at hLn
  generalize List.foldl (candStep P current) [] (List.drop (blocked.offset + 1) (List.finRange cs))
    = L at hcr hret hLn ⊢
  refine rslv_of_pass ?_ _ (fun _ _ _ => rfl) (fun _ _ => rfl)
  refine pass_corr (SRpl pl) (fun fdn dn => DnR dn fdn) (Bbu.Flat.passStep pl M cand count) _ ?_
    (Bbu.Flat.passFrom pl M cand count exW) ?_ _ _ rfl hinit (dnR_replicate hm _)
  · intro k hk rs ⟨b1, st, dn⟩ hb1 hsr hdn
    simp only at hb1 hsr hdn
    subst hb1
    dsimp only
    have hs : (srcOf pl.source pl.m).length ≤ Bbu.MAX_N := by rw [hsl]; exact hm
    have hinv : ∀ x ∈ L, ∀ w, PInv P w →
        PInv P (Bbu.Flat.pickStep pl rs.spills M rs.droppedNow (.ofNat 64 x.val) w) := by
      intro x hx w hw
      unfold Bbu.Flat.pickStep
      dsimp only
      split_ifs
      all_goals first | exact hw | exact .inr ⟨x, rfl, hret x hx⟩
    have hpi := pick_inv hcr (by omega) _ hinv
      (fun i w => Bbu.Flat.pickFrom pl rs.spills M rs.droppedNow cand count i w.1 w.2)
      (fun i w => Bbu.Flat.pickFrom_eq _ _ _ _ _ _ _ _ _) (NONE, 0) (.inl rfl)
    rw [show ((none, 0) : Option (Fin (srcOf pl.source pl.m).length) × Nat) =
        absPick (NONE, (0 : BitVec 8)) by simp only [absPick, finOpt_none hs]; rfl]
    rw [(pick_eq hcr (by omega) (Bbu.Flat.pickStep pl rs.spills M rs.droppedNow) _ ?hst hinv
      (fun i w => Bbu.Flat.pickFrom pl rs.spills M rs.droppedNow cand count i w.1 w.2)
      (fun i w => Bbu.Flat.pickFrom_eq _ _ _ _ _ _ _ _ _) (NONE, 0) (.inl rfl)).1]
    case hst =>
      intro x hx w hw
      have hPx := hret x hx
      by_cases hd0 : get rs.droppedNow (BitVec.ofNat 64 x.val) = 0
      · rw [ite_eq_right (not_not.mpr ((DnR.zero hdn x).mpr hd0)),
          classify_corr hm hn ok hsr.1 hsr.2.1 hR hdn x hPx, except_ok_bind]
        unfold Bbu.Flat.pickStep
        rw [ite_eq_right (not_not.mpr hd0)]
        dsimp only
        generalize Bbu.Flat.classify pl rs.spills M rs.droppedNow (BitVec.ofNat 64 x.val) = c
        by_cases hcn : c = Bbu.Flat.NOCLASS
        · rw [clsOf, ite_eq_left hcn, ite_eq_left hcn, ite_eq_left (by simp)]
        · rw [clsOf, ite_eq_right hcn, ite_eq_right hcn]
          rw [ite_eq_right (by simp), requires_of_true _ (by rfl), except_ok_bind,
            requires_of_true _ (by exact hPx), except_ok_bind]
          obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hPx
          have hdg : ∀ h', (P.destinationOf x).get h' = dx := by
            intro h'; simp only [Mapping.destinationOf, hdx, Option.get_some]
          simp only [hdg, Option.get_some]
          have hdM := hR.dest x
          rw [hdx, Option.map_some] at hdM
          rw [optOf_eq_some hdM]
          have ht : (srcOf pl.target pl.n).length ≤ Bbu.MAX_N := by rw [htl]; exact hn
          have hxN := x.isLt
          have hdxN := dx.isLt
          rcases hw with hw | ⟨y, hy, hPy⟩
          · obtain ⟨w1, w2⟩ := w
            simp only at hw
            subst hw
            simp [absPick, finOpt_none hs, finOpt_ofNat hs]
          · obtain ⟨w1, w2⟩ := w
            simp only at hy
            subst hy
            obtain ⟨dy, hdy⟩ := Option.isSome_iff_exists.mp hPy
            have hdN := hR.dest y
            rw [hdy, Option.map_some] at hdN
            have hdyN := dy.isLt
            have hyN := y.isLt
            have hcmp : BitVec.ofNat 64 dy.val < BitVec.ofNat 64 dx.val ↔ dy < dx := by
              rw [Bbu.Flat.ofNat_lt_iff (by omega), Bbu.Flat.toNat_ofNat_lt (by omega), Fin.lt_def]
            have hne : BitVec.ofNat 64 y.val ≠ NONE :=
              Bbu.Flat.ne_none (by rw [Bbu.Flat.toNat_ofNat_lt (by omega)]; omega)
            simp [absPick, finOpt_ofNat hs, optOf_eq_some hdN, hdy, hne, hcmp, BitVec.lt_def,
              Mapping.destinationOf]
            simp only [BitVec.toNat_inj]
            split_ifs <;> simp [finOpt_ofNat hs]
      · rw [ite_eq_left (fun h => hd0 ((DnR.zero hdn x).mp h))]
        unfold Bbu.Flat.pickStep
        rw [ite_eq_left hd0]
    dsimp only at hpi ⊢
    unfold Bbu.Flat.passStep
    dsimp only
    generalize Bbu.Flat.pickFrom pl rs.spills M rs.droppedNow cand count 0 NONE 0 = r at hpi ⊢
    rw [pure_bind]
    have hsS := hsl ▸ hm
    rcases hpi with hr | ⟨y, hy, hPy⟩
    · obtain ⟨r1, r2⟩ := r
      simp only at hr
      subst hr
      rw [ite_eq_left rfl]
      simp only [absPick, finOpt_none hs, Option.isSome_none, Bool.false_eq_true,
        not_false_eq_true, ↓reduceIte]
      exact ⟨rfl, hsr⟩
    · obtain ⟨r1, r2⟩ := r
      simp only at hy
      subst hy
      have hy := src_lt hm y
      rw [ite_eq_right (Bbu.Flat.ne_none (by rw [Bbu.Flat.toNat_ofNat_lt (by omega)]; omega))]
      have hab : (absPick (s := (srcOf pl.source pl.m).length) (BitVec.ofNat 64 y.val, r2)).1 =
          some y := by simp only [absPick, finOpt_ofNat hs]
      have hg : ∀ h', (absPick (s := (srcOf pl.source pl.m).length)
          (BitVec.ofNat 64 y.val, r2)).1.get h' = y := by intro h'; simp only [hab, Option.get_some]
      have h2 : (absPick (s := (srcOf pl.source pl.m).length) (BitVec.ofNat 64 y.val, r2)).2 =
          r2.toNat := rfl
      conv => arg 4; rw [ite_eq_right (by rw [hab]; simp), requires_of_true _ (by rw [hab]; rfl),
        except_ok_bind]
      simp only [hg, h2]
      have hxS := get_mem_take pl.source hm hy
      by_cases hsp : r2 = Bbu.Flat.SPILL
      · have h4 : r2.toNat = 4 := by rw [hsp]; rfl
        conv => arg 4; rw [ite_eq_left h4, src_get, hsr.1]
        have hac := add_corr ok rs.spills hxS
        revert hac
        generalize spillAdd rs.spills (get pl.source (BitVec.ofNat 64 y.val)) = A
        generalize (pSpills (pl.source.toList.take pl.m.toNat) pl.n.toNat pl.target rs.spills).add
          (decode (get pl.source (BitVec.ofNat 64 y.val))) = B
        intro hac
        rcases A with ⟨a, sp'⟩
        cases a <;> cases B <;> simp only [SpCorr] at hac
        · rw [ite_eq_right (fun h => h.2 rfl), ite_eq_left hsp, except_ok_bind]
          exact ⟨rfl, ⟨hac, hsr.2.1, dnR_set hs hsr.2.2 y y.isLt⟩, dnR_set hs hdn y y.isLt⟩
        · rw [ite_eq_left ⟨hsp, by simp⟩]
          trivial
      · have h4 : r2.toNat ≠ 4 := fun h => hsp (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        conv => arg 4; rw [ite_eq_right h4]
        rw [ite_eq_right (fun h => hsp h.1), ite_eq_right hsp]
        exact ⟨rfl, ⟨hsr.1, hsr.2.1, dnR_set hs hsr.2.2 y y.isLt⟩, dnR_set hs hdn y y.isLt⟩
  · intro k rs hk
    rw [Bbu.Flat.passFrom_eq, Bbu.Flat.ofNat_succ]
    by_cases hk' : k < blocked.excess
    · rw [ite_eq_left ((ofNat_lt_toNat (by omega)).mpr (by omega)), ite_eq_left hk']
    · rw [ite_eq_right (fun h => hk' (by rw [← hex]; exact (ofNat_lt_toNat (by omega)).mp h)),
        ite_eq_right hk']

end

end PlanBridge
