import Shuffler.BuildBottomUp.Optimality.Lemmas.TightLowerBound

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

--- Lifted states ---------------------------------------------------------------------------------

-- Positions below b map to themselves. Position b + i maps to b + (m i).
def liftMap (b : ℕ) (m : Mapping n t) (hn : n' = b + n) (ht : t' = b + t) : Mapping n' t' where
  toFun i := if h : i.val < b then some ⟨i.val, by omega⟩
    else (m ⟨i.val - b, by omega⟩).map fun j => ⟨b + j.val, by omega⟩
  invFun j := if h : j.val < b then some ⟨j.val, by omega⟩
    else (m.symm ⟨j.val - b, by omega⟩).map fun i => ⟨b + i.val, by omega⟩
  inv i j := by
    refine Iff.symm ?_
    by_cases hi : i.val < b <;> by_cases hj : j.val < b <;>
      simp only [hi, hj, ↓reduceDIte, Option.some.injEq, Fin.ext_iff,
        Option.map_eq_some_iff]
    · exact eq_comm
    · exact ⟨fun h => by omega, fun ⟨_, _, h⟩ => by omega⟩
    · exact ⟨fun ⟨_, _, h⟩ => by omega, fun h => by omega⟩
    · constructor
      · rintro ⟨a, ha, hab⟩
        refine ⟨⟨i.val - b, by omega⟩, ?_, ?_⟩
        · rw [PEquiv.eq_some_iff, ha]
          exact congrArg some (Fin.ext (by simp; omega))
        · simp; omega
      · rintro ⟨a, ha, hab⟩
        refine ⟨⟨j.val - b, by omega⟩, ?_, ?_⟩
        · rw [← PEquiv.eq_some_iff, ha]
          exact congrArg some (Fin.ext (by simp; omega))
        · simp; omega

theorem swap_append_add (pre xs : Stack) (i j : ℕ) :
    (pre ++ xs).swap (pre.length + i) (pre.length + j) = pre ++ xs.swap i j := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    rw [List.length_cons, show pre.length + 1 + i = (pre.length + i) + 1 by omega,
      show pre.length + 1 + j = (pre.length + j) + 1 by omega, List.cons_append,
      List.swap_cons, ih, List.cons_append]

theorem liftSwap_eq (pre prev : Stack) (h : idx < prev.length) :
    (pre ++ prev).swap ((pre ++ prev).length - 1) ((pre ++ prev).length - 1 - idx) =
      pre ++ prev.swap (prev.length - 1) (prev.length - 1 - idx) := by
  rw [List.length_append, show pre.length + prev.length - 1 = pre.length + (prev.length - 1) by
    omega, show pre.length + (prev.length - 1) - idx = pre.length + (prev.length - 1 - idx) by
    omega, swap_append_add]

theorem liftDup_eq (pre prev : Stack) (h : idx ≤ prev.length) (hlo : 1 ≤ idx) :
    (pre ++ prev) ++ [(pre ++ prev)[(pre ++ prev).length - idx]'(by simp; omega)] =
      pre ++ (prev ++ [prev[prev.length - idx]'(by omega)]) := by
  rw [List.append_assoc]
  congr 3
  rw [List.getElem_append_right (by simp; omega)]
  congr 1
  simp; omega

theorem liftPop_eq (pre prev : Stack) (h : 0 < prev.length) :
    (pre ++ prev).dropLast = pre ++ prev.dropLast := by
  rw [List.dropLast_append_of_ne_nil (List.ne_nil_of_length_pos h)]

-- The same operations on a stack with `pre` below it.
def liftTrace (pre : Stack) : {first current : Stack} →
    Trace spills first current → Trace spills (pre ++ first) (pre ++ current)
  | _, _, .Lit s => .Lit (pre ++ s)
  | _, _, .Swap (prev := prev) idx hlen hlo hhi t =>
    liftSwap_eq pre prev hlen ▸ .Swap idx (by simp; omega) hlo hhi (liftTrace pre t)
  | _, _, .Dup (prev := prev) idx hlen hlo hhi t =>
    liftDup_eq pre prev hlen hlo ▸ .Dup idx (by simp; omega) hlo hhi (liftTrace pre t)
  | _, _, .Pop (prev := prev) hlen t =>
    liftPop_eq pre prev hlen ▸ .Pop (by simp; omega) (liftTrace pre t)
  | _, _, .Push (prev := prev) v hfree t => List.append_assoc pre prev [v] ▸ .Push v hfree (liftTrace pre t)
  | _, _, .Load (prev := prev) id hs t => List.append_assoc pre prev [.Var id] ▸ .Load id hs (liftTrace pre t)

-- `pre` sits below the stack and below the target, each slot at its own destination.
def liftState (pre : Stack) (s : State source target spills) :
    State (pre ++ source) (pre ++ target) spills where
  planned_mapping := liftMap pre.length s.planned_mapping (by simp) (by simp)
  stack := pre ++ s.stack
  trace := liftTrace pre s.trace
  mapping := liftMap pre.length s.mapping (by simp) (by simp)
  pending_generations := s.pending_generations

--- Static facts ----------------------------------------------------------------------------------

theorem liftMap_symm_apply (b : ℕ) (m : Mapping n t) (hn : n' = b + n) (ht : t' = b + t)
    (j : Fin t') :
    (liftMap b m hn ht).symm j = if h : j.val < b then some ⟨j.val, by omega⟩
      else (m.symm ⟨j.val - b, by omega⟩).map fun i => ⟨b + i.val, by omega⟩ := rfl

theorem unmapped_liftMap (b : ℕ) (m : Mapping n t) (hn : n' = b + n) (ht : t' = b + t) :
    (liftMap b m hn ht).unmapped_target_slots = m.unmapped_target_slots := by
  subst hn ht
  simp only [Mapping.unmapped_target_slots, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp [liftMap_symm_apply]

theorem swapCount_cast {current current' : Stack} (h : current = current')
    (t : Trace spills first current) : (h ▸ t).swapCount = t.swapCount := by
  subst h
  rfl

theorem swapCount_liftTrace (pre : Stack) (t : Trace spills first current) :
    (liftTrace pre t).swapCount = t.swapCount := by
  induction t with
  | Lit => simp [liftTrace, Trace.swapCount]
  | Swap idx hlen hlo hhi t ih =>
    simp only [liftTrace, swapCount_cast, Trace.swapCount, ih]
  | Dup idx hlen hlo hhi t ih =>
    simp only [liftTrace, swapCount_cast, Trace.swapCount, ih]
  | Pop hlen t ih =>
    simp only [liftTrace, swapCount_cast, Trace.swapCount, ih]
  | Push v hfree t ih =>
    simp only [liftTrace, swapCount_cast, Trace.swapCount, ih]
  | Load id hs t ih =>
    simp only [liftTrace, swapCount_cast, Trace.swapCount, ih]

theorem liftState_valid (pre : Stack) (s : State source target spills) (h : s.Valid) :
    (liftState pre s).Valid where
  size := by
    have := h.size
    simp [liftState]
    omega
  pending := (unmapped_liftMap _ _ (by simp [liftState]) (by simp)).trans h.pending
  available i := by
    simp only [State.isAvailable, Stack.shallowestCopyPosition_isSome, liftState, Fin.getElem_fin]
    by_cases hi : i.val < pre.length
    · right; right
      rw [List.getElem_append_left hi]
      exact List.mem_append_left _ (List.getElem_mem hi)
    · have ha := h.available ⟨i.val - pre.length, by have := i.isLt; simp at this; omega⟩
      simp only [State.isAvailable, Stack.shallowestCopyPosition_isSome] at ha
      rw [List.getElem_append_right (by omega)]
      exact ha.imp_right fun h => h.imp_right fun h => List.mem_append_right _ h


--- Simulation ------------------------------------------------------------------------------------

-- `x` succeeds with a related value whenever `y` succeeds.
def Sim (R : α → β → Prop) (x : Except Error α) (y : Except Error β) : Prop :=
  ∀ b, y = .ok b → ∃ a, x = .ok a ∧ R a b

theorem Sim.ok {R : α → β → Prop} (h : R a b) : Sim R (.ok a) (.ok b) := by
  rintro _ ⟨⟩
  exact ⟨a, rfl, h⟩

theorem Sim.error {R : α → β → Prop} (x : Except Error α) (e : Error) : Sim R x (.error e) := by
  rintro _ ⟨⟩

theorem Sim.bind {R : α → β → Prop} {R' : γ → δ → Prop} {x : Except Error α} {y : Except Error β}
    {f : α → Except Error γ} {g : β → Except Error δ} (h : Sim R x y)
    (step : ∀ a b, R a b → Sim R' (f a) (g b)) : Sim R' (x >>= f) (y >>= g) := by
  intro d hd
  cases hy : y with
  | error e => simp [hy, except_error_bind] at hd
  | ok b =>
    obtain ⟨a, hx, hab⟩ := h b hy
    rw [hy, except_ok_bind] at hd
    rw [hx, except_ok_bind]
    exact step a b hab d hd

theorem Sim.ite {R : α → β → Prop} {p q : Prop} [Decidable p] [Decidable q] {a b : Except Error α}
    {a' b' : Except Error β} (hpq : p ↔ q) (hyes : q → Sim R a a') (hno : ¬ q → Sim R b b') :
    Sim R (if p then a else b) (if q then a' else b') := by
  by_cases hq : q
  · rw [ite_eq_left (hpq.mpr hq), ite_eq_left hq]
    exact hyes hq
  · rw [ite_eq_right (fun hp => hq (hpq.mp hp)), ite_eq_right hq]
    exact hno hq

theorem Sim.dite {R : α → β → Prop} {p q : Prop} [Decidable p] [Decidable q]
    {a : p → Except Error α} {b : ¬ p → Except Error α} {a' : q → Except Error β}
    {b' : ¬ q → Except Error β} (hpq : p ↔ q) (hyes : ∀ hp hq, Sim R (a hp) (a' hq))
    (hno : ∀ hp hq, Sim R (b hp) (b' hq)) :
    Sim R (if h : p then a h else b h) (if h : q then a' h else b' h) := by
  by_cases hq : q
  · rw [dite_eq_left (hpq.mpr hq), dite_eq_left hq]
    exact hyes _ hq
  · rw [dite_eq_right (fun hp => hq (hpq.mp hp)), dite_eq_right hq]
    exact hno _ hq

theorem Sim.bind_eq {R : α → β → Prop} {y : Except Error γ} {f : γ → Except Error α}
    {g : γ → Except Error β} (step : ∀ v, y = .ok v → Sim R (f v) (g v)) :
    Sim R (y >>= f) (y >>= g) := by
  cases y with
  | error e => exact Sim.error _ e
  | ok v => exact step v rfl

theorem Sim.bind_of_eq {R : α → β → Prop} {x y : Except Error γ} {f : γ → Except Error α}
    {g : γ → Except Error β} (hxy : x = y) (step : ∀ v, y = .ok v → Sim R (f v) (g v)) :
    Sim R (x >>= f) (y >>= g) := by
  subst hxy
  exact Sim.bind_eq step

theorem Sim.with_eq {R : α → β → Prop} {x : Except Error α} {y : Except Error β} (h : Sim R x y) :
    Sim (fun a b => R a b ∧ y = .ok b) x y := by
  intro b hb
  obtain ⟨a, hx, hab⟩ := h b hb
  exact ⟨a, hx, hab, hb⟩

theorem Sim.attach {R : α → β → Prop} {R' : γ → δ → Prop} {x : Except Error α}
    {y : Except Error β} {f : {a // x = .ok a} → Except Error γ}
    {g : {b // y = .ok b} → Except Error δ} (h : Sim R x y)
    (step : ∀ a b, R a.val b.val → Sim R' (f a) (g b)) : Sim R' (x.attach >>= f) (y.attach >>= g) := by
  intro d hd
  cases y with
  | error e => cases hd
  | ok b =>
    obtain ⟨a, rfl, hab⟩ := h b rfl
    exact step ⟨a, rfl⟩ ⟨b, rfl⟩ hab d hd

theorem index_error (h : ¬ o < n) : index n o = .error (.assertion "offset is out of bounds") := by
  unfold index
  rw [dite_eq_right h]
  rfl

-- Both sides read the same offset, shifted by `b` on the left.
theorem Sim.index_bind {R : α → β → Prop} {n' n b o' o : ℕ} {f : Fin n' → Except Error α}
    {g : Fin n → Except Error β} (hn : n' = b + n) (ho : o' = b + o)
    (step : ∀ (i' : Fin n') (i : Fin n), i'.val = b + i.val → Sim R (f i') (g i)) :
    Sim R (index n' o' >>= f) (index n o >>= g) := by
  subst ho
  by_cases ho : o < n
  · have e1 : index n o = .ok ⟨o, ho⟩ := index_eq ⟨o, ho⟩
    have e2 : index n' (b + o) = .ok ⟨b + o, by omega⟩ := index_eq ⟨b + o, by omega⟩
    rw [e1, e2]
    exact step _ _ rfl
  · rw [index_error ho, except_error_bind]
    exact Sim.error _ _

-- Both sides check the same offset, shifted by `b` on the left, then run `gen` or `rest`.
theorem Sim.ite_index {R : α → β → Prop} {A A' : Prop} [Decidable A] [Decidable A']
    {n' n b o' o : ℕ} {B : Fin n' → Prop} {B' : Fin n → Prop} [DecidablePred B] [DecidablePred B']
    {gen rest : Except Error α} {gen' rest' : Except Error β}
    (hA : A ↔ A') (hn : n' = b + n) (ho : o' = b + o)
    (hB : ∀ i i', i.val = b + i'.val → (B i ↔ B' i'))
    (hgen : A' → Sim R gen gen') (hrest : Sim R rest rest') :
    Sim R (if A then index n' o' >>= (fun i => if B i then gen else rest) else rest)
      (if A' then index n o >>= (fun i => if B' i then gen' else rest') else rest') :=
  Sim.ite hA (fun hA' => Sim.index_bind hn ho fun i i' hi =>
    Sim.ite (hB i i' hi) (fun _ => hgen hA') (fun _ => hrest)) (fun _ => hrest)

theorem Sim.requires {R : α → β → Prop} {p q : Prop} [Decidable p] [Decidable q] {x : Except Error α}
    {y : Except Error β} {r r' : String} (hpq : p ↔ q) (step : q → Sim R x y) :
    Sim R (requires p r >>= fun _ => x) (requires q r' >>= fun _ => y) := by
  by_cases hq : q
  · rw [requires_of_true _ (hpq.mpr hq), requires_of_true _ hq]
    exact step hq
  · intro b hb
    simp [_root_.Shuffler.BuildBottomUp.requires, hq, throw, throwThe, MonadExceptOf.throw,
      except_error_bind] at hb

-- Both loop bodies stop at the same step, or both continue.
def StepRel (R : β' → β → Prop) : ForInStep β' → ForInStep β → Prop
  | .done a, .done b => R a b
  | .yield a, .yield b => R a b
  | _, _ => False

theorem Sim.forIn {R : β' → β → Prop} (xs : List α) (f : α → α')
    (bL : α' → β' → Except Error (ForInStep β')) (bS : α → β → Except Error (ForInStep β))
    (hstep : ∀ x ∈ xs, ∀ a b, R a b → Sim (StepRel R) (bL (f x) a) (bS x b))
    (a : β') (b : β) (hr : R a b) :
    Sim R (forIn (xs.map f) a bL) (forIn xs b bS) := by
  induction xs generalizing a b with
  | nil => exact Sim.ok hr
  | cons x xs ih =>
    simp only [List.map_cons, List.forIn_cons]
    refine Sim.bind (hstep x (List.mem_cons_self ..) a b hr) ?_
    rintro (a' | a') (b' | b') hab <;> simp only [StepRel] at hab
    · exact Sim.ok hab
    · exact ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy)) _ _ hab

--- Lifted states ---------------------------------------------------------------------------------

-- `L` is `S` with `pre` below its stack and below its target.
structure Lifted (pre : Stack) (L : State source' (pre ++ target) spills)
    (S : State source target spills) : Prop where
  stack : L.stack = pre ++ S.stack
  pending : L.pending_generations = S.pending_generations
  count : L.trace.swapCount = S.trace.swapCount
  low : ∀ j < pre.length, L.positionOfNat j = some j
  position : ∀ j, L.positionOfNat (pre.length + j) = (S.positionOfNat j).map (pre.length + ·)
  copies : ∀ v ∈ target, ¬ v.can_be_freely_generated → ¬ spills.is_spilled v → v ∈ S.stack

theorem positionOfNat_lt (s : State source target spills) (j : ℕ) (hj : j < target.length) :
    s.positionOfNat j = (s.mapping.symm ⟨j, hj⟩).map Fin.val := by
  simp [State.positionOfNat, State.positionOf, hj]

theorem slotAt_append (pre xs : Stack) (o : ℕ) :
    slotAt (pre ++ xs) (pre.length + o) = slotAt xs o := by
  by_cases ho : o < xs.length
  · rw [show o = (⟨o, ho⟩ : Fin xs.length).val from rfl, slotAt_index,
      show pre.length + o = (⟨pre.length + o, by simp; omega⟩ : Fin (pre ++ xs).length).val from rfl,
      slotAt_index]
    simp [List.getElem_append_right]
  · have hl : ¬ pre.length + o < (pre ++ xs).length := by simp; omega
    simp only [slotAt, index_error ho, index_error hl, except_error_bind]

section Lifted

variable {pre : Stack} {L : State source' (pre ++ target) spills} {S : State source target spills}

theorem Lifted.length (h : Lifted pre L S) : L.stack.length = pre.length + S.stack.length := by
  rw [h.stack, List.length_append]

theorem Lifted.getElem (h : Lifted pre L S) (i : ℕ) (hi : i < S.stack.length) :
    L.stack[pre.length + i]'(by rw [h.length]; omega) = S.stack[i] := by
  rw [List.getElem_of_eq h.stack, List.getElem_append_right (by omega)]
  simp

theorem Lifted.slotAt (h : Lifted pre L S) (o : ℕ) :
    slotAt L.stack (pre.length + o) = slotAt S.stack o := by
  rw [h.stack, slotAt_append]

theorem Lifted.slotAt_fin (h : Lifted pre L S) (i : Fin L.stack.length) (i' : Fin S.stack.length)
    (hi : i.val = pre.length + i'.val) :
    BuildBottomUp.slotAt L.stack i.val = BuildBottomUp.slotAt S.stack i'.val := by
  rw [hi, h.slotAt]

theorem Lifted.isFinal (h : Lifted pre L S) (o : ℕ) :
    (∃ h, L.isFinal ⟨pre.length + o, h⟩) ↔ ∃ h, S.isFinal ⟨o, h⟩ := by
  rw [isFinal_iff_positionOf, isFinal_iff_positionOf, h.position]
  cases S.positionOfNat o <;> simp

theorem Lifted.isFinal_fin (h : Lifted pre L S) (i : Fin L.stack.length) (i' : Fin S.stack.length)
    (hi : i.val = pre.length + i'.val) : L.isFinal i ↔ S.isFinal i' := by
  rw [State.isFinal_iff, State.isFinal_iff, hi]
  exact h.isFinal _

theorem Lifted.isFinal_low (h : Lifted pre L S) (j : ℕ) (hj : j < pre.length) : ∃ h, L.isFinal ⟨j, h⟩ :=
  (isFinal_iff_positionOf L j).mpr (h.low j hj)

theorem Lifted.offsetToDepth (h : Lifted pre L S) (i : Fin L.stack.length)
    (i' : Fin S.stack.length) (hi : i.val = pre.length + i'.val) :
    (L.stack.offsetToDepth i).val = (S.stack.offsetToDepth i').val := by
  simp only [Stack.offsetToDepth, h.length]
  omega

theorem Lifted.depthOf (h : Lifted pre L S) (i : Fin L.stack.length)
    (i' : Fin S.stack.length) (hi : i.val = pre.length + i'.val) :
    (L.depthOf i).val = (S.depthOf i').val :=
  h.offsetToDepth i i' hi

theorem Lifted.isSwapReachable (h : Lifted pre L S) (i : Fin L.stack.length)
    (i' : Fin S.stack.length) (hi : i.val = pre.length + i'.val) :
    L.isSwapReachable i ↔ S.isSwapReachable i' := by
  simp only [State.isSwapReachable, h.depthOf i i' hi]

theorem Lifted.isSwapReachable_fin (h : Lifted pre L S) (i : Fin L.stack.length)
    (i' : Fin S.stack.length) (hi : i.val = pre.length + i'.val) :
    L.stack.isSwapReachable i ↔ S.stack.isSwapReachable i' := by
  simp only [Stack.isSwapReachable, h.offsetToDepth i i' hi]

theorem Lifted.positionOf (h : Lifted pre L S) (d : Fin (pre ++ target).length)
    (d' : Fin target.length) (hd : d.val = pre.length + d'.val) :
    (L.positionOf d).map Fin.val = (S.positionOf d').map (pre.length + ·.val) := by
  have hp := h.position d'.val
  rw [positionOfNat_lt S _ d'.isLt, ← hd, positionOfNat_lt L _ d.isLt, Option.map_map] at hp
  exact hp

theorem Lifted.positionOf_isSome (h : Lifted pre L S) (d : Fin (pre ++ target).length)
    (d' : Fin target.length) (hd : d.val = pre.length + d'.val) :
    (L.positionOf d).isSome = (S.positionOf d').isSome := by
  have hp := congrArg Option.isSome (h.positionOf d d' hd)
  simpa using hp

theorem Lifted.positionOf_none (h : Lifted pre L S) (d : Fin (pre ++ target).length)
    (d' : Fin target.length) (hd : d.val = pre.length + d'.val) (hn : S.positionOf d' = none) :
    L.positionOf d = none := by
  have hp := h.positionOf d d' hd
  rw [hn, Option.map_none] at hp
  simpa using hp

theorem Lifted.positionOf_some (h : Lifted pre L S) (d : Fin (pre ++ target).length)
    (d' : Fin target.length) (hd : d.val = pre.length + d'.val) {b' : Fin S.stack.length}
    (hb : S.positionOf d' = some b') :
    ∃ b : Fin L.stack.length, L.positionOf d = some b ∧ b.val = pre.length + b'.val := by
  have hp := h.positionOf d d' hd
  rw [hb, Option.map_some] at hp
  obtain ⟨b, hb, hbv⟩ := Option.map_eq_some_iff.mp hp
  exact ⟨b, hb, hbv⟩

theorem Lifted.mem (h : Lifted pre L S) {v : Value} (hv : v ∈ S.stack) : v ∈ L.stack := by
  rw [h.stack]
  exact List.mem_append_right _ hv

theorem Lifted.copy (h : Lifted pre L S) {v : Value} (hv : v ∈ S.stack) :
    ∃ c c', S.stack.shallowestCopyPosition v = some c' ∧
      L.stack.shallowestCopyPosition v = some c ∧ c.val = pre.length + c'.val := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp
    ((Stack.shallowestCopyPosition_isSome _ _).mpr hv)
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp
    ((Stack.shallowestCopyPosition_isSome _ _).mpr (h.mem hv))
  refine ⟨c, c', hc', hc, ?_⟩
  have hv' := shallowestCopyPosition_value _ _ c' hc'
  have hv'' := shallowestCopyPosition_value _ _ c hc
  have hge := shallowestCopyPosition_ge L.stack v c ⟨pre.length + c'.val, by rw [h.length]; omega⟩
    hc (by rw [← hv']; exact h.getElem c'.val c'.isLt)
  dsimp only at hge
  obtain ⟨k, hk⟩ : ∃ k, c.val = pre.length + k := ⟨c.val - pre.length, by omega⟩
  have hkl : k < S.stack.length := by have := c.isLt; have := h.length; omega
  have hle := shallowestCopyPosition_ge S.stack v c' ⟨k, hkl⟩ hc' (by
    rw [Fin.getElem_fin, ← h.getElem k hkl, ← hv'', Fin.getElem_fin]
    exact getElem_congr_idx hk.symm)
  dsimp only at hle
  omega

theorem Lifted.isDupReachable (h : Lifted pre L S) (i : Fin L.stack.length)
    (i' : Fin S.stack.length) (hi : i.val = pre.length + i'.val) :
    L.stack.isDupReachable i ↔ S.stack.isDupReachable i' := by
  simp only [Stack.isDupReachable, h.offsetToDepth i i' hi]

theorem Lifted.available (h : Lifted pre L S) (d : Fin target.length) : S.isAvailable d := by
  simp only [State.isAvailable, Stack.shallowestCopyPosition_isSome]
  by_cases hg : target[d].can_be_freely_generated
  · exact Or.inl hg
  · by_cases hs : spills.is_spilled target[d]
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr (h.copies _ (List.getElem_mem d.isLt) hg hs))

end Lifted

theorem swapIdx_add (b x y p : ℕ) : swapIdx (b + x) (b + y) (b + p) = b + swapIdx x y p := by
  unfold swapIdx
  split_ifs <;> omega

theorem swapIdx_low (b x y j : ℕ) (hj : j < b) : swapIdx (b + x) (b + y) j = j := by
  unfold swapIdx
  split_ifs <;> omega

theorem positionOfNat_swapDestinations (s : State source target spills) (a a' : Fin s.stack.length)
    (j : ℕ) :
    ({ s with mapping := s.mapping.swapDestinations a a' } : State source target spills).positionOfNat j =
      (s.positionOfNat j).map (swapIdx a.val a'.val) := by
  unfold State.positionOfNat State.positionOf
  split
  · simp only [Mapping.swapDestinations_symm_apply, Option.map_map]
    congr 1
    funext p
    simp only [Function.comp_apply, Equiv.swap_apply_def, swapIdx, Fin.ext_iff]
    split_ifs <;> rfl
  · rfl

section Lifted

variable {pre : Stack} {L : State source' (pre ++ target) spills} {S : State source target spills}

theorem Lifted.retag (h : Lifted pre L S) {L' : State source' (pre ++ target) spills}
    {S' : State source target spills} (hstack : L'.stack = pre ++ S'.stack)
    (hpending : L'.pending_generations = S'.pending_generations)
    (hcount : L'.trace.swapCount = S'.trace.swapCount) (hsub : S.stack ⊆ S'.stack) (x y : ℕ)
    (hL : ∀ j, L'.positionOfNat j =
      (L.positionOfNat j).map (swapIdx (pre.length + x) (pre.length + y)))
    (hS : ∀ j, S'.positionOfNat j = (S.positionOfNat j).map (swapIdx x y)) : Lifted pre L' S' where
  stack := hstack
  pending := hpending
  count := hcount
  low j hj := by rw [hL, h.low j hj, Option.map_some, swapIdx_low _ _ _ _ hj]
  position j := by
    rw [hL, h.position, hS, Option.map_map, Option.map_map]
    congr 1
    funext p
    exact swapIdx_add _ _ _ _
  copies v hv hg hs := hsub (h.copies v hv hg hs)

theorem swapDestinations_ok {s n : State source target spills} {x y : ℕ}
    (hrun : s.swapDestinations x y = .ok n) :
    ∃ hx : x < s.stack.length, ∃ hy : y < s.stack.length,
      n = { s with mapping := s.mapping.swapDestinations ⟨x, hx⟩ ⟨y, hy⟩ } := by
  by_cases hx : x < s.stack.length
  · by_cases hy : y < s.stack.length
    · refine ⟨hx, hy, ?_⟩
      rw [show x = (⟨x, hx⟩ : Fin s.stack.length).val from rfl,
        show y = (⟨y, hy⟩ : Fin s.stack.length).val from rfl, swapDestinations_result] at hrun
      exact (Except.ok.inj hrun).symm
    · simp only [State.swapDestinations, index_eq ⟨x, hx⟩, index_error hy, except_ok_bind,
        except_error_bind] at hrun
      cases hrun
  · simp only [State.swapDestinations, index_error hx, except_error_bind] at hrun
    cases hrun

theorem Lifted.swapDestinations (h : Lifted pre L S) (x' y' x y : ℕ) (hx : x' = pre.length + x)
    (hy : y' = pre.length + y) :
    Sim (Lifted pre) (L.swapDestinations x' y') (S.swapDestinations x y) := by
  intro S' hrun
  obtain ⟨hx, hy, rfl⟩ := swapDestinations_ok hrun
  subst x' y'
  have hl := h.length
  refine ⟨_, swapDestinations_result L ⟨pre.length + x, by omega⟩ ⟨pre.length + y, by omega⟩, ?_⟩
  exact h.retag h.stack h.pending h.count (List.Subset.refl _) x y
    (positionOfNat_swapDestinations L _ _) (positionOfNat_swapDestinations S _ _)

end Lifted

theorem swapWith_pre {s n : State source target spills} {x : ℕ}
    (hrun : s.swapWith x = .ok n) :
    ∃ hx : x < s.stack.length, x + 1 < s.stack.length ∧
      s.stack.isSwapReachable ⟨x, hx⟩ ∧ ¬ s.isFinal ⟨x, hx⟩ := by
  have hs : ⦃True⦄ s.swapWith x
      ⦃fun _ => ∃ hx : x < s.stack.length, x + 1 < s.stack.length ∧
        s.stack.isSwapReachable ⟨x, hx⟩ ∧ ¬ s.isFinal ⟨x, hx⟩; epost⟨fun _ => True⟩⦄ := by
    vcgen [State.swapWith, requires, index]
    all_goals simp_all [Stack.isSwapReachable, Stack.offsetToDepth]
    all_goals omega
  have hp := post_of_triple_ok hs hrun
  exact hp

theorem swapWith_noBlocked (s : State source target spills) (x : ℕ) :
    NoBlocked (s.swapWith x) := by
  apply noBlocked_of_triple
  vcgen [State.swapWith, requires, index]
  all_goals simp_all [noBlockedErrors]

section Lifted

variable {pre : Stack} {L : State source' (pre ++ target) spills} {S : State source target spills}

theorem Lifted.swapWith (h : Lifted pre L S) (x : ℕ) :
    Sim (Lifted pre) (L.swapWith (pre.length + x)) (S.swapWith x) := by
  intro S' hrun
  obtain ⟨hx, hbelow, hreach, hnfinal⟩ := swapWith_pre hrun
  have hsw : Swapped S S' ⟨x, hx⟩ := by
    have hp := swap_spec S ⟨x, hx⟩ hbelow hreach hnfinal
    rw [hrun] at hp
    exact hp
  have hcS := (swap_counts S S' x hrun).swaps
  have hl := h.length
  obtain ⟨L', hL, hlw⟩ := Spec.success
    (swap_spec L ⟨pre.length + x, by omega⟩ (show pre.length + x + 1 < L.stack.length by omega)
      ((h.isSwapReachable_fin ⟨pre.length + x, by omega⟩ ⟨x, hx⟩ rfl).mpr hreach)
      (fun hf => hnfinal ((h.isFinal x).mp ⟨_, hf⟩).2))
    (swapWith_noBlocked L _)
  have hcL := (swap_counts L L' _ hL).swaps
  have htop : L.stack.length - 1 = pre.length + (S.stack.length - 1) := by omega
  refine ⟨L', hL, h.retag ?_ (hlw.pending.trans (h.pending.trans hsw.pending.symm))
    (by rw [hcL, hcS, h.count]) hsw.subset x (S.stack.length - 1) ?_ hsw.positionOf⟩
  · rw [hlw.stack_eq, hsw.stack_eq]
    dsimp only
    rw [htop]
    have hs := h.stack
    revert hs
    generalize L.stack = ls
    rintro rfl
    exact swap_append_add _ _ _ _
  · intro j
    rw [hlw.positionOf]
    dsimp only
    rw [htop]

end Lifted

--- Produce ---------------------------------------------------------------------------------------
-- A filtered copy is a reachable shallowest copy.
abbrev Filtered (s : State source target spills) (d : Fin target.length) : Prop :=
  ∃ c, (s.stack.shallowestCopyPosition target[d]).filter
    (fun pos => s.stack.isDupReachable pos) = some c

theorem produce_pre {s n : State source target spills} {d : Fin target.length}
    (hrun : s.produce d = .ok n) :
    s.mapping.symm d = none ∧
      (target[d].can_be_freely_generated ∨ spills.is_spilled target[d] ∨ Filtered s d) := by
  have hc : ⦃True⦄ s.produce d
      ⦃fun _ => s.mapping.symm d = none ∧
        (target[d].can_be_freely_generated ∨ spills.is_spilled target[d] ∨ Filtered s d);
        epost⟨fun _ => True⟩⦄ := by
    vcgen [State.produce, State.push, State.dup, requires, index]
    all_goals refine ⟨by assumption, ?_⟩
    all_goals simp only [Fin.getElem_fin] at *
    all_goals tauto
  have hp := post_of_triple_ok hc hrun
  exact hp

theorem produce_noBlocked' (s : State source target spills) (d : Fin target.length)
    (hfilter :
      ¬(target[d].can_be_freely_generated ∨ spills.is_spilled target[d]) → Filtered s d) :
    NoBlocked (s.produce d) := by
  apply noBlocked_of_triple
  vcgen [State.produce, State.push, State.dup, requires, index]
  all_goals simp_all [noBlockedErrors]

theorem _root_.Shuffler.BuildBottomUp.Growth.positionOfNat {s n : State source target spills}
    {d : Fin target.length} (hg : Growth s n d p) (j : ℕ) :
    n.positionOfNat j = if j = d.val then some s.stack.length else s.positionOfNat j := by
  split
  · rename_i hjd
    subst hjd
    rw [positionOfNat_lt n _ d.isLt]
    exact hg.bound
  · exact hg.positionOf_ne j ‹_›

section Lifted

variable {pre : Stack} {L : State source' (pre ++ target) spills} {S : State source target spills}

theorem Lifted.produce (h : Lifted pre L S) (d : Fin (pre ++ target).length)
    (d' : Fin target.length) (hd : d.val = pre.length + d'.val) :
    Sim (Lifted pre) (L.produce d) (S.produce d') := by
  intro S' hrun
  obtain ⟨hbS, hcond⟩ := produce_pre hrun
  have hgS : Growth S S' d' (S.pending_generations - 1) := by
    have hp := post_of_triple_ok (produce_spec S d' hbS (h.available d')) hrun
    exact hp
  have hslot : (pre ++ target)[d] = target[d'] := by
    simp only [Fin.getElem_fin, hd]
    rw [List.getElem_append_right (by omega)]
    simp
  have hbL : L.mapping.symm d = none := h.positionOf_none d d' hd hbS
  have haL : L.isAvailable d := by
    have ha := h.available d'
    simp only [State.isAvailable, Stack.shallowestCopyPosition_isSome] at ha ⊢
    rw [hslot]
    exact ha.imp_right fun h' => h'.imp_right h.mem
  have hfL :
      ¬((pre ++ target)[d].can_be_freely_generated ∨ spills.is_spilled (pre ++ target)[d]) →
      Filtered L d := by
    intro hn
    rw [hslot] at hn
    obtain ⟨c', hc'⟩ := (hcond.resolve_left fun h' => hn (Or.inl h')).resolve_left
      fun h' => hn (Or.inr h')
    obtain ⟨hsc', hr'⟩ := Option.filter_eq_some_iff.mp hc'
    have hmem : target[d'] ∈ S.stack := by
      rw [← shallowestCopyPosition_value _ _ c' hsc']
      exact List.getElem_mem _
    obtain ⟨c, c'', hc'', hc, hcc⟩ := h.copy hmem
    rw [hsc'] at hc''
    cases hc''
    refine ⟨c, ?_⟩
    rw [hslot, hc]
    simp only [Option.filter_some]
    rw [ite_eq_left]
    simpa [h.isDupReachable c c' hcc] using hr'
  obtain ⟨L', hL, hgL⟩ := Spec.success
    ((spec_iff_triple _ _).mpr (produce_spec L d hbL haL)) (produce_noBlocked' L d hfL)
  have hl := h.length
  refine ⟨L', hL, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hgL.stack_eq, hgS.stack_eq, h.stack, hslot, List.append_assoc]
  · rw [hgL.pending_eq, hgS.pending_eq, h.pending]
  · rw [produce_swaps hL, produce_swaps hrun, h.count]
  · intro j hj
    rw [hgL.positionOfNat, ite_eq_right (by omega), h.low j hj]
  · intro j
    rw [hgL.positionOfNat, hgS.positionOfNat, h.position]
    by_cases hj : j = d'.val
    · rw [ite_eq_left (by omega), ite_eq_left hj, hl]
      rfl
    · rw [ite_eq_right (by omega), ite_eq_right hj]
  · exact fun v hv hg hs => hgS.subset (h.copies v hv hg hs)

theorem Lifted.generate (h : Lifted pre L S) (o' o : ℕ) (ho : o' = pre.length + o) :
    Sim (Lifted pre) (L.generate o') (S.generate o) := by
  subst ho
  unfold State.generate
  simp_loop
  refine Sim.index_bind (by simp) rfl fun d d' hd => ?_
  refine Sim.bind (h.produce d d' hd) fun L1 S1 h1 => ?_
  have hl := h1.length
  apply Sim.ite (by omega)
  · intro hq
    refine Sim.index_bind hl rfl fun i' i hi => ?_
    apply Sim.ite (not_congr (h1.isFinal_fin i' i hi))
    · intro _
      rw [show L1.stack.length - 1 = pre.length + (S1.stack.length - 1) by omega, h1.slotAt,
        h1.slotAt]
      refine Sim.bind_eq fun v _ => Sim.bind_eq fun w _ => ?_
      apply Sim.ite Iff.rfl
      · exact fun _ => Sim.bind (h1.swapDestinations _ _ _ _ rfl rfl) fun _ _ h2 => Sim.ok h2
      · intro _
        refine Sim.index_bind hl rfl fun j' j hj => ?_
        apply Sim.ite (h1.isSwapReachable j' j hj)
        · exact fun _ => Sim.bind (h1.swapWith o) fun _ _ h2 => Sim.ok h2
        · exact fun _ => Sim.ok h1
    · exact fun _ => Sim.ok h1
  · exact fun _ => Sim.ok h1

--- Scans -----------------------------------------------------------------------------------------

-- The urgent scan of `buildBottomUp.loop`. A def over a general state lets its `if let` use the
-- matcher of the loop.
def urgentScanOf {source target : Stack} {spills : SpillSet} (state : State source target spills) (cursor : ℕ) : Except Error (Option ℕ) := do
  let mut urgent := none
  for offset in [cursor : target.length] do
    if (state.positionOf (← index target.length offset)).isSome then
      continue
    let slot ← BuildBottomUp.slotAt target offset
    if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
      continue
    if let some copy := state.stack.shallowestCopyPosition slot then
      if ¬ state.stack.isDupReachable copy then
        throw (.blocked ((state.depthOf copy) - MAX_DUP_DEPTH))
      if (state.depthOf copy) = MAX_DUP_DEPTH ∧ copy.val ≠ cursor ∧ urgent.isNone then
        urgent := some offset
  return urgent

theorem Lifted.urgentScan (h : Lifted pre L S) (c : ℕ) :
    Sim (fun p q => p = q.map (pre.length + ·))
      (urgentScanOf L (pre.length + c)) (urgentScanOf S c) := by
  unfold urgentScanOf
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', bind_pure]
  have hlist : List.range' (pre.length + c) [pre.length + c : (pre ++ target).length].size =
      (List.range' c [c : target.length].size).map (pre.length + ·) := by
    rw [List.map_add_range']
    simp [Std.Legacy.Range.size]
    omega
  rw [hlist]
  refine Sim.forIn _ _ _ _ ?_ none none rfl
  rintro x hx _ acc rfl
  have hx' : x < target.length := by
    simp [List.mem_range', Std.Legacy.Range.size] at hx
    omega
  refine Sim.index_bind (by simp) rfl fun d d' hd => ?_
  apply Sim.ite (by rw [h.positionOf_isSome d d' hd])
  · exact fun _ => Sim.ok rfl
  intro _
  rw [slotAt_append]
  apply Sim.bind_eq
  intro v hv
  apply Sim.ite Iff.rfl
  · exact fun _ => Sim.ok rfl
  intro hn
  rw [show x = (⟨x, hx'⟩ : Fin target.length).val from rfl, slotAt_index] at hv
  cases hv
  obtain ⟨cL, cS, hcS, hcL, hcc⟩ := h.copy (h.copies _ (List.getElem_mem _)
    (fun h' => hn (Or.inr (Or.inl h'))) (fun h' => hn (Or.inr (Or.inr h'))))
  simp only [Fin.getElem_fin] at hcL hcS ⊢
  rw [hcL, hcS]
  apply Sim.ite (by rw [h.isDupReachable cL cS hcc])
  · exact fun _ => Sim.error _ _
  intro _
  apply Sim.ite (by
    rw [h.depthOf cL cS hcc, hcc, Option.isNone_map, ne_eq, ne_eq, Nat.add_left_cancel_iff])
  · exact fun _ => Sim.ok rfl
  · exact fun _ => Sim.ok rfl

theorem take_reverse_range_add (b n d : ℕ) (hd : d ≤ n) :
    (List.range (b + n)).reverse.take d = ((List.range n).reverse.take d).map (b + ·) := by
  rw [List.range_add, List.reverse_append, List.take_append_of_le_length (by simp; omega),
    ← List.map_reverse, List.map_take]

theorem Lifted.copyScan (h : Lifted pre L S) (bL : Fin L.stack.length) (bS : Fin S.stack.length)
    (hb : bL.val = pre.length + bS.val) :
    Sim (fun p q => p = pre.length + q)
      (do
        let mut pos := bL.val
        for candidate in (List.range L.stack.length).reverse.take (L.depthOf bL) do
          if (← BuildBottomUp.slotAt L.stack candidate) = (← BuildBottomUp.slotAt L.stack bL) ∧
              ¬ L.isFinal (← index L.stack.length candidate) then
            pos := candidate
            break
        return pos : Except Error ℕ)
      (do
        let mut pos := bS.val
        for candidate in (List.range S.stack.length).reverse.take (S.depthOf bS) do
          if (← BuildBottomUp.slotAt S.stack candidate) = (← BuildBottomUp.slotAt S.stack bS) ∧
              ¬ S.isFinal (← index S.stack.length candidate) then
            pos := candidate
            break
        return pos : Except Error ℕ) := by
  simp only [bind_pure]
  have hlist : (List.range L.stack.length).reverse.take (L.depthOf bL) =
      ((List.range S.stack.length).reverse.take (S.depthOf bS)).map (pre.length + ·) := by
    rw [h.depthOf bL bS hb, show List.range L.stack.length = List.range (pre.length + S.stack.length)
      by rw [h.length], take_reverse_range_add _ _ _ (S.depthOf bS).isLt.le]
  rw [hlist, h.slotAt_fin bL bS hb, hb]
  refine Sim.forIn _ _ _ _ ?_ _ _ rfl
  rintro x hx _ acc rfl
  rw [h.slotAt]
  refine Sim.bind_eq fun v _ => Sim.bind_eq fun w _ => ?_
  refine Sim.index_bind h.length rfl fun i' i hi => ?_
  apply Sim.ite (and_congr Iff.rfl (not_congr (h.isFinal_fin i' i hi)))
  · exact fun _ => Sim.ok rfl
  · exact fun _ => Sim.ok rfl

end Lifted
--- Lifted permutations ---------------------------------------------------------------------------

open Shuffler.Permute in
-- Positions below b are fixed. Position b + j moves to b + (permS j).
def PermLift (b : ℕ) (permL : Equiv.Perm (Fin m)) (permS : Equiv.Perm (Fin n)) : Prop :=
  (∀ i : Fin m, i.val < b → permL i = i) ∧
    ∀ (i : Fin m) (j : Fin n), i.val = b + j.val → (permL i).val = b + (permS j).val

theorem finRange_add (b n : ℕ) : List.finRange (b + n) =
    (List.finRange b).map (Fin.castAdd n) ++ (List.finRange n).map (Fin.natAdd b) := by
  simp only [← List.ofFn_id, List.ofFn_add, List.map_ofFn]
  rfl

theorem search_fixed (perm : Equiv.Perm (Fin m)) (l : List (Fin m)) (p : Option {i // perm i ≠ i})
    (hl : ∀ i ∈ l, perm i = i) :
    l.foldl (fun p i => if h : perm i ≠ i then some ⟨i, h⟩ else p) p = p := by
  induction l generalizing p with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, dite_eq_right_iff.mpr (fun h => absurd (hl x (by simp)) h)]
    exact ih p (fun i hi => hl i (by simp [hi]))

theorem search_map (permL : Equiv.Perm (Fin m)) (permS : Equiv.Perm (Fin n)) (f : Fin n → Fin m)
    (hf : ∀ j, permL (f j) ≠ f j ↔ permS j ≠ j) (hv : ∀ j, (f j).val = b + j.val)
    (l : List (Fin n)) (pL : Option {i // permL i ≠ i}) (pS : Option {i // permS i ≠ i})
    (hp : pL.map (·.1.val) = pS.map (b + ·.1.val)) :
    ((l.map f).foldl (fun p i => if h : permL i ≠ i then some ⟨i, h⟩ else p) pL).map (·.1.val) =
      (l.foldl (fun p i => if h : permS i ≠ i then some ⟨i, h⟩ else p) pS).map (b + ·.1.val) := by
  induction l generalizing pL pS with
  | nil => exact hp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    by_cases hx : permS x ≠ x
    · rw [dite_eq_left hx, dite_eq_left ((hf x).mpr hx)]
      simp [hv]
    · rw [dite_eq_right hx, dite_eq_right (fun h => hx ((hf x).mp h))]
      exact hp

theorem search_lift (hm : m = b + n) (permL : Equiv.Perm (Fin m)) (permS : Equiv.Perm (Fin n))
    (h : PermLift b permL permS) :
    ((List.finRange m).foldl (fun (p : Option {i // permL i ≠ i}) i => if h : permL i ≠ i then some ⟨i, h⟩ else p)
      none).map (·.1.val) =
      ((List.finRange n).foldl (fun (p : Option {i // permS i ≠ i}) i => if h : permS i ≠ i then some ⟨i, h⟩ else p)
        none).map (b + ·.1.val) := by
  subst hm
  rw [finRange_add, List.foldl_append, search_fixed _ ((List.finRange b).map (Fin.castAdd n)) _ (by
    intro i hi
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hi
    exact h.1 _ (by simp))]
  refine search_map _ _ _ (fun j => ?_) (fun j => Fin.val_natAdd b j) _ _ _ rfl
  rw [ne_eq, ne_eq, Fin.ext_iff, Fin.ext_iff, h.2 _ j (by simp), Fin.val_natAdd,
    Nat.add_left_cancel_iff]

theorem swap_lift_high {x y i : Fin m} {x' y' j : Fin n} (hx : x.val = b + x'.val)
    (hy : y.val = b + y'.val) (hi : i.val = b + j.val) :
    (Equiv.swap x y i).val = b + (Equiv.swap x' y' j).val := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

theorem PermLift.mul_swap {permL : Equiv.Perm (Fin m)} {permS : Equiv.Perm (Fin n)}
    (h : PermLift b permL permS) {x y : Fin m} {x' y' : Fin n} (hx : x.val = b + x'.val)
    (hy : y.val = b + y'.val) :
    PermLift b (permL * Equiv.swap x y) (permS * Equiv.swap x' y') := by
  refine ⟨fun i hi => ?_, fun i j hij => ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by rintro rfl; omega)
      (by rintro rfl; omega), h.1 i hi]
  · exact h.2 _ _ (swap_lift_high hx hy hij)

open Shuffler.Permute in
theorem go_lift (spills : SpillSet) (pre : Stack) {xs ys : Stack}
    (hys : ys.length = pre.length + xs.length) (hneS : xs.length > 0) (hneL : ys.length > 0)
    (currentS : Stack) (permS : Permutation xs) (traceS : Trace spills xs currentS)
    (hlenS : currentS.length = xs.length) :
    ∀ (currentL : Stack) (permL : Permutation ys) (traceL : Trace spills ys currentL)
      (hlenL : currentL.length = ys.length), currentL = pre ++ currentS →
      PermLift pre.length permL permS →
      ∀ {res : Stack} {tr : Trace spills xs res},
        permute.go spills xs currentS permS traceS hneS hlenS = .ok ⟨res, tr⟩ →
        ∃ tr', permute.go spills ys currentL permL traceL hneL hlenL = .ok ⟨pre ++ res, tr'⟩ ∧
          tr'.swapCount + traceS.swapCount = tr.swapCount + traceL.swapCount := by
  refine permute.go.induct spills xs hneS
    (motive := fun currentS permS traceS hlenS =>
      ∀ (currentL : Stack) (permL : Permutation ys) (traceL : Trace spills ys currentL)
        (hlenL : currentL.length = ys.length), currentL = pre ++ currentS →
        PermLift pre.length permL permS →
        ∀ {res : Stack} {tr : Trace spills xs res},
          permute.go spills xs currentS permS traceS hneS hlenS = .ok ⟨res, tr⟩ →
          ∃ tr', permute.go spills ys currentL permL traceL hneL hlenL = .ok ⟨pre ++ res, tr'⟩ ∧
            tr'.swapCount + traceS.swapCount = tr.swapCount + traceL.swapCount)
    ?_ ?_ ?_ ?_ ?_ currentS permS traceS hlenS
  · intro current perm trace hlen top htop ht idx hdepth currentL permL traceL hlenL hcur hrel
      res tr hresult
    rw [permute.go.eq_1, dite_eq_left ht, dite_eq_left hdepth] at hresult
    contradiction
  · intro current perm trace hlen top htop ht idx hdepth stack' perm' h1 h2 h3 trace' ih
      currentL permL traceL hlenL hcur hrel res tr hresult
    rw [permute.go.eq_1, dite_eq_left ht, dite_eq_right hdepth] at hresult
    have hv := hrel.2 ⟨ys.length - 1, by omega⟩ top (by simp only [htop]; omega)
    have htL : permL ⟨ys.length - 1, by omega⟩ ≠ ⟨ys.length - 1, by omega⟩ := by
      intro h
      apply ht
      rw [Fin.ext_iff] at h ⊢
      simp only at h
      omega
    have hidx : (permL ⟨ys.length - 1, by omega⟩).rev.val = idx := by
      simp only [Fin.val_rev, idx, hv]
      omega
    rw [permute.go.eq_1, dite_eq_left htL, dite_eq_right (by rw [hidx]; exact hdepth)]
    subst hcur
    refine (ih _ _ _ _ ?_ ?_ hresult).imp fun tr' h => ⟨h.1, ?_⟩
    · simp only [List.length_append, hidx, stack', hlen]
      rw [show pre.length + xs.length - 1 = pre.length + (xs.length - 1) by omega,
        show pre.length + (xs.length - 1) - idx = pre.length + (xs.length - 1 - idx) by omega,
        swap_append_add]
    · exact hrel.mul_swap (by simp only [htop]; omega) hv
    · have := h.2
      simp only [Trace.swapCount, trace'] at this ⊢
      omega
  · intro current perm trace hlen top htop ht search pos hpos hsearch idx hdepth
      currentL permL traceL hlenL hcur hrel res tr hresult
    dsimp only [search, idx] at hsearch hdepth
    rw [permute.go.eq_1, dite_eq_right ht] at hresult
    simp only [hsearch, dite_eq_left hdepth] at hresult
    contradiction
  · intro current perm trace hlen top htop ht search pos hpos hsearch idx hdepth hpos_ne hlt
      stack' perm' h1 h2 h3 trace' ih currentL permL traceL hlenL hcur hrel res tr hresult
    dsimp only [search, idx] at hsearch hdepth
    rw [permute.go.eq_1, dite_eq_right ht] at hresult
    simp only [hsearch, dite_eq_right hdepth] at hresult
    have hv := hrel.2 ⟨ys.length - 1, by omega⟩ top (by simp only [htop]; omega)
    have htL : ¬ permL ⟨ys.length - 1, by omega⟩ ≠ ⟨ys.length - 1, by omega⟩ := by
      intro h
      apply ht
      intro h'
      apply h
      rw [Fin.ext_iff] at h' ⊢
      simp only at h' hv ⊢
      omega
    have hs := search_lift hys permL perm hrel
    rw [hsearch] at hs
    obtain ⟨⟨posL, hposL⟩, hsL, hposv⟩ : ∃ q, (List.finRange ys.length).foldl
        (fun (p : Option {i // permL i ≠ i}) i => if h : permL i ≠ i then some ⟨i, h⟩ else p)
        none = some q ∧ q.1.val = pre.length + pos.val := by
      revert hs
      cases (List.finRange ys.length).foldl
        (fun (p : Option {i // permL i ≠ i}) i => if h : permL i ≠ i then some ⟨i, h⟩ else p) none
      · simp
      · simp
    have hidx : posL.rev.val = idx := by
      simp only at hposv
      simp only [Fin.val_rev, idx]
      omega
    rw [permute.go.eq_1, dite_eq_right htL]
    simp only [hsL, dite_eq_right (show ¬ posL.rev.val > MAX_SWAP_DEPTH by rw [hidx]; exact hdepth)]
    subst hcur
    refine (ih _ _ _ _ ?_ ?_ hresult).imp fun tr' h => ⟨h.1, ?_⟩
    · simp only [List.length_append, hidx, stack', hlen]
      rw [show pre.length + xs.length - 1 = pre.length + (xs.length - 1) by omega,
        show pre.length + (xs.length - 1) - idx = pre.length + (xs.length - 1 - idx) by omega,
        swap_append_add]
    · exact hrel.mul_swap (by simp only [htop]; omega) hposv
    · have := h.2
      simp only [Trace.swapCount, trace'] at this ⊢
      omega
  · intro current perm trace hlen top htop ht search hsearch currentL permL traceL hlenL hcur hrel
      res tr hresult
    dsimp only [search] at hsearch
    rw [permute.go.eq_1, dite_eq_right ht, hsearch] at hresult
    cases hresult
    have hv := hrel.2 ⟨ys.length - 1, by omega⟩ top (by simp only [htop]; omega)
    have htL : ¬ permL ⟨ys.length - 1, by omega⟩ ≠ ⟨ys.length - 1, by omega⟩ := by
      intro h
      apply ht
      intro h'
      apply h
      rw [Fin.ext_iff] at h' ⊢
      simp only at h' hv ⊢
      omega
    have hs := search_lift hys permL perm hrel
    rw [hsearch, Option.map_none, Option.map_eq_none_iff] at hs
    rw [permute.go.eq_1, dite_eq_right htL]
    simp only [hs]
    subst hcur
    exact ⟨traceL, rfl, Nat.add_comm _ _⟩

open Shuffler.Permute in
-- Permuting pre ++ xs with a permutation that fixes pre and acts on xs as permS
-- gives pre ++ (the result of permS on xs), with the same SWAP count.
theorem permute_lift (spills : SpillSet) (pre xs : Stack) (permL : Permutation (pre ++ xs))
    (permS : Permutation xs) (hrel : PermLift pre.length permL permS) {res : Stack}
    {tr : Trace spills xs res} (h : permute spills xs permS = .ok ⟨res, tr⟩) :
    ∃ tr', permute spills (pre ++ xs) permL = .ok ⟨pre ++ res, tr'⟩ ∧
      tr'.swapCount = tr.swapCount := by
  have hys : (pre ++ xs).length = pre.length + xs.length := List.length_append
  unfold permute at h ⊢
  by_cases hneS : 0 < xs.length
  · rw [dite_eq_left hneS] at h
    rw [dite_eq_left (by omega)]
    obtain ⟨tr', hgo, hc⟩ := go_lift spills pre hys hneS (by omega) xs permS (.Lit xs) rfl
      (pre ++ xs) permL (.Lit (pre ++ xs)) rfl rfl hrel h
    exact ⟨tr', hgo, by simpa [Trace.swapCount] using hc⟩
  · rw [dite_eq_right hneS] at h
    cases h
    have hfix : ∀ i, permL i = i := fun i => hrel.1 i (by omega)
    by_cases hneL : 0 < (pre ++ xs).length
    · rw [dite_eq_left hneL, permute.go.eq_1, dite_eq_right (by simp [hfix]),
        search_fixed _ _ _ (fun i _ => hfix i)]
      exact ⟨_, rfl, rfl⟩
    · rw [dite_eq_right hneL]
      exact ⟨_, rfl, rfl⟩

open Shuffler.Permute in
theorem permute_lift_eq (spills : SpillSet) {pre xs ys : Stack} (hys : ys = pre ++ xs)
    (permL : Permutation ys) (permS : Permutation xs) (hrel : PermLift pre.length permL permS)
    {res : Stack} {tr : Trace spills xs res} (h : permute spills xs permS = .ok ⟨res, tr⟩) :
    ∃ tr', permute spills ys permL = .ok ⟨pre ++ res, tr'⟩ ∧ tr'.swapCount = tr.swapCount := by
  subst hys
  exact permute_lift spills pre xs permL permS hrel h

theorem requires_of_false {c : Prop} [Decidable c] (h : ¬ c) (r : String) :
    requires c r = .error (.assertion r) := by
  unfold requires
  rw [dite_eq_right h]
  rfl

theorem mapping_eq_some_iff (s : State source target spills) (i : Fin s.stack.length) (j : ℕ)
    (hj : j < target.length) : s.mapping i = some ⟨j, hj⟩ ↔ s.positionOfNat j = some i.val := by
  rw [positionOfNat_lt _ _ hj, ← PEquiv.eq_some_iff]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    obtain ⟨x, hx, hxi⟩ := Option.map_eq_some_iff.mp h
    rw [show i = x from Fin.ext hxi.symm, hx]

theorem positionOf_toPermutation (s : State source target spills)
    (hlen : s.stack.length = target.length) (hsource : ∀ i, (s.mapping i).isSome)
    (i : Fin s.stack.length) :
    s.positionOfNat (s.mapping.toPermutation hlen hsource i).val = some i.val := by
  have happly := Mapping.toPermutation_apply s.mapping hlen hsource i
  exact (mapping_eq_some_iff s i _ (by omega)).mp happly.symm

namespace Lifted

variable {pre : Stack} {L : State source' (pre ++ target) spills} {S : State source target spills}

theorem complete (h : Lifted pre L S)
    (hq : S.stack.length = target.length ∧ ∀ i, (S.mapping i).isSome) :
    L.stack.length = (pre ++ target).length ∧ ∀ i, (L.mapping i).isSome := by
  have hl := h.length
  refine ⟨by simp; omega, fun i => ?_⟩
  by_cases hi : i.val < pre.length
  · rw [(mapping_eq_some_iff L i i.val (by simp; omega)).mpr (h.low i.val hi)]
    rfl
  · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hq.2 ⟨i.val - pre.length, by omega⟩)
    have hS := (mapping_eq_some_iff S _ j.val j.isLt).mp hj
    have hL : L.positionOfNat (pre.length + j.val) = some i.val := by
      rw [h.position, hS]
      simp only [Option.map_some, Option.some.injEq]
      omega
    rw [(mapping_eq_some_iff L i _ (by simp)).mpr hL]
    rfl

theorem permLift (h : Lifted pre L S) (hpL : L.stack.length = (pre ++ target).length)
    (hsL : ∀ i, (L.mapping i).isSome) (hpS : S.stack.length = target.length)
    (hsS : ∀ i, (S.mapping i).isSome) :
    PermLift pre.length (L.mapping.toPermutation hpL hsL) (S.mapping.toPermutation hpS hsS) := by
  refine ⟨fun i hi => Fin.ext ?_, fun i j hij => ?_⟩
  · exact positionOf_inj (positionOf_toPermutation L hpL hsL i) (h.low i.val hi)
  · apply positionOf_inj (positionOf_toPermutation L hpL hsL i)
    rw [h.position, positionOf_toPermutation S hpS hsS j, hij]
    rfl

end Lifted

--- Loop ------------------------------------------------------------------------------------------

-- Results agree up to pre at the bottom, with the same swap count.
abbrev LoopRel (pre : Stack) (r' : Σ res : Stack, Trace spills source' res)
    (r : Σ res : Stack, Trace spills source res) : Prop :=
  r'.1 = pre ++ r.1 ∧ r'.2.swapCount = r.2.swapCount

-- The steps after the target slot is filled: swap it into place, then advance.
theorem Lifted.tail {pre : Stack} {L : State source' (pre ++ target) spills}
    {S : State source target spills} (h : Lifted pre L S) (c : ℕ)
    (hrec : ∀ (L' : State source' (pre ++ target) spills) (S' : State source target spills),
      Lifted pre L' S' →
      Sim (LoopRel pre) (buildBottomUp.loop (pre.length + c + 1) L') (buildBottomUp.loop (c + 1) S')) :
    Sim (LoopRel pre)
      (index L.stack.length (pre.length + c) >>= fun i =>
        requires (¬ L.isFinal i) "target slot is already final" >>= fun _ =>
        if pre.length + c ≠ L.stack.length - 1 then
          index L.stack.length (pre.length + c) >>= fun i =>
            if ¬ L.isSwapReachable i then
              index L.stack.length (pre.length + c) >>= fun i =>
                Except.error (Error.blocked (↑(L.depthOf i) - MAX_SWAP_DEPTH))
            else L.swapWith (pre.length + c) >>= fun st => buildBottomUp.loop (pre.length + c + 1) st
        else buildBottomUp.loop (pre.length + c + 1) L)
      (index S.stack.length c >>= fun i =>
        requires (¬ S.isFinal i) "target slot is already final" >>= fun _ =>
        if c ≠ S.stack.length - 1 then
          index S.stack.length c >>= fun i =>
            if ¬ S.isSwapReachable i then
              index S.stack.length c >>= fun i =>
                Except.error (Error.blocked (↑(S.depthOf i) - MAX_SWAP_DEPTH))
            else S.swapWith c >>= fun st => buildBottomUp.loop (c + 1) st
        else buildBottomUp.loop (c + 1) S) := by
  have hl := h.length
  refine Sim.index_bind hl rfl fun i i' hi => ?_
  refine Sim.requires (not_congr (h.isFinal_fin i i' hi)) fun _ => ?_
  have hc := i'.isLt
  apply Sim.ite (by constructor <;> intro _ <;> omega)
  · intro _
    refine Sim.index_bind hl rfl fun j j' hj => ?_
    apply Sim.ite (not_congr (h.isSwapReachable j j' hj))
    · exact fun _ => Sim.index_bind hl rfl fun _ _ _ => Sim.error _ _
    · exact fun _ => Sim.bind (h.swapWith c) fun L' S' h' => hrec L' S' h'
  · exact fun _ => hrec L S h

theorem swapDestinations_length {s n : State source target spills} {x y : ℕ}
    (hrun : s.swapDestinations x y = .ok n) : n.stack.length = s.stack.length := by
  obtain ⟨_, _, rfl⟩ := swapDestinations_ok hrun
  rfl

-- The loop at offset pre.length + c on L does what the loop at offset c does on S.
theorem loop_lift (c : ℕ) (L : State source' (pre ++ target) spills) (S : State source target spills)
    (h : Lifted pre L S) :
    Sim (LoopRel pre) (buildBottomUp.loop (pre.length + c) L) (buildBottomUp.loop c S) := by
  rw [buildBottomUp.loop.eq_def (pre.length + c), buildBottomUp.loop.eq_def c]
  simp only [except_error_bind, throw, throwThe,
    MonadExceptOf.throw, ite_true]
  have hl := h.length
  have hn : (pre ++ target).length = pre.length + target.length := List.length_append
  apply Sim.ite (by omega)
  · exact fun _ => Sim.ok ⟨h.stack, h.count⟩
  intro hc
  have hrec : ∀ (L' : State source' (pre ++ target) spills) (S' : State source target spills),
      Lifted pre L' S' →
      Sim (LoopRel pre) (buildBottomUp.loop (pre.length + c + 1) L')
        (buildBottomUp.loop (c + 1) S') :=
    fun L' S' h' => loop_lift (c + 1) L' S' h'
  refine Sim.ite_index (by omega) hl rfl (fun i i' hi => h.isFinal_fin i i' hi)
    (fun _ => hrec L S h) ?_
  apply Sim.ite (by rw [h.pending])
  · intro hz r hr
    by_cases hq : S.stack.length = target.length ∧ ∀ i, (S.destinationOf i).isSome
    · have hp := h.complete hq
      rw [requires_of_true _ hq.1, except_ok_bind,
        requires_of_true (∀ i, (S.destinationOf i).isSome) hq.2, except_ok_bind] at hr
      rw [requires_of_true _ hp.1, except_ok_bind,
        requires_of_true (∀ i, (L.destinationOf i).isSome) hp.2, except_ok_bind]
      cases hperm : Shuffler.Permute.permute spills S.stack
          (S.mapping.toPermutation hq.1 hq.2) with
      | error err =>
        rw [hperm] at hr
        cases hr
      | ok result =>
        obtain ⟨res, tr⟩ := result
        rw [hperm] at hr
        cases hr
        obtain ⟨tr', hL, hcount⟩ := permute_lift_eq spills h.stack _ _
          (h.permLift hp.1 hp.2 hq.1 hq.2) hperm
        rw [hL]
        refine ⟨_, rfl, rfl, ?_⟩
        dsimp only
        rw [swapCount_concat, swapCount_concat, hcount, h.count]
    · by_cases hq1 : S.stack.length = target.length
      · rw [requires_of_true _ hq1, except_ok_bind] at hr
        rw [requires_of_false (fun hb => hq ⟨hq1, hb⟩), except_error_bind] at hr
        cases hr
      · rw [requires_of_false hq1, except_error_bind] at hr
        cases hr
  intro hz
  have hs := h.urgentScan c
  unfold urgentScanOf at hs
  simp only [bind_pure, except_error_bind, throw, throwThe,
    MonadExceptOf.throw] at hs
  refine Sim.bind hs ?_
  rintro _ uS rfl
  apply Sim.dite (by
    rw [Option.isSome_map, hl]
    exact and_congr Iff.rfl (and_congr (by cases uS <;> simp) (by omega)))
  · intro _ hq
    rw [Option.get_map]
    refine Sim.attach (h.generate _ _ rfl) fun a b hab => ?_
    have hgen := b.property
    exact loop_lift c a.val b.val hab
  intro _ _
  refine Sim.ite_index (by rw [Option.isNone_map, hl, hn]; exact and_congr Iff.rfl (by omega)) hn hl
    (fun i i' hi => by
      have hp : (L.positionOf i).isNone = (S.positionOf i').isNone := by
        simpa using congrArg Option.isNone (h.positionOf i i' hi)
      rw [hp, hl]
      exact and_congr Iff.rfl (by omega)) ?_ ?_
  · intro _
    refine Sim.attach (h.generate _ _ hl) fun a b hab => ?_
    have hgen := b.property
    exact loop_lift c a.val b.val hab
  refine Sim.index_bind hn rfl fun d d' hd => ?_
  cases hpS : S.positionOf d' with
  | none =>
    rw [h.positionOf_none d d' hd hpS]
    refine Sim.bind (h.generate _ _ rfl) fun L2 S2 h2 => ?_
    refine Sim.index_bind h2.length rfl fun i i' hi => ?_
    apply Sim.ite (h2.isFinal_fin i i' hi)
    · exact fun _ => hrec L2 S2 h2
    · exact fun _ => h2.tail c hrec
  | some b =>
    obtain ⟨bL, hbL, hbv⟩ := h.positionOf_some d d' hd hpS
    rw [hbL]
    refine Sim.requires (by omega) fun _ => ?_
    refine Sim.bind_of_eq (h.slotAt c) fun v _ => Sim.bind_of_eq (h.slotAt_fin bL b hbv) fun w _ => ?_
    apply Sim.ite Iff.rfl
    · intro _
      refine Sim.bind_of_eq (h.slotAt c) fun v _ =>
        Sim.bind_of_eq (h.slotAt_fin bL b hbv) fun w _ => ?_
      refine Sim.requires Iff.rfl fun _ => ?_
      exact Sim.bind (h.swapDestinations _ _ _ _ rfl hbv) fun L' S' h' => hrec L' S' h'
    intro _
    rw [index_eq bL, index_eq b, except_ok_bind, except_ok_bind]
    have hs := h.copyScan bL b hbv
    simp only [bind_pure] at hs
    refine Sim.bind hs ?_
    rintro _ pS rfl
    refine Sim.bind_of_eq (h.slotAt pS) fun v _ =>
      Sim.bind_of_eq (h.slotAt_fin bL b hbv) fun w _ => ?_
    refine Sim.requires Iff.rfl fun _ => ?_
    refine Sim.bind (h.swapDestinations _ _ _ _ rfl hbv).with_eq fun L2 S2 ⟨h2, hsd⟩ => ?_
    have hS2 := swapDestinations_length hsd
    have hb := b.isLt
    have hl2 := h2.length
    apply Sim.ite (by omega)
    · exact fun _ => hrec L2 S2 h2
    intro _
    apply Sim.ite (by constructor <;> intro _ <;> omega)
    · intro _
      refine Sim.index_bind hl2 rfl fun j j' hj => ?_
      apply Sim.ite (not_congr (h2.isSwapReachable j j' hj))
      · exact fun _ => Sim.index_bind hl2 rfl fun _ _ _ => Sim.error _ _
      · exact fun _ => Sim.bind (h2.swapWith pS) fun L3 S3 h3 => h3.tail c hrec
    · exact fun _ => h2.tail c hrec
termination_by (target.length - c, S.pending_generations)
decreasing_by
  all_goals first | exact Prod.Lex.left _ _ (by omega) | skip
  all_goals
    apply Prod.Lex.right
    rw [(generate_counts _ _ _ hgen).pending]
    omega

--- Lift theorem ----------------------------------------------------------------------------------

-- Slots of pre are at their own destinations. The other positions shift by pre.length.
theorem positionOf_liftState (pre : Stack) (s : State source target spills) (j : ℕ) :
    (liftState pre s).positionOfNat j =
      if j < pre.length then some j else (s.positionOfNat (j - pre.length)).map (pre.length + ·) := by
  by_cases hj : j < (pre ++ target).length
  · have hm : ∀ k : Fin (pre ++ target).length, ((liftState pre s).mapping.symm k).map Fin.val =
        if h : k.val < pre.length then some k.val
        else ((s.mapping.symm ⟨k.val - pre.length, by have := k.isLt; simp at this; omega⟩).map
          Fin.val).map (pre.length + ·) := by
      intro k
      show ((liftMap pre.length s.mapping (by simp [liftState]) (by simp)).symm k).map Fin.val = _
      rw [liftMap_symm_apply]
      split <;> simp [Option.map_map, Function.comp_def]
    have hj2 : ¬ j < pre.length → j - pre.length < target.length := by simp at hj; omega
    simp only [State.positionOfNat, State.positionOf, hj, ↓reduceDIte, hm]
    split
    · rfl
    · simp [hj2 ‹_›]
  · have hj2 : ¬ j < pre.length ∧ ¬ j - pre.length < target.length := by simp at hj; omega
    simp only [State.positionOfNat, hj, ↓reduceDIte, hj2]
    simp

-- liftState is Lifted when every target slot of s is available.
theorem lifted_liftState (pre : Stack) (s : State source target spills)
    (havail : ∀ i, s.isAvailable i) : Lifted pre (liftState pre s) s where
  stack := rfl
  pending := rfl
  count := swapCount_liftTrace pre s.trace
  low j hj := by simp [positionOf_liftState, hj]
  position j := by simp [positionOf_liftState]
  copies v hv hg hs := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have ha := havail ⟨i, hi⟩
    simp only [State.isAvailable, Stack.shallowestCopyPosition_isSome, Fin.getElem_fin] at ha
    exact (ha.resolve_left hg).resolve_left hs

-- Offsets below pre.length are final, so the loop skips them.
theorem loop_skip {pre : Stack} {L : State source' (pre ++ target) spills}
    {S : State source target spills} (h : Lifted pre L S) (j : ℕ) (hj : j < pre.length) :
    buildBottomUp.loop j L = buildBottomUp.loop (j + 1) L := by
  have hj' : ¬ j ≥ (pre ++ target).length := by simp; omega
  have hjl : j < L.stack.length := by rw [h.length]; omega
  rw [buildBottomUp.loop.eq_def j]
  simp_loop
  rw [ite_eq_right hj', ite_eq_left hjl, index_eq ⟨j, hjl⟩, except_ok_bind,
    ite_eq_left ((L.isFinal_iff ⟨j, hjl⟩).mpr (h.isFinal_low j hj))]

-- The loop passes over the offsets below pre.length.
theorem loop_low {pre : Stack} {L : State source' (pre ++ target) spills}
    {S : State source target spills} (h : Lifted pre L S) :
    ∀ d ≤ pre.length, buildBottomUp.loop (pre.length - d) L = buildBottomUp.loop pre.length L
  | 0, _ => rfl
  | d + 1, hd => by
    rw [loop_skip h _ (by omega), show pre.length - (d + 1) + 1 = pre.length - d by omega]
    exact loop_low h d (by omega)

-- BBU succeeds on the lift with the same SWAP count.
theorem buildBottomUp_lift (pre : Stack) (s : State source target spills) (hv : s.Valid)
    {res : Stack} {tr : Trace spills source res} (hs : buildBottomUp s hv = .ok ⟨res, tr⟩) :
    ∃ tr', buildBottomUp (liftState pre s) (liftState_valid pre s hv) = .ok ⟨pre ++ res, tr'⟩ ∧
      tr'.swapCount = tr.swapCount := by
  have h := lifted_liftState pre s hv.available
  have hr := loop_eq_of_ok hs
  obtain ⟨⟨resL, trL⟩, ha, ha1, ha2⟩ := loop_lift 0 (liftState pre s) s h _ hr
  have e := loop_low h pre.length le_rfl
  rw [Nat.sub_self] at e
  rw [Nat.add_zero] at ha
  dsimp only at ha1 ha2
  subst ha1
  have hlen : res.length = target.length := by
    unfold buildBottomUp at hs
    rw [hr, except_ok_bind] at hs
    by_contra hne
    simp [requires, hne, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at hs
  refine ⟨trL, ?_, ha2⟩
  unfold buildBottomUp
  rw [e, ha, except_ok_bind]
  dsimp only
  rw [requires_of_true _ (by simp [hlen] : (pre ++ res).length = (pre ++ target).length),
    except_ok_bind]
  rfl

-- BBU on a Valid state, lifted by any pre, stays Valid and adds the same number of SWAPs.
theorem lift_succeeds (pre : Stack) (s : State source target spills) (hv : s.Valid)
    {res : Stack} {tr : Trace spills source res} (hs : buildBottomUp s hv = .ok ⟨res, tr⟩)
    {count : ℕ} (hc : tr.swapCount = s.trace.swapCount + count) :
    ∃ hv' : (liftState pre s).Valid, ∃ tr',
      buildBottomUp (liftState pre s) hv' = .ok ⟨pre ++ res, tr'⟩ ∧
        tr'.swapCount = (liftState pre s).trace.swapCount + count := by
  obtain ⟨tr', hs', hc'⟩ := buildBottomUp_lift pre s hv hs
  refine ⟨liftState_valid pre s hv, tr', hs', ?_⟩
  rw [hc', hc]
  exact congrArg (· + count) (swapCount_liftTrace pre s.trace).symm

-- Slots below a state keep its SWAP count.
theorem swapCounts_lift (pre : Stack) (h : count ∈ swapCounts n k) :
    count ∈ swapCounts (pre.length + n) k := by
  obtain ⟨source, target, spills, initial, hv, result, trace, hk, hn, hrun, hc⟩ := h
  obtain ⟨hv', trace', hrun', hc'⟩ := lift_succeeds pre initial hv hrun hc
  exact ⟨_, _, _, liftState pre initial, hv', _, trace', hk, by simp [liftState, hn], hrun', hc'⟩

end Shuffler.Optimality.BBU
