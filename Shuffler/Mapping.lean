import Mathlib.Data.PEquiv
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

-- A Mapping is a partial bijection between source positions and target positions.
abbrev Mapping (source_len target_len : ℕ) := PEquiv (Fin source_len) (Fin target_len)

namespace Mapping

variable {source_len target_len : ℕ}

-- pop removes the top source position and its binding, if any; all other bindings stay unchanged.
def pop : (mapping : Mapping (source_len + 1) target_len) → Mapping source_len target_len
| ⟨toFun, invFun, hinv⟩ => by
  -- Restrict toFun to the remaining source positions.
  let toFun' := fun (x : Fin source_len) => toFun x.castSucc
  -- Keep each target's inverse binding below the removed top; return none otherwise.
  let invFun' : Fin target_len → Option (Fin source_len) := fun x =>
    (invFun x).bind fun i =>
      if h : i.val < source_len then some ⟨i.val, h⟩ else none
  refine ⟨toFun', invFun', ?_⟩
  simp only [toFun', invFun', ← hinv]
  intro a b
  cases invFun b <;> simp +contextual [Fin.ext_iff]

-- bind connects an unbound source to an unbound target and keeps all existing bindings unchanged.
def bind (mapping : Mapping source_len target_len) (p : Fin source_len) (d : Fin target_len)
    (hp : mapping p = none) (hd : mapping.symm d = none) : Mapping source_len target_len where
  -- Map source position p to some d and keep all other results unchanged.
  toFun := Function.update mapping p (some d)
  -- Map target position d to some p and keep all other results unchanged.
  invFun := Function.update mapping.symm d (some p)
  inv a b := by
    simp only [Function.update_apply]
    split_ifs with ha hb hb
    · subst ha hb; simp
    · subst ha; simp [← PEquiv.eq_some_iff, hd, Ne.symm hb]
    · subst hb; simp [PEquiv.eq_some_iff, hp, Ne.symm ha]
    · exact PEquiv.mem_iff_mem mapping

-- Exchange the destinations of two source positions, including unbound positions.
def swapDestinations (mapping : Mapping source_len target_len) (a b : Fin source_len) :
    Mapping source_len target_len :=
  (Equiv.swap a b).toPEquiv.trans mapping

-- push adds a new source top and binds it to an unbound target; all existing bindings stay unchanged.
def push (mapping : Mapping source_len target_len) (dst : Fin target_len)
    (hdst : mapping.symm dst = none) : Mapping (source_len + 1) target_len := by
  -- Extend the mapping with an unbound source position.
  let extended : Mapping (source_len + 1) target_len := {
    -- Preserve old forward assignments; leave the new top unbound.
    toFun := fun i =>
      if h : i.val < source_len then mapping ⟨i.val, h⟩ else none
    -- Increase the bound of each inverse index without changing its value;
    -- leave unbound destinations as none.
    invFun := fun d => (mapping.symm d).map Fin.castSucc
    inv := by
      intro i d
      split_ifs with h
      · rw [← mapping.eq_some_iff]
        cases mapping.symm d <;> simp [Fin.ext_iff]
      · cases mapping.symm d <;> simp [Fin.ext_iff]
        omega
  }
  -- Bind the top source position to dst.
  exact extended.bind (Fin.last source_len) dst
    (by simp [extended])
    (by simpa [extended, PEquiv.symm] using hdst)

-- Count the target slots that are not bound to a source slot.
def unmapped_target_slots (mapping : Mapping source_len target_len) : ℕ :=
  (Finset.univ.filter (λ j => mapping.symm j = .none)).card

-- Binding all targets forces equal lengths and binds all sources when source_len ≤ target_len.
theorem complete_of_target_total
    (mapping : Mapping source_len target_len)
    (hsize : source_len ≤ target_len)
    (htarget : ∀ j, (mapping.symm j).isSome) :
    source_len = target_len ∧ ∀ i, (mapping i).isSome := by
  let position := fun j => (mapping.symm j).get (htarget j)
  have hposition : ∀ j, mapping (position j) = some j := fun j =>
    mapping.eq_some_iff.mp (Option.some_get (htarget j)).symm
  have hinj : Function.Injective position := by
    intro j k h
    apply Option.some_injective
    rw [← hposition j, ← hposition k, h]
  have hlen : source_len = target_len :=
    Nat.le_antisymm hsize (by simpa using Fintype.card_le_of_injective position hinj)
  have hsurj : Function.Surjective position :=
    ((Fintype.bijective_iff_injective_and_card position).mpr
      ⟨hinj, by simp [hlen]⟩).2
  refine ⟨hlen, ?_⟩
  intro i
  obtain ⟨j, rfl⟩ := hsurj i
  rw [hposition j]
  rfl

-- Build a permutation when source and target lengths are equal and every source position is bound.
def toPermutation
    (mapping : Mapping source_len target_len)
    (hlen : source_len = target_len)
    (hsource : ∀ i, (mapping i).isSome) : Equiv.Perm (Fin source_len) :=
  have htarget := (complete_of_target_total mapping.symm hlen.ge hsource).2
  let equiv : Fin source_len ≃ Fin target_len := {
    toFun := fun i => (mapping i).get (hsource i)
    invFun := fun j => (mapping.symm j).get (htarget j)
    left_inv := fun i => by
      apply Option.some_injective
      rw [Option.some_get]
      exact mapping.eq_some_iff.mpr (Option.some_get (hsource i)).symm
    right_inv := fun j => by
      apply Option.some_injective
      rw [Option.some_get]
      exact mapping.eq_some_iff.mp (Option.some_get (htarget j)).symm
  }
  equiv.trans (finCongr hlen.symm)

-- The permutation sends each source position to its bound target position.
@[simp] theorem toPermutation_apply
    (mapping : Mapping source_len target_len)
    (hlen : source_len = target_len)
    (hsource : ∀ i, (mapping i).isSome)
    (i : Fin source_len) :
    some (Fin.cast hlen (mapping.toPermutation hlen hsource i)) = mapping i := by
  subst target_len
  simp [toPermutation]

-- The unbound target count is zero exactly when every target is bound.
theorem unmapped_target_slots_eq_zero (mapping : Mapping source_len target_len) :
    unmapped_target_slots mapping = 0 ↔ ∀ j, (mapping.symm j).isSome := by
  simp [unmapped_target_slots, Finset.filter_eq_empty_iff, Option.isSome_iff_ne_none]

-- Popping preserves the lookup result at every remaining source position.
@[simp] theorem pop_apply (mapping : Mapping (source_len + 1) target_len)
    (i : Fin source_len) : mapping.pop i = mapping i.castSucc := by
  rfl

-- After binding p to d, the forward lookup at p returns some d.
@[simp] theorem bind_apply (mapping : Mapping source_len target_len)
    (p : Fin source_len) (d : Fin target_len) (hp : mapping p = none)
    (hd : mapping.symm d = none) : mapping.bind p d hp hd p = some d := by
  simp [bind]

-- Binding p to d preserves forward lookups at all other source positions.
@[simp] theorem bind_apply_of_ne (mapping : Mapping source_len target_len)
    (p : Fin source_len) (d : Fin target_len) (hp : mapping p = none)
    (hd : mapping.symm d = none) (i : Fin source_len) (hi : i ≠ p) :
    mapping.bind p d hp hd i = mapping i := by
  simp [bind, hi]

-- After binding p to d, the inverse lookup at d returns some p.
@[simp] theorem bind_symm_apply (mapping : Mapping source_len target_len)
    (p : Fin source_len) (d : Fin target_len) (hp : mapping p = none)
    (hd : mapping.symm d = none) : (mapping.bind p d hp hd).symm d = some p := by
  change Function.update mapping.symm d (some p) d = _
  simp

-- Binding p to d preserves inverse lookups at all other target positions.
@[simp] theorem bind_symm_apply_of_ne (mapping : Mapping source_len target_len)
    (p : Fin source_len) (d : Fin target_len) (hp : mapping p = none)
    (hd : mapping.symm d = none) (j : Fin target_len) (hj : j ≠ d) :
    (mapping.bind p d hp hd).symm j = mapping.symm j := by
  change Function.update mapping.symm d (some p) j = _
  simp [hj]

-- Look up the source position after exchanging a and b.
@[simp] theorem swapDestinations_apply (mapping : Mapping source_len target_len)
    (a b p : Fin source_len) :
    mapping.swapDestinations a b p = mapping (Equiv.swap a b p) := by
  simp [swapDestinations, PEquiv.trans, Equiv.toPEquiv]

-- The first source position receives the second position's destination.
theorem swapDestinations_apply_left (mapping : Mapping source_len target_len)
    (a b : Fin source_len) : mapping.swapDestinations a b a = mapping b := by
  simp

-- The second source position receives the first position's destination.
theorem swapDestinations_apply_right (mapping : Mapping source_len target_len)
    (a b : Fin source_len) : mapping.swapDestinations a b b = mapping a := by
  simp

-- All other source positions keep their destinations.
theorem swapDestinations_apply_of_ne (mapping : Mapping source_len target_len)
    {a b p : Fin source_len} (ha : p ≠ a) (hb : p ≠ b) :
    mapping.swapDestinations a b p = mapping p := by
  simp [Equiv.swap_apply_of_ne_of_ne ha hb]

-- Inverse lookups exchange a and b and keep unbound targets unbound.
@[simp] theorem swapDestinations_symm_apply (mapping : Mapping source_len target_len)
    (a b : Fin source_len) (d : Fin target_len) :
    (mapping.swapDestinations a b).symm d = (mapping.symm d).map (Equiv.swap a b) := by
  rcases hd : mapping.symm d with _ | p
  · refine Option.eq_none_iff_forall_ne_some.2 fun q hq => ?_
    rw [PEquiv.eq_some_iff, swapDestinations_apply, ← PEquiv.eq_some_iff, hd] at hq
    cases hq
  · rw [Option.map_some, PEquiv.eq_some_iff, swapDestinations_apply, Equiv.swap_apply_self,
      ← PEquiv.eq_some_iff, hd]

-- A target bound to the first position becomes bound to the second position.
theorem swapDestinations_symm_of_symm_eq_left (mapping : Mapping source_len target_len)
    (a b : Fin source_len) (d : Fin target_len) (hd : mapping.symm d = some a) :
    (mapping.swapDestinations a b).symm d = some b := by
  simp [hd]

-- A target bound to the second position becomes bound to the first position.
theorem swapDestinations_symm_of_symm_eq_right (mapping : Mapping source_len target_len)
    (a b : Fin source_len) (d : Fin target_len) (hd : mapping.symm d = some b) :
    (mapping.swapDestinations a b).symm d = some a := by
  simp [hd]

-- Exchanging the same pair twice restores the mapping.
@[simp] theorem swapDestinations_swapDestinations (mapping : Mapping source_len target_len)
    (a b : Fin source_len) :
    (mapping.swapDestinations a b).swapDestinations a b = mapping := by
  simp [swapDestinations, ← PEquiv.trans_assoc, ← Equiv.toPEquiv_trans]

-- Exchanging a position with itself leaves the mapping unchanged.
theorem swapDestinations_self (mapping : Mapping source_len target_len) (a : Fin source_len) :
    mapping.swapDestinations a a = mapping := by
  simp [swapDestinations]

-- Pushing to d binds the new source top to d.
@[simp] theorem push_apply_top (mapping : Mapping source_len target_len)
    (d : Fin target_len) (hd : mapping.symm d = none) :
    push mapping d hd (Fin.last source_len) = some d := by
  simp [push]

-- Pushing preserves forward lookups at all existing source positions.
@[simp] theorem push_apply_castSucc (mapping : Mapping source_len target_len)
    (d : Fin target_len) (hd : mapping.symm d = none) (i : Fin source_len) :
    push mapping d hd i.castSucc = mapping i := by
  have hne : i.val ≠ source_len := Nat.ne_of_lt i.isLt
  simp [push, bind, Fin.ext_iff, hne, i.isLt]

-- After pushing to d, the inverse lookup at d returns the new source top.
@[simp] theorem push_symm_apply (mapping : Mapping source_len target_len)
    (d : Fin target_len) (hd : mapping.symm d = none) :
    (push mapping d hd).symm d = some (Fin.last source_len) := by
  rw [(push mapping d hd).eq_some_iff]
  exact push_apply_top mapping d hd

-- Pushing to d preserves all other targets' bindings.
@[simp] theorem push_symm_apply_of_ne (mapping : Mapping source_len target_len)
    (d : Fin target_len) (hd : mapping.symm d = none) (j : Fin target_len)
    (hj : j ≠ d) :
    (push mapping d hd).symm j =
      (mapping.symm j).map Fin.castSucc := by
  change Function.update _ d _ j = _
  simp only [Function.update_apply, ite_eq_right hj]
  rfl

-- Binding a free source to a free target preserves every existing binding.
-- For PEquiv, a ≤ b means every binding x ↦ y in a is also present in b.
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PEquiv.html#PEquiv.le_def
theorem le_bind (mapping : Mapping source_len target_len)
    (p : Fin source_len) (d : Fin target_len) (hp : mapping p = none)
    (hd : mapping.symm d = none) : mapping ≤ mapping.bind p d hp hd := by
  intro i j hij
  by_cases hi : i = p
  · subst i
    simp [hp] at hij
  · simpa [hi] using hij

-- Popping after pushing restores the original mapping.
@[simp] theorem pop_push (mapping : Mapping source_len target_len)
    (d : Fin target_len) (hd : mapping.symm d = none) :
    (push mapping d hd).pop = mapping := by
  apply PEquiv.ext
  intro i
  rw [pop_apply]
  exact push_apply_castSucc mapping d hd i

-- A target that was unbound remains unbound after popping.
@[simp] theorem pop_symm_apply_of_none (mapping : Mapping (source_len + 1) target_len)
    (d : Fin target_len) (hd : mapping.symm d = none) : mapping.pop.symm d = none := by
  change (mapping.symm d).bind _ = none
  rw [hd]
  rfl

-- Popping unbinds the target that was bound to the source top.
@[simp] theorem pop_symm_apply_of_top (mapping : Mapping (source_len + 1) target_len)
    (d : Fin target_len) (hd : mapping (Fin.last source_len) = some d) :
    mapping.pop.symm d = none := by
  change (mapping.symm d).bind _ = none
  rw [mapping.eq_some_iff.mpr hd]
  simp

-- Popping a bound top and pushing to the same target restores the original mapping.
theorem push_pop (mapping : Mapping (source_len + 1) target_len)
    (d : Fin target_len) (hd : mapping (Fin.last source_len) = some d) :
    push mapping.pop d
      (pop_symm_apply_of_top mapping d hd) = mapping := by
  apply PEquiv.ext
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [hd]
  · simp

-- Binding two pairs with distinct source and target positions gives the same result in either order.
theorem bind_comm (mapping : Mapping source_len target_len)
    (p q : Fin source_len) (d e : Fin target_len)
    (hp : mapping p = none) (hq : mapping q = none)
    (hd : mapping.symm d = none) (he : mapping.symm e = none)
    (hpq : p ≠ q) (hde : d ≠ e) :
    (mapping.bind p d hp hd).bind q e
      (by simpa [hpq.symm] using hq) (by simpa [hde.symm] using he) =
    (mapping.bind q e hq he).bind p d
      (by simpa [hpq] using hp) (by simpa [hde] using hd) := by
  apply PEquiv.ext
  intro i
  simp only [bind, PEquiv.coe_mk, Function.update_apply]
  split_ifs <;> simp_all

-- Binding a free source to a free target reduces the unbound target count by one.
theorem unmapped_target_slots_bind (mapping : Mapping source_len target_len)
    (p : Fin source_len) (d : Fin target_len)
    (hp : mapping p = none) (hd : mapping.symm d = none) :
    unmapped_target_slots (mapping.bind p d hp hd) + 1 = unmapped_target_slots mapping := by
  have hset : (Finset.univ.filter fun j => (mapping.bind p d hp hd).symm j = none) =
      (Finset.univ.filter fun j => mapping.symm j = none).erase d := by
    ext j
    by_cases hj : j = d
    · subst j; simp
    · simp [hj]
  unfold unmapped_target_slots
  rw [hset]
  exact Finset.card_erase_add_one (by simp [hd])

-- Pushing reduces the unbound target count by one.
theorem unmapped_target_slots_push (mapping : Mapping source_len target_len)
    (d : Fin target_len) (hd : mapping.symm d = none) :
    unmapped_target_slots (push mapping d hd) + 1 =
      unmapped_target_slots mapping := by
  have hset : (Finset.univ.filter fun j => (push mapping d hd).symm j = none) =
      (Finset.univ.filter fun j => mapping.symm j = none).erase d := by
    ext j
    by_cases hj : j = d
    · subst j; simp
    · simp [hj]
  unfold unmapped_target_slots
  rw [hset]
  exact Finset.card_erase_add_one (by simp [hd])

-- After popping, a target is unbound exactly when it was unbound or bound to the removed top.
@[simp] theorem pop_symm_eq_none_iff (mapping : Mapping (source_len + 1) target_len)
    (d : Fin target_len) :
    mapping.pop.symm d = none ↔ mapping.symm d = none ∨ mapping (Fin.last source_len) = some d := by
  rw [← mapping.eq_some_iff]
  change (mapping.symm d).bind _ = none ↔ _
  cases h : mapping.symm d with
  | none => simp
  | some i =>
    simp [Fin.ext_iff]
    have hi := i.isLt
    omega

-- Popping an unbound source top preserves the unbound target count.
theorem unmapped_target_slots_pop_of_unbound (mapping : Mapping (source_len + 1) target_len)
    (htop : mapping (Fin.last source_len) = none) :
    unmapped_target_slots mapping.pop = unmapped_target_slots mapping := by
  unfold unmapped_target_slots
  congr 1
  ext d
  simp [htop]

-- Popping a bound source top increases the unbound target count by one.
theorem unmapped_target_slots_pop_of_bound (mapping : Mapping (source_len + 1) target_len)
    (d : Fin target_len) (htop : mapping (Fin.last source_len) = some d) :
    unmapped_target_slots mapping.pop = unmapped_target_slots mapping + 1 := by
  have h := unmapped_target_slots_push
    mapping.pop
    d (pop_symm_apply_of_top mapping d htop)
  rw [push_pop mapping d htop] at h
  exact h.symm

-- Pushing to two distinct targets gives different mappings when the order is reversed.
theorem push_push_ne (mapping : Mapping source_len target_len)
    (d e : Fin target_len) (hd : mapping.symm d = none) (he : mapping.symm e = none)
    (hde : d ≠ e) :
    push (push mapping d hd) e
      (by simp [hde.symm, he]) ≠
    push (push mapping e he) d
      (by simp [hde, hd]) := by
  intro h
  have hlookup := congrArg
    (fun mapping : Mapping (source_len + 1 + 1) target_len =>
      mapping (Fin.last source_len).castSucc) h
  simp only [push_apply_castSucc, push_apply_top, Option.some.injEq] at hlookup
  exact hde hlookup

-- Popping an unbound source top and then pushing cannot restore the original mapping.
theorem push_pop_ne_of_unbound (mapping : Mapping (source_len + 1) target_len)
    (d : Fin target_len) (hd : mapping.symm d = none)
    (htop : mapping (Fin.last source_len) = none) :
    push mapping.pop d
      (pop_symm_apply_of_none mapping d hd) ≠ mapping := by
  intro h
  have hlookup := congrArg (fun mapping : Mapping (source_len + 1) target_len =>
    mapping (Fin.last source_len)) h
  simp [htop] at hlookup

-- With no source positions, every inverse lookup returns none.
@[simp] theorem symm_apply_empty (mapping : Mapping 0 target_len) (d : Fin target_len) :
    mapping.symm d = none := by
  cases h : mapping.symm d with
  | none => rfl
  | some i => exact Fin.elim0 i

-- With no source positions, the unbound target count equals the target length.
@[simp] theorem unmapped_target_slots_empty (mapping : Mapping 0 target_len) :
    unmapped_target_slots mapping = target_len := by
  simp [unmapped_target_slots, symm_apply_empty mapping]

end Mapping

@[simp] theorem Mapping.unmapped_target_slots_swapDestinations
    (mapping : Mapping source_len target_len) (a b : Fin source_len) :
    (mapping.swapDestinations a b).unmapped_target_slots = mapping.unmapped_target_slots := by
  simp [Mapping.unmapped_target_slots]

@[simp] theorem Mapping.cast_symm_val (mapping : Mapping n target_len) (h : n = m)
    (i : Fin target_len) :
    ((h ▸ mapping).symm i).map Fin.val = (mapping.symm i).map Fin.val := by
  cases h
  rfl

@[simp] theorem Mapping.unmapped_target_slots_cast (mapping : Mapping n target_len)
    (h : n = m) : (h ▸ mapping).unmapped_target_slots = mapping.unmapped_target_slots := by
  cases h
  rfl
