import Shuffler.Optimality.BirthPlacement.SourceLazy.Theorems

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

-- Each row is one token in source ++ births. Each column is one target slot.
def EndpointAllowed (reach height : Nat) (word target : Fin size → α)
    (before after : Fin size) : Prop :=
  word before = target after ∧ before.val ≤ after.val + reach ∧
    (before.val + reach + 1 < height → after = before)

instance [DecidableEq α] (reach height : Nat) (word target : Fin size → α)
    (before after : Fin size) : Decidable (EndpointAllowed reach height word target before after) := by
  unfold EndpointAllowed
  infer_instance

-- Integer row and column prices certify the minimum without enumerating assignments.
structure WeightDual (size : Nat) where
  row : Fin size → Int
  column : Fin size → Int

def WeightDual.bound (cert : WeightDual size) : Int :=
  (∑ index, cert.row index) + ∑ index, cert.column index

def WeightDual.ValidOn (cert : WeightDual size) (height : Nat)
    (allowed : Fin size → Fin size → Prop) : Prop :=
  ∀ before after, allowed before after →
    cert.row before + cert.column after ≤ edgeWeight height before after

instance (cert : WeightDual size) (height : Nat) (allowed : Fin size → Fin size → Prop)
    [DecidableRel allowed] : Decidable (cert.ValidOn height allowed) := by
  unfold WeightDual.ValidOn
  infer_instance

def WeightDual.Valid (cert : WeightDual size) (reach height : Nat)
    (word target : Fin size → α) : Prop :=
  cert.ValidOn height (EndpointAllowed reach height word target)

instance [DecidableEq α] (cert : WeightDual size) (reach height : Nat)
    (word target : Fin size → α) : Decidable (cert.Valid reach height word target) := by
  unfold WeightDual.Valid
  infer_instance

theorem WeightDual.bound_le_of_edges (cert : WeightDual size)
    (hvalid : cert.ValidOn height allowed) (assignment : Equiv.Perm (Fin size))
    (hallowed : ∀ index, allowed index (assignment index)) :
    cert.bound ≤ weightScore height assignment := by
  have he := Finset.sum_le_sum fun index (_ : index ∈ Finset.univ) =>
    hvalid index (assignment index) (hallowed index)
  rw [Finset.sum_add_distrib, Equiv.sum_comp assignment cert.column] at he
  simpa only [WeightDual.bound, weightScore_eq_sum, Nat.cast_sum] using he

theorem WeightDual.bound_le (cert : WeightDual size)
    (hvalid : cert.Valid reach height word target) (assignment : Equiv.Perm (Fin size))
    (hallowed : ∀ index, EndpointAllowed reach height word target index (assignment index)) :
    cert.bound ≤ weightScore height assignment :=
  cert.bound_le_of_edges hvalid assignment hallowed

theorem WeightDual.minimum (cert : WeightDual size)
    (hvalid : cert.Valid reach height word target)
    (hattains : cert.bound = weightScore height assignment)
    (other : Equiv.Perm (Fin size))
    (hallowed : ∀ index, EndpointAllowed reach height word target index (other index)) :
    weightScore height assignment ≤ weightScore height other := by
  have he := cert.bound_le hvalid other hallowed
  rw [hattains] at he
  exact_mod_cast he

theorem allowed_same_word (plan other : SourcePlan spills source target)
    (hword : other.births = plan.births) (index : Fin target.length) :
    EndpointAllowed 16 source.length (fun i => target[plan.assignment i])
      (fun i => target[i]) index (other.assignment index) := by
  have hw : birthWord target other.assignment = birthWord target plan.assignment :=
    other.source_append_births.symm.trans
      ((congrArg (fun births => source ++ births) hword).trans plan.source_append_births)
  have hv := congrFun (List.ofFn_inj.mp hw) index
  exact ⟨hv.symm, other.deadlines index, other.source_frozen index⟩

theorem WeightDual.minimalWeightForWord (cert : WeightDual target.length)
    (plan : SourcePlan spills source target)
    (hvalid : cert.Valid 16 source.length (fun i => target[plan.assignment i]) (fun i => target[i]))
    (hattains : cert.bound = weightScore source.length plan.assignment) :
    MinimalWeightForWord plan := by
  intro other hword
  exact cert.minimum hvalid hattains other.assignment (allowed_same_word plan other hword)

end Shuffler.Optimality.BirthPlacement.SourceLazy
