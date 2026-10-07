import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightSolver.Source
import Shuffler.Optimality.BirthPlacement.Word.Cached

namespace Tests.OptimalitySourceWeightAssignment

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement SourceLazy

private def exampleWord : Fin 6 → Nat := ![1, 0, 0, 1, 1, 1]
private def exampleTarget : Fin 6 → Nat := ![0, 1, 1, 1, 1, 0]
private def exampleAssignment : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 4, 3]
  invFun := ![2, 3, 0, 5, 4, 1]
  left_inv := by decide
  right_inv := by decide
private def exampleDual : WeightDual 6 where
  row := ![0, 1, 1, 0, 0, 1]
  column := ![0, 1, 1, 0, 0, 0]

example : exampleDual.Valid 2 3 exampleWord exampleTarget := by decide
example : exampleDual.bound = weightScore 3 exampleAssignment := by decide
example (other : Equiv.Perm (Fin 6))
    (hallowed : ∀ index, EndpointAllowed 2 3 exampleWord exampleTarget index (other index)) :
    weightScore 3 exampleAssignment ≤ weightScore 3 other :=
  exampleDual.minimum (by decide) (by decide) other hallowed

private def sourcePlan : SourcePlan ∅ [.Lit 1, .Lit 0, .Lit 2] [.Lit 0, .Lit 1, .Lit 2] where
  source_length := by decide
  assignment := Equiv.swap 0 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun index => Fin.elim0 index
  available := fun index => Fin.elim0 index

private def sourceDual : WeightDual 3 where
  row := ![2, 2, 0]
  column := fun _ => 0

example : MinimalWeightForWord sourcePlan :=
  WeightDual.minimalWeightForWord (target := [.Lit 0, .Lit 1, .Lit 2])
    sourceDual sourcePlan (by decide) (by decide)

#guard (WeightSolver.solve 2 3 exampleWord exampleTarget).map
  (fun result => weightScore 3 result.assignment) = some 5
#guard (WeightSolver.minimize sourcePlan).map
  (fun result => weightScore 3 result.plan.assignment) = some 4

-- The production min-E function keeps the early pin. That does not minimize W.
private theorem exampleBalanced : Word.Balanced exampleWord exampleTarget :=
  Word.balanced_of_matching exampleAssignment (by decide)
#guard (Word.cachedOptimal 2 exampleWord exampleTarget exampleBalanced) 3 = 3
#guard weightScore 3 (Word.cachedOptimal 2 exampleWord exampleTarget exampleBalanced) = 7

private def pinnedAllowed (before after : Fin 6) : Prop :=
  EndpointAllowed 2 3 exampleWord exampleTarget before after ∧ (before = 3 ↔ after = 3)
private def pinnedDual : WeightDual 6 where
  row := ![1, 1, 1, 0, 1, 2]
  column := ![0, 1, 0, 0, -1, 0]
private theorem pinnedValid : pinnedDual.ValidOn 3 pinnedAllowed := by
  unfold WeightDual.ValidOn pinnedAllowed
  decide

-- Even the best completion of pin 3 costs at least six.
example (other : Equiv.Perm (Fin 6))
    (hallowed : ∀ index, EndpointAllowed 2 3 exampleWord exampleTarget index (other index))
    (hpin : other 3 = 3) : 6 ≤ weightScore 3 other := by
  have he := pinnedDual.bound_le_of_edges pinnedValid other (fun index =>
    ⟨hallowed index, ⟨fun h => h ▸ hpin, fun h => other.injective (h.trans hpin.symm)⟩⟩)
  have hb : pinnedDual.bound = 6 := by decide
  rw [hb] at he
  exact_mod_cast he

private def embeddedWord (i : Fin 41) : Nat :=
  match i.val with
  | 0 | 24 | 32 | 40 => 1
  | 8 | 16 => 0
  | _ => i.val + 2
private def embeddedTarget (i : Fin 41) : Nat :=
  match i.val with
  | 8 | 16 | 24 | 32 => 1
  | 0 | 40 => 0
  | _ => i.val + 2
private def embeddedAssignment : Equiv.Perm (Fin 41) :=
  Equiv.swap 0 16 * Equiv.swap 8 40 * Equiv.swap 40 24
private theorem embeddedBalanced : Word.Balanced embeddedWord embeddedTarget :=
  Word.balanced_of_matching embeddedAssignment (by decide)

#guard (Word.cachedOptimal 16 embeddedWord embeddedTarget embeddedBalanced) 24 = 24
#guard weightScore 17 (Word.cachedOptimal 16 embeddedWord embeddedTarget embeddedBalanced) = 7
#guard (WeightSolver.solve 16 17 embeddedWord embeddedTarget).map
  (fun result => weightScore 17 result.assignment) = some 5

-- Empty inputs, no source, and the initial-top boundary.
#guard (WeightSolver.solve 16 0 (Fin.elim0 : Fin 0 → Nat) Fin.elim0).map
  (fun result => weightScore 0 result.assignment) = some 0
#guard (WeightSolver.solve 16 0 (![1, 0] : Fin 2 → Nat) ![0, 1]).map
  (fun result => weightScore 0 result.assignment) = some 2
#guard (WeightSolver.solve 16 1 (![1, 0] : Fin 2 → Nat) ![0, 1]).map
  (fun result => weightScore 1 result.assignment) = some 2
#guard (WeightSolver.solve 0 2 (![0, 1] : Fin 2 → Nat) ![0, 1]).map
  (fun result => weightScore 2 result.assignment) = some 0

-- Frozen mismatch, a failed deadline, and unequal value counts.
#guard (WeightSolver.solve 0 2 (![1, 0] : Fin 2 → Nat) ![0, 1]).isNone
#guard (WeightSolver.solve 0 0 (![1, 0] : Fin 2 → Nat) ![0, 1]).isNone
#guard (WeightSolver.solve 16 0 (![0, 0] : Fin 2 → Nat) ![0, 1]).isNone

-- The checker rejects invalid inverses, invalid prices, and a nonminimum map.
#guard (WeightSolver.checkedPermutation 2 #[0, 0] #[0, 1]).isNone
#guard (WeightSolver.checkedPermutation 2 #[0] #[0, 1]).isNone
#guard (WeightSolver.checkedPermutation 2 #[0, 2] #[0, 1]).isNone
#guard (WeightSolver.check 2 3 exampleWord exampleTarget exampleAssignment
  (⟨fun _ => 100, fun _ => 0⟩ : WeightDual 6)).isNone
#guard (WeightSolver.check 2 3 exampleWord exampleTarget
  (Word.cachedOptimal 2 exampleWord exampleTarget exampleBalanced) exampleDual).isNone

-- This oracle enumerates all endpoint permutations. It does not use network paths.
private def exhaustiveMinimum (reach height : Nat) (word target : Fin size → Nat) : Option Nat :=
  (List.finRange size).permutations.foldl (fun best permutation =>
    if (List.finRange size).all (fun index =>
        decide (EndpointAllowed reach height word target index (permutation.getD index.val index))) then
      let cost := ((List.finRange size).map fun index =>
        edgeWeight height index (permutation.getD index.val index)).sum
      some (match best with | none => cost | some old => min old cost)
    else best) none

-- All binary words of length three, all source heights, and reaches zero to two.
#guard (List.range 8).all (fun first => (List.range 8).all (fun second =>
  (List.range 4).all (fun height => (List.range 3).all (fun reach =>
    let word : Fin 3 → Nat := fun i => first / 2 ^ i.val % 2
    let target : Fin 3 → Nat := fun i => second / 2 ^ i.val % 2
    (WeightSolver.solve reach height word target).map (fun result => weightScore height result.assignment) ==
      exhaustiveMinimum reach height word target))))

private def usesReversePath (graph : WeightSolver.Network) (count : Nat) : Bool :=
  ((List.range count).foldlM (fun (flow, used) _ => do
    let (labels, _) ← WeightSolver.shortest graph flow
    let path ← WeightSolver.path graph labels graph.outgoing.size graph.sink
    let next ← WeightSolver.augment graph flow
    return (next, used || path.any (fun index => graph.edges[index]!.capacity == 0)))
      (WeightSolver.initial graph, false)).any Prod.snd

#guard usesReversePath (WeightSolver.network 2 3 exampleWord exampleTarget) 6

#print axioms WeightDual.minimum
#print axioms WeightDual.minimalWeightForWord
#print axioms WeightSolver.Solution.minimum
#print axioms WeightSolver.reassign_minimum

end Tests.OptimalitySourceWeightAssignment
