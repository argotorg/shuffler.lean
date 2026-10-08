import Shuffler.BuildBottomUp.Optimality.Theorems
import Tests.BuildBottomUpObservations

open Shuffler Shuffler.BuildBottomUp Shuffler.Optimality.BBU

namespace OptimalityWindowTests

-- The window bound U for 3 ≤ n ≤ 17 and k ≥ 1.
private def U (n k : Nat) : Nat := 2 * (n - 1) + 2 * k - 2

-- Production BBU swap count of a state; an error keeps its Error value.
private def count (s : State source target spills) : Except Error Nat :=
  (BuildBottomUpTestSupport.runIfValid s).map (·.2.swapCount)

-- The three fields of `State.Valid`, decided.
private def valid (s : State source target spills) : Bool :=
  decide (s.stack.length + s.pending_generations = target.length) &&
  decide (s.mapping.unmapped_target_slots = s.pending_generations) &&
  decide (∀ i, s.isAvailable i)

-- The state has n slots and k pending generations, it is valid, and BBU emits c swaps.
private def check (s : State source target spills) (n k c : Nat) : Bool :=
  s.stack.length == n && s.pending_generations == k && valid s && count s == .ok c

/-! Family C: k ∈ {1, 2} for every n from 3 to 17. -/

#guard (List.range 15).all fun i => let n := i + 3
  check (convState n 1) n 1 (U n 1) && check (convState n 2) n 2 (U n 2)
#guard check (convState 3 1) 3 1 4 && check (convState 3 2) 3 2 6
#guard check (convState 17 1) 17 1 32 && check (convState 17 2) 17 2 34
#guard (convState 3 1).stack = [.Var ⟨3⟩, .Var ⟨0⟩, .Var ⟨2⟩]
#guard (convState 4 1).stack = [.Var ⟨3⟩, .Var ⟨4⟩, .Var ⟨0⟩, .Var ⟨1⟩]
#guard (convState 6 2).stack = [.Var ⟨2⟩, .Var ⟨3⟩, .Var ⟨5⟩, .Var ⟨6⟩, .Var ⟨0⟩, .Var ⟨1⟩]

/-! Family D: k = 3 for every n from 4 to 15. -/

#guard (List.range 12).all fun i => let n := i + 4; check (dState n) n 3 (U n 3)
#guard check (dState 4) 4 3 10 && check (dState 15) 15 3 32
#guard (dState 4).stack = [.Var ⟨2⟩, .Var ⟨0⟩, .Var ⟨5⟩, .Var ⟨1⟩]

/-! Family W: n ∈ {15, 16, 17} and k ≥ 3. -/

#guard (List.range 40).all fun i => let k := i + 3
  check (windowState 17 k) 17 k (U 17 k) && check (windowState 16 k) 16 k (U 16 k)
#guard (List.range 40).all fun i => let k := i + 4
  !(k % 16 = 2 || k % 16 = 3) → check (windowState 15 k) 15 k (U 15 k)
#guard check (windowState 17 3) 17 3 36
#guard check (windowState 15 4) 15 4 34 && check (windowState 15 17) 15 17 60
#guard check (windowState 15 20) 15 20 66

/-! `WindowAttained` covers every n from 15 to 17 except n = 15 with k mod 16 ∈ {2, 3},
and every n ≥ 4 for k ≤ 3. -/

#guard decide (WindowAttained 3 1) && decide (WindowAttained 3 2) && decide (WindowAttained 4 3)
#guard decide (WindowAttained 16 18) && decide (WindowAttained 17 19) && decide (WindowAttained 15 20)
#guard !decide (WindowAttained 3 3) && !decide (WindowAttained 14 4) && !decide (WindowAttained 4 4)
#guard !decide (WindowAttained 15 18) && !decide (WindowAttained 15 19) && !decide (WindowAttained 15 34)

/-! Negative cases. -/

-- At n = 15 and k mod 16 ∈ {2, 3} a shared value of W sits in a dropped slot: no copy
-- remains, so the state is not valid.
#guard !valid (windowState 15 18) && !valid (windowState 15 19)
#guard !valid (windowState 15 34) && !valid (windowState 15 35)
-- Family C with k = 3 has a second hole and costs less than U.
#guard (List.range 15).all fun i => let n := i + 3
  valid (convState n 3) && match count (convState n 3) with
    | .ok c => c < U n 3 | .error _ => false
-- Family D needs n ≥ 4: at n = 3 slot 0 is final.
#guard (dState 3).stack = [.Var ⟨0⟩, .Var ⟨4⟩, .Var ⟨1⟩]
#guard match count (dState 3) with | .ok c => c < U 3 3 | .error _ => false
-- No count differs from U by one on the families.
#guard (List.range 15).all fun i => let n := i + 3
  count (convState n 1) != .ok (U n 1 + 1) && count (convState n 1) != .ok (U n 1 - 1)

/-! n = 15, k = 19: a state outside the families attains U = 64, so `WindowAttained` is a
sufficient condition only. The state comes from a random search. -/

private def mkMapping (n N : Nat) (dests : List Nat) : Option (Mapping n N) :=
  (List.finRange n).foldlM (init := (⊥ : Mapping n N)) fun m p =>
    match dests[p.val]? with
    | none => none
    | some d =>
      if hd : d < N then
        if hp : m p = none then
          if hs : m.symm ⟨d, hd⟩ = none then some (m.bind p ⟨d, hd⟩ hp hs) else none
        else none
      else none

private def stateOf (source target : Stack) (spills : SpillSet) (dests : List Nat) :
    Option (State source target spills) := do
  let m ← mkMapping source.length target.length dests
  some { planned_mapping := m, stack := source, trace := .Lit source, mapping := m,
         pending_generations := target.length - source.length }

private def v (i : Nat) : Value := .Var ⟨i⟩
private def l (i : Nat) : Value := .Lit (Fin.ofNat _ i)

private def source19 : Stack := [0, 1, 2, 3, 13, 0, 6, 7, 8, 3, 10, 7, 6, 8, 14].map v
private def target19 : Stack :=
  [v 1, v 3, v 7, v 10, v 6, v 14, v 8, v 8, v 13, v 2, v 0, v 0, v 7, v 3, v 6, l 1015,
   v 13, v 3, l 1018, l 1019, l 1020, l 1021, l 1022, l 1023, v 2, l 1025, l 1026, l 1027,
   l 1028, l 1029, v 11, v 6, l 1032, v 13]
private def spills19 : SpillSet := ({2, 5, 6, 7, 9, 11, 12} : Finset Nat).image VarId.mk
private def dests19 : List Nat := [11, 0, 9, 1, 8, 10, 14, 12, 6, 13, 3, 2, 4, 7, 5]

#guard match stateOf source19 target19 spills19 dests19 with
  | some s => check s 15 19 (U 15 19)
  | none => false

end OptimalityWindowTests
