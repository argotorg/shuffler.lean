module

public import BbuKraken.Unit.Loop.Step
import all BbuKraken.Unit.Loop.Step
public import BbuKraken.FlatModelTest
import all BbuKraken.FlatModelTest

@[expose] public section

/-!
Tests of `Loop/Step.lean` on the states of `FlatModelTest.lean`: the budget `Bud` at the edges
(the budget 2 of `HInv.bud` is tight, the room `x` adds to the budget, and `HInv.bud` needs
`T < targetSize`), and the facts of `swapWith_pend`, `swapWith_tsize` and `generate_keep` on the
paths that are done and the paths that fail (where `generate` keeps `pend`, so `generate_keep`
needs `done`).
-/

namespace Bbu.Flat.StepTest

open Bbu Bbu.Flat.Test

instance (st : St) (T : Word) (k x : Nat) : Decidable (Bud st T k x) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ## `Bud` -/

-- One pending generation, no slot (`n = 1`, `m = 0`): the trace bound of `HInv` at `T = 0`
-- is an equality, so the budget is 2 and not 3.
def s1 : St := mk [] [x] []
#guard s1.pend = 1 ∧ s1.trace = []
#guard Bud s1 0 2 0
#guard ¬Bud s1 0 3 0
-- `n = 0`: `HInv s0 0` holds, but no budget: `HInv.bud` needs `T < targetSize`.
def s0 : St := mk [] [] []
#guard s0.targetSize = 0 ∧ s0.pend = 0 ∧ s0.trace = []
#guard ¬Bud s0 0 2 0 ∧ ¬Bud s0 0 1 0 ∧ Bud s0 0 0 0
-- `Bud.mono`: a smaller budget.
#guard Bud s1 0 1 0 ∧ Bud s1 0 0 0
-- `T = targetSize - 1`: the last iteration, `targetSize - (T + 1) = 0`, and `4 * n = 8`.
#guard Bud (mk [x, y] [x, y] [0, 1]) 1 8 0
#guard ¬Bud (mk [x, y] [x, y] [0, 1]) 1 9 0
-- The room `x` of the trace buffer adds to the budget: `x = 1` gives one operation more.
#guard Bud s1 0 3 1 ∧ ¬Bud s1 0 4 1
#guard Bud s0 0 1 1 ∧ ¬Bud s0 0 2 1

/-! ## `swapWith` keeps `pend` and `targetSize` -/

def keeps (st : St) (p : Word) : Bool :=
  (swapWith st p).2.pend == st.pend && (swapWith st p).2.targetSize == st.targetSize

-- Done.
#guard (swapWith s3 0).1 = .done ∧ keeps s3 0
#guard (swapWith (deep 18) 1).1 = .done ∧ keeps (deep 18) 1
-- Each check that fails: no slot, final, too deep, depth 0.
#guard (swapWith s3 3).1 = .assertionFailed ∧ keeps s3 3
#guard (swapWith (mk [x, y] [x, y] [0, 1]) 0).1 = .assertionFailed
  ∧ keeps (mk [x, y] [x, y] [0, 1]) 0
#guard (swapWith (deep 18) 0).1 = .assertionFailed ∧ keeps (deep 18) 0
#guard (swapWith s3 2).1 = .assertionFailed ∧ keeps s3 2
-- A state with pending generations.
#guard (swapWith (mk [x, y] [J, x, y] [2, 1]) 0).1 = .done ∧ keeps (mk [x, y] [J, x, y] [2, 1]) 0
#guard (mk [x, y] [J, x, y] [2, 1]).pend = 1

/-! ## `generate_keep` -/

def genKeeps (st : St) (t : Word) : Bool :=
  (generate st t).2.pend == st.pend - 1 && (generate st t).2.targetSize == st.targetSize

-- Done after `produce` only (push at the top, final).
#guard (generate s1 0).1 = .done ∧ genKeeps s1 0 ∧ (generate s1 0).2.pend = 0
-- Done after `produce` and `swapWith` (two operations).
def gSw : St := mk [x, y] [J, x, y] [1, 2]
#guard (generate gSw 0).1 = .done ∧ genKeeps gSw 0
#guard (generate gSw 0).2.trace.length = 2
-- Done after `produce` and `swapDestinations` (an equal slot at the offset).
def gSd : St := mk [x, y] [x, x, y] [1, 2]
#guard (generate gSd 0).1 = .done ∧ genKeeps gSd 0 ∧ (generate gSd 0).2.trace.length = 1
-- `pend = 0`: `pend - 1` wraps, and `generate_keep` gives the wrap.
#guard (generate { s1 with pend := 0 } 0).1 = .done ∧ genKeeps { s1 with pend := 0 } 0
#guard (generate { s1 with pend := 0 } 0).2.pend = -1
-- Not done: `t ≥ targetSize`. `generate` keeps `pend`, so the conclusion of `generate_keep`
-- is false: it needs `done`.
#guard (generate s1 1).1 = .assertionFailed ∧ !genKeeps s1 1
#guard (generate s1 1).2.pend = s1.pend
-- Not done: `produce` fails (an offset with a slot already).
#guard (generate (mk [x] [x] [0]) 0).1 = .assertionFailed ∧ !genKeeps (mk [x] [x] [0]) 0

end Bbu.Flat.StepTest
