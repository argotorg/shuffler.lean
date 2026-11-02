module

public import FlatShuffler.FlatSurplusRel
import all FlatShuffler.FlatSurplusRel
public import FlatShuffler.FlatPopTest
import all FlatShuffler.FlatPopTest

@[expose] public section

/-!
Tests of `FlatSurplus.lean`, of `Map.State.removeSurplus` (`MapModel.lean`) and of `absOut`
(`FlatSurplusRel.lean`): `removeSurplus` on an empty stack, with no surplus slot, with a surplus
top, with an equal surplus slot (`swapDestinations`), with a swap (`swapWith` of the deepest
reachable slot), at the swap reach (depth 16 and 17) and with a block; the bounds of
`remove_surplus`; the agreement of the flat model and the list model on all small cases and on
deep cases; and mutants of the list model that the cases tell apart. `test/surplus_diff.sh`
compares `remove_surplus` with the PR31 model and the asm on more cases.
-/

namespace FlatShuffler.Flat.SurplusTest

open FlatShuffler FlatShuffler.Flat.PopTest

def viewB (r : EmissionOutcome × St) := (r.1, view r.2, r.2.blockedOffset, r.2.blockedExcess)

def mkT (source : List StackSlot) (n : Nat) (ds : List (Option Nat)) : St :=
  mk source ((List.range n).map var) ds

/-! ## `removeSurplus` -/

-- An empty stack, and a stack with no surplus slot: no change.
#guard viewR (removeSurplus (mkT [] 1 [])) = (.done, view (mkT [] 1 []))
#guard viewR (removeSurplus (mkT [x, y] 2 [some 1, some 0]))
  = (.done, view (mkT [x, y] 2 [some 1, some 0]))
-- The top is the shallowest surplus slot: a pop.
#guard viewR (removeSurplus (mkT [x, y] 1 [some 0, none])) = (.done, [x], words [0], words [0], 0, [Op.pop])
-- Each slot is surplus: a pop of each.
#guard viewR (removeSurplus (mkT [x, y, x] 0 [none, none, none]))
  = (.done, [], [], [], 0, [Op.pop, Op.pop, Op.pop])
-- A surplus slot equal to the top takes the destination of the top: no swap.
#guard viewR (removeSurplus (mkT [x, y, x] 2 [none, some 1, some 0]))
  = (.done, [x, y], words [0, 1], words [0, 1], 0, [Op.pop])
-- No equal slot: a swap of the top with the surplus slot, then a pop.
#guard viewR (removeSurplus (mkT [var 4, x, y] 2 [none, some 0, some 1]))
  = (.done, [y, x], words [1, 0], words [1, 0], 0, [Op.swapW 2, Op.pop])
-- The equal slot `0` is below the shallowest surplus slot `1`.
#guard viewR (removeSurplus (mkT [x, var 4, y, x] 2 [none, none, some 0, some 1]))
  = (.done, [x, y], words [1, 0], words [1, 0], 0, [Op.pop, Op.swapW 1, Op.pop])
-- The swap is with the deepest reachable surplus slot `0`, not with the shallowest `1`.
#guard viewR (removeSurplus (mkT [var 5, var 4, x, y] 2 [none, none, some 0, some 1]))
  = (.done, [y, x], words [1, 0], words [1, 0], 0, [Op.swapW 3, Op.pop, Op.swapW 1, Op.pop])
-- A surplus top is popped first, then the slot at `0` is swapped and popped.
#guard viewR (removeSurplus (mkT [x, y, x] 1 [none, some 0, none]))
  = (.done, [y], words [0], words [0], 0, [Op.pop, Op.swapW 1, Op.pop])

/-! ## The swap reach -/

-- `k` slots: the slots at `us` are surplus (`var 1000`), the others are bound in order from the
-- bottom to the target offsets `0, 1, ...`, and are `var` of their target offset.
def deepDests (k : Nat) (us : List Nat) : List (Option Nat) :=
  ((List.range k).foldl (fun (acc : List (Option Nat) × Nat) p =>
    if us.contains p then (acc.1 ++ [none], acc.2) else (acc.1 ++ [some acc.2], acc.2 + 1)) ([], 0)).1

def deep (k : Nat) (us : List Nat) : St :=
  let ds := deepDests k us
  mkT (ds.map fun | some d => var d | none => var 1000) (k - us.length) ds

#guard deepDests 4 [1] = [some 0, none, some 1, some 2]
-- Depth 16: a swap.
#guard (removeSurplus (deep 17 [0])).1 = .done
#guard (removeSurplus (deep 17 [0])).2.trace = [Op.swapW 16, Op.pop]
#guard (removeSurplus (deep 18 [1])).2.trace = [Op.swapW 16, Op.pop]
-- Depth 17 and 18: a block, with the excess over 16, and no operation.
#guard (viewB (removeSurplus (deep 18 [0]))).1 = .blocked
#guard (viewB (removeSurplus (deep 18 [0]))).2.2 = (0, 1)
#guard (removeSurplus (deep 18 [0])).2.trace = []
#guard (viewB (removeSurplus (deep 19 [0]))).2.2 = (0, 2)
#guard (viewB (removeSurplus (deep 19 [1]))).2.2 = (1, 1)
-- The block keeps the operations before it: the pop of the surplus top.
#guard (viewB (removeSurplus (deep 19 [0, 18]))).1 = .blocked
#guard (viewB (removeSurplus (deep 19 [0, 18]))).2.2 = (0, 1)
#guard (removeSurplus (deep 19 [0, 18])).2.trace = [Op.pop]
-- A reachable surplus slot comes first, and its pop brings the slot at `0` into reach.
#guard (removeSurplus (deep 18 [0, 5])).1 = .done
#guard (removeSurplus (deep 18 [0, 5])).2.trace = [Op.swapW 12, Op.pop, Op.swapW 16, Op.pop]
#guard (removeSurplus (deep 18 [0, 5])).2.size = 16

/-! ## `remove_surplus` -/

def rs (m n : Word) : Word × Option (EmissionOutcome × St) :=
  remove_surplus m n (vec [x, y, x]) (vec [y, x]) (destWords [none, some 1, some 0]) (fun _ => 0) u1 up1

#guard (rs 3 2).1 = 1
#guard match (rs 3 2).2 with
  | some r => viewR r = (.done, [x, y], words [0, 1], words [0, 1], 0, [Op.pop])
  | none => false
#guard (rs 0 0).1 = 0
-- A block is not a failure: the result is the number of operations.
#guard (rs (.ofNat 64 maxStackSize) 2).1 = 0
#guard ((rs (.ofNat 64 maxStackSize) 2).2.map fun r => (r.1, r.2.blockedOffset, r.2.blockedExcess))
  = some (.blocked, 0, .ofNat 64 (maxStackSize - 1 - 16))
-- The bounds: `m, n ≤ maxStackSize`, with no state.
#guard (rs (.ofNat 64 (maxStackSize + 1)) 2).1 = -2 ∧ (rs (.ofNat 64 (maxStackSize + 1)) 2).2.isNone
#guard (rs 3 (.ofNat 64 (maxStackSize + 1))).1 = -2 ∧ (rs 3 (.ofNat 64 (maxStackSize + 1))).2.isNone
#guard (rs (-1) 2).1 = -2
#guard (rs 3 (.ofNat 64 maxStackSize)).1 = 1

/-! ## The list model -/

#guard Map.Mapping.swapDestinations ⟨[none, some 1, some 0], [some 2, some 1]⟩ 0 2
  = ⟨[some 0, some 1, none], [some 0, some 1]⟩
#guard Map.Mapping.swapDestinations ⟨[some 1, some 0], [some 1, some 0]⟩ 0 1
  = ⟨[some 0, some 1], [some 0, some 1]⟩
#guard Map.Mapping.swapDestinations ⟨[none, none], [none]⟩ 0 1 = ⟨[none, none], [none]⟩

def init (source : List StackSlot) (n : Nat) (ds : List (Option Nat)) : Map.State :=
  Map.State.init source (Map.plan source.length n ds)

-- `M` has no `DecidableEq`.
def resO : M (Option (Nat × Nat) × Map.State) → Err ⊕ (Option (Nat × Nat) × Map.State)
  | .error e => .inl e
  | .ok s => .inr s

#guard resO (init [] 1 []).removeSurplus = .inr (none, init [] 1 [])
#guard resO (init [x, y, x] 2 [none, some 1, some 0]).removeSurplus
  = .inr (none, ⟨Map.plan 3 2 [none, some 1, some 0], [x, y], [Op.pop],
      ⟨[some 0, some 1], [some 0, some 1]⟩, 0⟩)
-- `swapWith` fails on a final slot and out of the swap reach.
#guard resO ((init [x, y] 2 [some 0, some 1]).swapWith 0 |>.map (none, ·)) = .inl .assertion
#guard resO ((init [x, y] 2 [none, some 1]).swapWith 0 |>.map (none, ·)) |>.isRight
#guard resO ((init [x, y] 2 [none, some 1]).swapWith 1 |>.map (none, ·)) = .inl .assertion
#guard resO ((init [x, y] 2 [none, some 1]).swapWith 2 |>.map (none, ·)) = .inl .assertion
#guard resO ((init ((List.range 18).map var) 0 []).swapWith 1 |>.map (none, ·)) |>.isRight
#guard resO ((init ((List.range 18).map var) 0 []).swapWith 0 |>.map (none, ·)) = .inl .assertion

/-! ## The flat model and the list model agree (`removeSurplus_abs`) -/

-- The unbound slots of the small cases: two variables, a literal and junk.
def unbound : List StackSlot := [var 0, var 1, x, .junk]

-- Each stack with the destinations `ds`: a bound slot is the variable of its target offset.
def fill : List (Option Nat) → List (List StackSlot)
  | [] => [[]]
  | some d :: ds => (fill ds).map (var d :: ·)
  | none :: ds => (fill ds).flatMap fun s => unbound.map (· :: s)

-- The small cases: `m, n ≤ k`.
def small (k : Nat) : List (List StackSlot × Nat × List (Option Nat)) :=
  (List.range (k + 1)).flatMap fun m => (List.range (k + 1)).flatMap fun n =>
    (injections m n).flatMap fun ds => (fill ds).map fun s => (s, n, ds)

-- The deep cases: 15 to 19 slots, with surplus slots at `u` and, if any, at `v > u`, and the
-- bound slots in order from the bottom or from the top. The surplus slots are `var 0`, equal to
-- the slot bound for `0`.
def deepCases : List (List StackSlot × Nat × List (Option Nat)) :=
  (List.range 5).flatMap fun i => let k := 15 + i
    (List.range k).flatMap fun u => ((none :: ((List.range k).filter (u < ·)).map some).filter
      (fun v => u < 3 ∨ v = none)).flatMap fun v =>
        let us := u :: v.toList
        let ds := deepDests k us
        let n := k - us.length
        [ds, ds.map (·.map (n - 1 - ·))].map fun ds =>
          (ds.map fun | some d => var d | none => var 0, n, ds)

def listRun (c : List StackSlot × Nat × List (Option Nat)) : M (Option (Nat × Nat) × Map.State) :=
  (init c.1 c.2.1 c.2.2).removeSurplus

def flatRun (c : List StackSlot × Nat × List (Option Nat)) : M (Option (Nat × Nat) × Map.State) :=
  absOut (Map.plan c.1.length c.2.1 c.2.2) (removeSurplus (mkT c.1 c.2.1 c.2.2))

#guard (small 3).length = 792
#guard (small 3).all fun c => resO (listRun c) = resO (flatRun c)
#guard deepCases.length = 620
#guard deepCases.all fun c => resO (listRun c) = resO (flatRun c)
-- The cases have each result: a block, a swap, an equal slot, and no failure.
#guard deepCases.any fun c => match listRun c with | .ok (some _, _) => true | _ => false
#guard (small 3).any fun c => match listRun c with
  | .ok (none, s) => s.trace.any (·.kind = Swap) | _ => false
#guard (small 3 ++ deepCases).all fun c => (resO (listRun c)).isRight

/-! ## Mutants of the list model -/

-- The list model with the swap reach `reach`, with or without the equal slot, and with the swap
-- of the deepest (`deepest`) or of the shallowest reachable surplus slot.
def mutScan (reach : Nat) (s : Map.State) : Nat → Option Nat → Option Nat → Option Nat × Option Nat
  | 0, sh, dp => (sh, dp)
  | p + 1, sh, dp =>
    if s.mapping.dest.getD p none = none then
      mutScan reach s p (if sh = none then some p else sh)
        (if s.stack.length - 1 - p ≤ reach then some p else dp)
    else mutScan reach s p sh dp

def mutLoop (reach : Nat) (equal deepest : Bool) (s : Map.State) :
    Nat → M (Option (Nat × Nat) × Map.State)
  | 0 => .ok (none, s)
  | fuel + 1 =>
    if s.stack = [] then .ok (none, s)
    else match mutScan reach s s.stack.length none none with
      | (none, _) => .ok (none, s)
      | (some sh, none) =>
        let excess := s.stack.length - 1 - sh - reach
        if excess = 0 then .error .assertion else .ok (some (sh, excess), s)
      | (some sh, some dp) =>
        let top := s.stack.length - 1
        let s1 : M Map.State :=
          if sh = top then .ok s
          else match (if equal then s.equalBelow top top else none) with
            | some e => .ok { s with mapping := s.mapping.swapDestinations e top }
            | none => s.swapWith (if deepest then dp else sh)
        (s1.bind Map.State.pop).bind (mutLoop reach equal deepest · fuel)

def mutRun (reach : Nat) (equal deepest : Bool) (c : List StackSlot × Nat × List (Option Nat)) :=
  let s := init c.1 c.2.1 c.2.2
  mutLoop reach equal deepest s s.stack.length

def allCases := small 3 ++ deepCases

-- With the parameters of `removeSurplus`, the mutant is the list model.
#guard allCases.all fun c => resO (mutRun 16 true true c) = resO (listRun c)
-- Each mutant differs from the flat model on a case.
#guard allCases.any fun c => resO (mutRun 15 true true c) ≠ resO (flatRun c)
#guard allCases.any fun c => resO (mutRun 17 true true c) ≠ resO (flatRun c)
#guard allCases.any fun c => resO (mutRun 16 false true c) ≠ resO (flatRun c)
#guard allCases.any fun c => resO (mutRun 16 true false c) ≠ resO (flatRun c)

end FlatShuffler.Flat.SurplusTest
