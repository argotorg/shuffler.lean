module

public import Shuffler.BuildBottomUp.Defs
public meta import Shuffler.BuildBottomUp.Defs
import all Shuffler.BuildBottomUp.Defs
public import BbuKraken.Model
import all BbuKraken.Model

@[expose] public section

/-!
A differential test of the model `Bbu.buildBottomUp` against the original
`Shuffler.Emission.buildBottomUp`. The `#guard`s run when the file is built.

A value is a number, as in `bbu_harness` and `bbu_original`: 0 is a wildcard,
1 a function return label, 2 + 2 id a variable and 3 + 2 id a literal. The test
gives the same inputs to the two functions and compares all fields of the
results: the outcome (done, blocked with offset and excess, or assertion), the
stack, the destination of each slot, the position of each destination, the
pending generations and the operations.

The test does not use the definitions of the bridge (`BbuBridge.Defs`), so it
does not depend on `decode` or `Rel`.
-/

namespace BbuBridge.ModelDiff

open Shuffler Shuffler.Emission

/-! ## Inputs -/

-- `value` of `bbu_original`.
def value (k : Nat) : Value :=
  if k = 0 then .Wildcard
  else if k = 1 then .FunctionReturnLabel
  else if k % 2 = 0 then .Var ⟨(k - 2) / 2⟩
  else .Lit (Fin.ofNat _ ((k - 3) / 2))

-- `number` of `bbu_original`.
def number : Value → Nat
  | .Wildcard => 0
  | .FunctionReturnLabel => 1
  | .Var id => 2 + 2 * id.val
  | .Lit w => 3 + 2 * w.val

-- `slotOf` of `bbu_model` (`slot_of` of `bbu_harness.c`).
def slotOf (v : Nat) : Bbu.StackSlot :=
  ⟨.ofNat 32 (if v < 2 then 0 else (v - 2) / 2),
    if v = 0 then Bbu.Junk else if v = 1 then Bbu.FunctionReturnLabel else Bbu.Value,
    if v < 2 then Bbu.Unreachable else if v % 2 = 1 then Bbu.Const else 1⟩

-- The ids of the spilled variables.
def spilled : List Nat := [1]

def spills : SpillSet := (spilled.map VarId.mk).toFinset

def env (target : List Nat) : Bbu.Env :=
  ⟨target.map slotOf, fun i => if spilled.contains i then 1 else 0⟩

-- Bind each source position to its destination; none if a destination is out
-- of range or bound twice (`mapping?` of `bbu_original`).
def mapping? (m n : Nat) (dests : List Nat) : Option (Mapping m n) :=
  (List.finRange m).foldlM (fun mapping src => do
    let d ← dests[src.val]?
    if hd : d < n then
      if hs : mapping src = none then
        if hb : mapping.symm ⟨d, hd⟩ = none then some (mapping.bind src ⟨d, hd⟩ hs hb)
        else none
      else none
    else none) ⊥

/-! ## Results -/

-- The fields of a state.
structure Snap where
  stack : List Bbu.StackSlot
  dests : List (Option Nat)
  positionOf : List (Option Nat)
  pending : Nat
  ops : List Bbu.Op
  deriving DecidableEq, Repr

inductive Out where
  | done (s : Snap)
  | blocked (offset excess : Nat) (s : Snap)
  | assertion
  -- The original error `Blocked`. `buildBottomUp` returns a block as a result.
  | error
  deriving DecidableEq, Repr

def modelSnap (st : Bbu.St) : Snap :=
  ⟨st.slots.map (·.val), st.slots.map (some ·.dest), st.positionOf, st.pendingGenerations,
    st.trace⟩

def modelOut : Bbu.M Bbu.St → Out
  | .ok st => .done (modelSnap st)
  | .error (.blocked pos excess st) => .blocked pos excess (modelSnap st)
  | .error .assertion => .assertion

-- The operations of an original trace, as the C++ records them.
def ops {spills : SpillSet} {s r : Stack} : Trace spills s r → List Bbu.Op
  | .Lit _ => []
  | .Swap idx _ _ _ t => ops t ++ [⟨Bbu.Swap, .ofNat 8 idx, .junk⟩]
  | .Dup idx _ _ _ _ t => ops t ++ [⟨Bbu.Dup, .ofNat 8 idx, .junk⟩]
  | .Push v _ t => ops t ++ [⟨Bbu.Push, 0, slotOf (number v)⟩]
  | .Load id _ t => ops t ++ [⟨Bbu.Load, 0, slotOf (number (.Var id))⟩]
  | .Pop _ t => ops t ++ [⟨2, 0, .junk⟩]

def origSnap {source target : Stack} {spills : SpillSet} (s : State source target spills) : Snap :=
  ⟨s.stack.map (slotOf ∘ number), List.ofFn fun i => (s.mapping i).map Fin.val,
    List.ofFn fun j => (s.mapping.symm j).map Fin.val, s.pending_generations, ops s.trace⟩

def origOut {source target : Stack} {spills : SpillSet} :
    Except ShuffleErr (Result source target spills) → Out
  | .ok ⟨none, s⟩ => .done (origSnap s)
  | .ok ⟨some b, s⟩ => .blocked b.offset b.excess (origSnap s)
  | .error (.assertion _) => .assertion
  | .error (.Blocked _) => .error

-- The original result, or none if the inputs are not valid (`State.Valid`).
def orig (source target dests : List Nat) : Option Out :=
  let src := source.map value
  let tgt := target.map value
  match mapping? src.length tgt.length dests with
  | none => none
  | some mapping =>
    let state : State src tgt spills := {
      planned_mapping := mapping
      stack := src
      trace := .Lit src
      mapping := mapping
      pending_generations := tgt.length - src.length }
    if hsize : state.stack.length + state.pending_generations = tgt.length then
      if hpending : state.mapping.unmapped_target_slots = state.pending_generations then
        if havailable : ∀ i, state.isAvailable i then
          if hlabels : ∀ j, tgt[j].isFunctionReturnLabel → (state.mapping.symm j).isSome then
            some (origOut (buildBottomUp state ⟨hsize, hpending, havailable, hlabels⟩))
          else none
        else none
      else none
    else none

def model (source target dests : List Nat) : Out :=
  modelOut (Bbu.buildBottomUp (env target) (source.map slotOf) dests)

-- The two results of valid inputs, or none if the inputs are not valid.
def compare (source target dests : List Nat) : Option (Out × Out) :=
  (orig source target dests).map fun o => (o, model source target dests)

/-! ## The encoding -/

-- The values: a wildcard, a function return label, variable 0, literal 0 and
-- variable 1, which is spilled.
def alphabet : List Nat := [0, 1, 2, 3, 4]

#guard alphabet.all fun k => number (value k) = k
-- The model and the original agree on the spilled variables of the alphabet.
#guard alphabet.all fun k =>
  Bbu.isSpilled (env []) (slotOf k) = decide (spills.is_spilled (value k))

/-! ## All inputs with at most three target slots -/

-- All lists of `m` distinct destinations below `n`.
def injections : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | m + 1, n => (injections m n).flatMap fun ds =>
    (List.range n).filterMap fun d => if d ∈ ds then none else some (ds ++ [d])

#guard injections 0 0 = [[]]
#guard injections 1 0 = []
#guard (injections 2 3).length = 6
#guard (injections 3 3).all fun ds => ds.Nodup

def words (k : Nat) : List (List Nat) := (List.replicate k alphabet).sections

-- All sources, targets and destinations with `m ≤ n ≤ 3`.
def inputs : List (List Nat × List Nat × List Nat) :=
  (List.range 4).flatMap fun n => (List.range (n + 1)).flatMap fun m =>
    (words m).flatMap fun s => (words n).flatMap fun t => (injections m n).map fun d => (s, t, d)

def results : List (Option (Out × Out)) := inputs.map fun (s, t, d) => compare s t d

def valid : List (Out × Out) := results.filterMap id

def isDone : Out → Bool
  | .done _ => true
  | _ => false

def isBlocked : Out → Bool
  | .blocked .. => true
  | _ => false

-- The number of inputs, of valid inputs, and of valid inputs on which the
-- original is done. The counts also check that the validity filter does not skip
-- all inputs. A stack of three slots is in reach, so no input blocks.
#guard (inputs.length, valid.length, (valid.filter fun r => isDone r.1).length) =
  (116056, 59572, 59572)
-- The model and the original agree on each valid input.
#guard valid.all fun (o, m) => o = m

/-! ## Deep stacks -/

-- `n` distinct literals.
def lits (n : Nat) : List Nat := (List.range n).map fun i => 3 + 2 * i

-- The identity destinations with the positions `a` and `b` exchanged.
def swapped (n a b : Nat) : List Nat :=
  (List.range n).map fun i => if i = a then b else if i = b then a else i

-- A swap at depth 16, the maximum.
def deepSwapOk : Option (Out × Out) := compare (lits 17) (lits 17) (swapped 17 0 16)
-- A swap at depth 17.
def deepSwapBlocked : Option (Out × Out) := compare (lits 18) (lits 18) (swapped 18 0 17)
-- A copy of variable 0 at depth 17.
def deepDupBlocked : Option (Out × Out) :=
  compare (2 :: lits 16) (2 :: lits 16 ++ [2]) (List.range 17)

#guard deepSwapOk.any fun (o, m) => isDone o && o = m
#guard deepSwapBlocked.any fun (o, m) => isBlocked o && o = m
#guard deepDupBlocked.any fun (o, m) => isBlocked o && o = m

/-! ## Sensitivity -/

-- The final permutation of the C++ (`Bbu.buildBottomUpC`) differs from the
-- original on equal slots: the test sees the difference.
#guard (orig [3, 3] [3, 3] [1, 0]).isSome
#guard orig [3, 3] [3, 3] [1, 0] ≠
  some (modelOut (Bbu.buildBottomUpC (env [3, 3]) ([3, 3].map slotOf) [1, 0]))
-- Inputs that are not valid: a destination bound twice, an unbound function
-- return label, and a variable that is neither in the source nor spilled.
#guard (compare [2, 2] [2, 2] [0, 0]).isNone
#guard (compare [] [1] []).isNone
#guard (compare [] [2] []).isNone

end BbuBridge.ModelDiff
