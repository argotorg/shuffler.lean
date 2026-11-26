import Skel.Gen.Derived.Spike
import Skel.Gen.Generate
import Skel.Types
import Skel.Render
import Skel.Rungs
import Skel.Loop
import Lift.Spike.Code

/-! The table of `toyJob` (`docs/one-way-lift-g1-plan-20261118.md`, G1-12 and section 6.2): the generated rows of `toyJob`,
which calls `toySum`. The callee model is the model of the generated `toySum`, in the namespace `ToySum`, and the
`decompiles_l2` of `toySum` is a closed dependency: its block lemmas and its proof are part of the model text, so the table
has the rows of `toyJob` only. The functions are pure; the process is in `Skel/Main.lean`. -/

namespace Skel.Toy.Job

open Skel Skel.Gen

/-- The target of the generated `toySum`: the constants of the hand chain (`Lift/Spike/L1.lean`). -/
def sumTarget : Target :=
  { step := "L1.step", lo := "toyJobPC", hi := "toyEndPC", entryPC := "toySumPC", imports := [], callees := [] }

/-- The callee `toySum` of `toyJob`: the model is the namespace `ToySum`, the inputs are in the order of `Reg64`, the stack
room is 0. -/
def sumCallee : Callee := ⟨".Ltoy.toySum", "ToySum", [.rsi, .rdi], "toySumPC", 0, false, 0, none⟩

/-- The target of `toyJob`. -/
def jobTarget : Target :=
  { step := "L1.step", lo := "toyJobPC", hi := "toyEndPC", entryPC := "toyJobPC", imports := [],
    callees := [sumCallee] }

/-- The header of a check file: the namespace of the file, and the modules that the generated texts use. -/
def header : Header :=
  { imports := ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Spike.Sites", "Lift.Spike.L1",
      "Lift.Sem.StackRoom", "Lift.Spike.Sites.Stack", "Lift.Tactic.Block", "Lift.Tactic.Compose", "Skel.Gen.Sites.Spike"],
    namespace_ := "Skel.Gen.Job", opens := ["Lift.P2.Total", "Lift.Sem", "Lift.Spike"] }

/-- The name of a closed answer in the check files of the rows above it: a block row is its label, any other row is its
own name. -/
def answerName (ob : Obligation) : String :=
  match ob.origin with
  | .block label => label
  | _ => ob.id.name

/-- The theorems of the rows of a generated function, with the proof of a block row `by intros; lift_block` and the `det`
proof for `decompiles_l2`. -/
def theoremsOf (g : Generated) : List String :=
  g.obligations.map fun ob =>
    let proof := match ob.origin, g.det.find? (·.1 == ob.id) with
      | .block _, _ => "by intros; lift_block"
      | _, some (_, text) => text
      | _, none => "by intros; lift_block"
    theoremText (answerName ob) ob.statement proof

/-- The block source of the run: the derived parts of `Lift.Spike.Code.code` (N11, N14). -/
def source : BlockSource := .derived Skel.Gen.Derived.spike

/-- The generated `toySum`, and the generated `toyJob`, from the block source `src`. -/
def sumGenFrom (src : BlockSource) : Except GenError Generated :=
  generate sumTarget Hints.none .storeChain Lift.Spike.Code.code src "toySum"

def jobGenFrom (src : BlockSource) : Except GenError Generated :=
  generate jobTarget Hints.none .storeChain Lift.Spike.Code.code src "toyJob"

def sumGen : Except GenError Generated := sumGenFrom source

def jobGen : Except GenError Generated := jobGenFrom source

/-- The generated `toyJob` with the model text of `toySum` and its closed `decompiles_l2` in front, in the namespace
`ToySum`. -/
def generated : Except GenError Generated := do
  let s ← sumGen
  let j ← jobGen
  let dep := "namespace ToySum\n\n" ++ s.modelText ++ "\n" ++ "\n\n".intercalate (theoremsOf s) ++ "\n\nend ToySum\n\n"
  pure { j with modelText := dep ++ j.modelText }

/-- The ids that an obligation depends on, directly or not. -/
def transitiveDeps (l : Ledger) (ob : Obligation) : List ObId :=
  l.records.toList.reverse.foldl (fun acc r => if acc.contains r.ob.id then acc ++ r.ob.deps else acc) ob.deps

/-- The closed answers of the deps of `ob`, as declarations, in ledger order. -/
def answers (l : Ledger) (ob : Obligation) : List String :=
  let deps := transitiveDeps l ob
  l.records.toList.filterMap fun r =>
    match r.status with
    | .closed c => if deps.contains r.ob.id then some (theoremText (answerName r.ob) r.ob.statement c.proof) else none
    | _ => none

/-- The check file of the proof `text` of `ob`. -/
def checkFileOf (cfg : Config) (g : Generated) (l : Ledger) (ob : Obligation) (text : String) : LeanFile :=
  { name := s!"{header.namespace_}.{ob.id.name}", limitMs := cfg.limitMs,
    text := Skel.checkFile header g.modelText (answers l ob) ob text }

/-- The file of a candidate: a check file for a proof, and an empty file for the others (the table has no refute and no
ask file). -/
def render (cfg : Config) (g : Generated) (l : Ledger) (ob : Obligation) : Candidate → LeanFile
  | .proof _ text => checkFileOf cfg g l ob text
  | _ => { name := "", text := "", limitMs := cfg.limitMs }

/-- The action with its check file made again from the ledger `l`, which holds the answers. -/
def refresh (cfg : Config) (g : Generated) (l : Ledger) : Action → Action
  | .check p f =>
    match l.records.find? (·.ob.id == p.ob), p.candidate with
    | some r, .proof _ text => .check p (checkFileOf cfg g l r.ob text)
    | _, _ => .check p f
  | a => a

/-- The ladders of the table: the `det` rung gives the proof of each row, a complete proof term (`det` starts with
`by`). -/
def laddersOf (g : Generated) : Ladders :=
  ladders [] { l2PlusText := "", l3Text := "", loopRule := "" } [] [] g.det
    ⟨"", "", ""⟩

/-- The step function of the table. -/
def stepFn (cfg : Config) (g : Generated) : Ledger → Event → Ledger × Action := fun l ev =>
  let (l', a) := Skel.step cfg (laddersOf g) (render cfg g l) l ev
  (l', refresh cfg g l' a)

end Skel.Toy.Job
