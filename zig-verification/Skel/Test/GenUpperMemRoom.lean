import Skel.Test.GenUpperRoom
import Skel.Test.GenCallMem

/-! The tests of a stack room in a function with memory in its state (suite `genuppermemroom`, task PIL-CALL2, U5b):
`lake exe skel-test --only genuppermemroom`.

A function with memory in its state (a store through a register, or a call of a callee with memory) and a stack room writes
the room: the L2 model writes the pushes into the memory. So the bytes that the result keeps are the bytes outside the
writable objects and outside the room (the frame clause of `Fn.Return`), and no object meets the room (`Fn.Entry.apart`).

- Synthetic, no loop (`GenUpperRoomTests.memRoom`): a push of 8 and its pop into `rax`, a store through `rdi`, room 8, a
  result with a value and a heap. Lean accepts the G1 text, the L2⁺ text, the relations, every row as a `Prop`,
  `refines_l2p`, `above_l2p` and `above_l3` (with `refines_l3` as a binder), with the standard axioms. The L2 model writes the
  push into the memory and reads the pop from it; the proof of `refines_l2p` steps through both (PIL-CALL3,
  `Lift/Sem/StackPush.lean`): `SimIn` and `SimSt` have the room of the L2 memory (`SysV.RoomAt`) and no object in the room.
- A pop of a word that the entry block pushed (`splitSummary`, PIL-CALL4): the relation at each label has the words that the
  entry block saved and that no other block writes (`Blocks.Returns.simAt`). Lean accepts `refines_l2p`, `above_l2p`, `above_l3`.
- Negative: the same file with the frame clause of `l3.post` without the room is rejected (`postP` keeps only the bytes outside
  the room); a statement room that is not the room of the code is an error; a pop of a word that a later block wrote
  (`overSummary`) has no proof text, and the error names the depth.
- The pilot `mapInPlace` (room 32, memory from the call of `map`): the plan has the room, and the head LBB30_1 with `r15`
  the term of the minimum of two loads (`headTerm`, MAP-HEAD; PIL-CALL5). -/

namespace GenUpperMemRoomTests

open Skel Skel.Gen
open GenUpperPlanTests (hasText)

def target : Target := GenModelTests.sumTarget

def summary : Except GenError Summary :=
  match GenUpperRoomTests.memRoom with
  | some s => .ok s
  | none => .error (.shape 0 "fixture missing")

/-- The shape of `GenUpperBothTests` (one object at `p`, a 64-bit value) with the room `room`. -/
def shape (room : Nat) : Except GenError StmtShape :=
  match GenUpperBothTests.bothShape 64 with
  | some sh => .ok { sh with fn := { sh.fn with room := room } }
  | none => .error (.shape 0 "fixture missing")

def hint : HintRecord := GenUpperBothTests.bothHint GenUpperPlanTests.u64

def plan (room : Nat := 8) : Except GenError UpperPlan := do upperPlan (← summary) (← shape room) hint

open GenUpperRoomTests (below above lit) in
open GenVarsTests (rg) in
/-- A push of `rbx` and a store through `rdi` in the entry block, the pop of `rbx` into `rax` in the next block: room 8. -/
def splitSummary : Except GenError Summary :=
  match GenModelTests.synth "memRoomSplit"
      [ GenUpperPlanTests.blk "entry" 0 [.store 0 (below 8) .W64 (rg .rbx), .store 1 (rg .rdi) .W64 (lit 1)]
          [(.rsp, .sub (rg .rsp) (lit 8))] (GenUpperPlanTests.goto 4),
        GenUpperPlanTests.blk "o4" 4 [.load 0 (above 0) .W64, .load 1 (above 8) .W64]
          [(.rax, .load 0), (.rbx, .load 0), (.rsp, .add (rg .rsp) (lit 16))] GenUpperPlanTests.ret ] with
  | some s => .ok s
  | none => .error (.shape 0 "fixture missing")

def splitPlan : Except GenError UpperPlan := do upperPlan (← splitSummary) (← shape 8) hint

open GenUpperRoomTests (below above lit) in
open GenVarsTests (rg) in
/-- Negative (PIL-CALL4): the entry block pushes `rbx`, the block `o4` writes `rdi` to the same word, and `o8` pops it. No live
push of the entry block has the word at `o8`. -/
def overSummary : Except GenError Summary :=
  match GenModelTests.synth "memRoomOver"
      [ GenUpperPlanTests.blk "entry" 0 [.store 0 (below 8) .W64 (rg .rbx), .store 1 (rg .rdi) .W64 (lit 1)]
          [(.rsp, .sub (rg .rsp) (lit 8))] (GenUpperPlanTests.goto 4),
        GenUpperPlanTests.blk "o4" 4 [.store 0 (above 0) .W64 (rg .rdi)] [] (GenUpperPlanTests.goto 8),
        GenUpperPlanTests.blk "o8" 8 [.load 0 (above 0) .W64, .load 1 (above 8) .W64]
          [(.rax, .load 0), (.rbx, .load 0), (.rsp, .add (rg .rsp) (lit 16))] GenUpperPlanTests.ret ] with
  | some s => .ok s
  | none => .error (.shape 0 "fixture missing")

def overPlan : Except GenError UpperPlan := do upperPlan (← overSummary) (← shape 8) hint

/-- The check file of `memRoom` (as `GenUpperBothTests.fileOf`). `mutate` changes the whole generated text. -/
def fileOf (mutate : String → String := id) (sum : Except GenError Summary := summary) : Except GenError String := do
  let s ← sum
  let sh ← shape 8
  let p ← upperPlan s sh hint
  let g1 ← GenModelTests.textOf target [] s
  let g3 ← upperModelText target s p
  let rel ← upperRelText target sh p
  let rs ← upperRows target "Lift.Spike.Code.code" sh p
  let row (n : String) : Except GenError String :=
    match rs.find? (·.id.name == n) with
    | some o => .ok o.statement
    | none => .error (.shape 0 s!"no row {n}")
  let refines ← row "refines_l3"
  let above ← row "above_l3"
  let a3 ← aboveL3Proof sh p
  let r2 ← refinesProof target s p
  let a2 ← aboveProof s p
  let defs := rs.map fun o => s!"def row_{o.id.name.replace "." "_"} : Prop := {o.statement}"
  let thms := [s!"theorem refines_l2p : {← row "refines_l2p"} := by\n{r2}", s!"theorem above_l2p : {← row "above_l2p"} := by\n{a2}",
    s!"theorem above_l3 (refines_l3 : {refines}) : {above} := by\n{introAboveL3 p sh}\n{a3}"]
  let imports := target.imports ++ ["Lift.Sem.HeapLemmas", "Lift.Sem.Bridge", "Lift.Sem.StackRoom", "Lift.Sem.StackPush",
    "Lift.Trusted.Object", "Lift.Pilot.Encode", "Lift.Spike.Code"]
  pure (mutate ("\n".intercalate (imports.map fun i => s!"import {i}") ++
    s!"\n\nopen {GenUpperModelTests.sumOpens} Lift.Sem.Bridge\n\n" ++ GenUpperBothTests.specText GenUpperBothTests.wide ++
    "\nnamespace MemRoomCheck\n\n" ++ "\n\n".intercalate [g1, g3, rel] ++ "\n\n" ++ "\n\n".intercalate defs ++ "\n\n" ++
    "\n\n".intercalate thms ++ "\n\nend MemRoomCheck\n\n#print axioms MemRoomCheck.above_l3\n" ++
    "#print axioms MemRoomCheck.refines_l2p\n#print axioms MemRoomCheck.above_l2p\n"))

def ok {α : Type} : Except GenError α → Bool
  | .ok _ => true
  | .error _ => false

def pureChecks : List (String × Bool) :=
  [ ("memRoom: the plan has room 8, memory and a value with a heap",
      (plan).toOption.any fun p => p.room == 8 && p.mem && p.kind == .both),
    ("memRoom: the model text, the relations, the rows and above_l3 are generated", ok (fileOf)),
    ("memRoom: refines_l2p and above_l2p have proof texts",
      ok (do refinesProof target (← summary) (← plan)) && ok (do aboveProof (← summary) (← plan))),
    ("memRoom: SimIn and SimSt have the room of the L2 memory and no object in the room",
      (do upperRelText target (← shape 8) (← plan)).toOption.any fun t =>
        hasText t "SysV.RoomAt b.policy b.mem b.sp 8" && hasText t "SysV.RoomAt y.input.policy y.mem y.input.sp 8" &&
          hasText t "SysV.Below y.input.sp 8 b → ¬ Covered x.mem b"),
    ("splitSummary: a pop of a word that the entry block pushed has proof texts (one relation for each label)",
      ok (do refinesProof target (← splitSummary) (← splitPlan)) && ok (do aboveProof (← splitSummary) (← splitPlan))),
    ("overSummary: an overwritten saved word uses private bytes and has a named proof refusal",
      overPlan.toOption.any (·.privateStack) &&
      (do upperModelText target (← overSummary) (← overPlan)).toOption.any (hasText · "PrivateStack.load") &&
      GenUpperModelTests.errHas (do refinesProof target (← overSummary) (← overPlan)) "private stack bytes"),
    ("memRoom: SimSt and SimOut keep the bytes outside the room",
      (do upperRelText target (← shape 8) (← plan)).toOption.any fun t =>
        hasText t "¬ SysV.Below y.input.sp 8 b → y.mem.get? b" && hasText t "¬ SysV.Below y.sp 8 b → r'.2.get? b"),
    ("memRoom: postP keeps the bytes outside the objects and the room",
      (do upperModelText target (← summary) (← plan)).toOption.any (hasText · "SysV.Below")),
    ("memRoom: l3.rep says that no object meets the room",
      (do upperRelText target (← shape 8) (← plan)).toOption.any (hasText · "SysV.Below s.data.regs.rsp.toBitVec 8")),
    ("memRoom: a statement room that is not the room of the code is an error", !ok (plan 16)) ]

/-- The frame clause of `l3.post` with no room: each byte that the objects do not own is unchanged. -/
def dropRoom (t : String) : String :=
  t.replace "(objsP p x ++ frame).Owned b → ¬ SysV.Below s.data.regs.rsp.toBitVec 8 b → t.data.dmem.get? b"
    "(objsP p x ++ frame).Owned b → t.data.dmem.get? b"

def leanChecks : IO (List (String × Bool × String)) := do
  let label := "memRoom: the texts, the rows and above_l3 are accepted with the standard axioms"
  let first ← match fileOf with
    | .error e => pure (label, false, s!"no text: {repr e}")
    | .ok text => GenUpperInputsTests.accepted label "memroom" text "MemRoomCheck.above_l3"
  let l2label := "memRoom: refines_l2p and above_l2p are accepted with the standard axioms"
  let l2p ← match fileOf with
    | .error e => pure (l2label, false, s!"no text: {repr e}")
    | .ok text => GenUpperInputsTests.accepted l2label "memroom-l2p" text "MemRoomCheck.above_l2p"
  let mlabel := "memRoom: l3.post without the room in its frame clause is rejected"
  let second ← match fileOf, fileOf dropRoom with
    | .ok t, .ok m =>
      if t == m then pure (mlabel, false, "the mutation changes nothing")
      else do
        let (_, acc, msg) ← GenUpperInputsTests.accepted mlabel "memroom-mutant" m "MemRoomCheck.above_l3"
        pure (mlabel, !acc, msg)
    | _, _ => pure (mlabel, false, "no text")
  let slabel := "splitSummary: refines_l2p, above_l2p and above_l3 are accepted with the standard axioms"
  let split ← match fileOf id splitSummary with
    | .error e => pure (slabel, false, s!"no text: {repr e}")
    | .ok text => GenUpperInputsTests.accepted slabel "memroom-split" text "MemRoomCheck.refines_l2p"
  pure [first, l2p, second, split]

/-- The plan of the pilot `mapInPlace`: its real blocks and callee `map`, its real shape and hint. -/
def mapInPlacePlan (units : List (String × HintRecord)) : Except GenError UpperPlan := do
  let some h := units.lookup "shuffler.MappingBuilder.mapInPlace" | throw (.shape 0 "no unit")
  let some sh := GenUpperNarrowTests.pilotShape ShapeTests.mapInPlacePilot | throw (.shape 0 "no shape")
  let cs ← GenCallMemTests.calleesOfMapInPlace
  let bs ← blocksFrom Lift.Level3.Code.code (.derived Skel.Gen.Derived.pilot) GenCallMemTests.mapInPlaceLabel
  let s : Summary := ⟨GenCallMemTests.mapInPlaceLabel, bs, vars bs cs, ← frameFacts (cs.map fun c => (c.name, c.room)) bs, none⟩
  upperPlan s sh h

def pilotChecks (units : List (String × HintRecord)) : List (String × Bool) :=
  -- PIL-CALL5: `headVal` gives `r15` the head term of MAP-HEAD, so the plan no longer stops at the head state of LBB30_1
  [ ("mapInPlace: the plan has the room 32 with memory and the head LBB30_1, where r15 is a term (the minimum of two loads)",
      (mapInPlacePlan units).toOption.any fun p => p.room == 32 && p.mem && p.heads.any fun h =>
        h.name.s == "LBB30_1" && h.state.any fun (r, v) => r == .r15 && match v with | .term _ => true | _ => false) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `genuppermemroom`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genuppermemroom" then return 0
  let mut failed := 0
  for (name, good) in pureChecks do
    unless good do
      failed := failed + 1
      IO.println s!"FAIL  genuppermemroom: {name}"
  for (name, good) in pilotChecks (← GenUpperNarrowTests.shufflerUnits) do
    unless good do
      failed := failed + 1
      IO.println s!"FAIL  genuppermemroom: {name}"
  for (name, good, msg) in (← leanChecks) do
    unless good do
      failed := failed + 1
      IO.println s!"FAIL  genuppermemroom: {name}\n{msg}"
  return failed

end GenUpperMemRoomTests
