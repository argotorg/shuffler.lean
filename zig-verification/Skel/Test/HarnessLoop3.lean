import Skel.Discover.Upper
import Skel.Discover.Targets
import Skel.Lean.Shape
import Skel.Lean.SampleObj
import Skel.Lean.Refute
import Skel.Test.DiscoverBlind
import Skel.Io
import Skel.Full.Driver
import Lift.Shuffler.Internal.Proposed.SwapWithStatement
import Lift.Shuffler.Internal.Proposed.DupStatement
import Lift.Shuffler.Internal.Proposed.PushStatement
import Lift.Shuffler.Internal.Proposed.ResolveStatement

/-! The tests of the harness causes of task HARNESS-LOOP3 (suite `harnessloop3`): `lake exe skel-test --only harnessloop3`. A
check that does not hold prints one `FAIL` line. No check makes a paid call.

- I3: the loop row of a function with a call (`mapInPlace`) runs the blocks with the callee relation of `l2p.returns`, not
  `noCall`, and its statement elaborates. A loop row with no call keeps `noCall`.
- I4: the L3 text of a statement names each constant of the project with its full name (`qualifyText`), so that each name of
  the closestCopy text resolves in its refute file and in its check file.
- I1: draws guided by the branch conditions. On a toy with a rare "new best" branch (an element equal to the key), the plain
  refuter leaves the edge with no visit; the guided search covers it, passes a right candidate and refutes a wrong one. On
  closestCopy, a mutant reaches the update path (the edge o72->o83), which no random draw reached in HARNESS-LOOP2. -/

namespace HarnessLoop3Tests

open Skel Skel.Discover Skel.Discover.Upper
open System (FilePath)

def has (s t : String) : Bool := (s.splitOn t).length > 1

def cfg : Skel.Config :=
  { gate := .strict, limitMs := 300000, seed := 1, samples := 200, useTemplates := false, discover := true }

/-- The unit of the pilot function `fn`, its generated chain with the refute texts, and its loop row. -/
def pilotRow (dir : FilePath) (fn : String) : IO (Except String (FnUnit × Skel.Generated × Obligation)) := do
  let us ← Skel.Discover.Targets.unitsOf dir 180000 [fn]
  let some (_, .ok u) := us.head? | return .error s!"no unit of {fn}"
  let g := u.upper.withRefute cfg.seed cfg.samples
  let some ob := g.obligations.find? (·.claim == .loop) | return .error s!"no loop row of {fn}"
  return .ok (u, g, ob)

/-- The text `s` with `extra` before its last line that starts with `end `. -/
def beforeEnd (s extra : String) : String :=
  let ls := s.splitOn "\n"
  match (ls.zipIdx.filter (·.1.startsWith "end ")).getLast? with
  | some (_, i) => "\n".intercalate (ls.take i ++ [extra] ++ ls.drop i)
  | none => s ++ "\n" ++ extra

/-- The output of Lean on the text `text`, written to `dir/name.lean`. -/
def leanOut (dir : FilePath) (name text : String) : IO String := do
  IO.FS.writeFile (dir / s!"{name}.lean") text
  pure (← NxLift.Proc.runLean #[(dir / s!"{name}.lean").toString] 600000).output

/-- The lines of `out` with an error. -/
def errorLines (out : String) : List String := (out.splitOn "\n").filter (has · "error")

/-! ## I3: the loop row of a function with a call -/

def i3Checks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop3-i3"
  match ← pilotRow dir "mapInPlace", ← pilotRow dir "closestCopy" with
  | .ok (u, g, ob), .ok (_, _, obc) =>
    let text := Skel.checkFile u.header g.modelText [] ob "by\n  sorry"
    let out ← leanOut dir "maprow" text
    let errs := errorLines out
    pure
      [ (s!"i3: the loop row of mapInPlace has the callee relation {ob.statement}",
          has ob.statement ".Returns (fun _ => (fun (x : mappingMap.In2p)" &&
          has ob.statement "Lift.Sem.CallFrame.PermLift" && has ob.statement "mappingMap.l2p.returns" &&
          !has ob.statement "noCall"),
        (s!"i3: the loop row of mapInPlace elaborates {errs.take 3}", errs.isEmpty && has out "sorryAx"),
        ("i3 negative: the loop row of closestCopy (no call) has noCall", has obc.statement "blocksP.Returns noCall") ]
  | .error e, _ => pure [(s!"i3: {e}", false)]
  | _, .error e => pure [(s!"i3: {e}", false)]

/-! ## I4: full names in the L3 text -/

def i4PureChecks : List (String × Bool) :=
  let cs : List Lean.Name := [`P.S.eql, `P.Slot, `P.Slot.word, `P.T.junk, `P.T.run, `Q.run]
  let q := Skel.Shape.qualifyText (Skel.Shape.fullAmong cs)
  [ ("i4: a name of a constant gets its full name",
      q "def eql (a b : Slot) : Bool := a.word = Slot.word b" == "def P.S.eql (a b : P.Slot) : Bool := a.word = P.Slot.word b"),
    ("i4: a constant with a field keeps the field", q "junk.kind == x.kind" == "P.T.junk.kind == x.kind"),
    ("i4: a comment, a string and a name after a dot do not change",
      q "-- eql Slot\n/- eql /- Slot -/ junk -/ \"eql\" .eql x.eql" == "-- eql Slot\n/- eql /- Slot -/ junk -/ \"eql\" .eql x.eql"),
    ("i4 negative: a name of two constants keeps its name", q "run" == "run"),
    ("i4 negative: a full name and a local name do not change", q "P.S.eql src best" == "P.S.eql src best"),
    ("i4: the pieces join to the text",
      String.join ((Skel.Shape.identPieces "a.b /- c -/ d -- e\n\"f\" g").map (·.2)) == "a.b /- c -/ d -- e\n\"f\" g") ]

/-- The code identifiers of a Lean text whose first character is upper case (a type or a full name), each once. -/
def upperIdents (s : String) : List String :=
  ((Skel.Shape.identPieces s).filterMap fun (isId, t) =>
    if isId && (t.front).isUpper && !["Prop", "Type", "Sort"].contains t then some t else none).eraseDups

def i4LeanChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop3-i4"
  match ← pilotRow dir "closestCopy" with
  | .error e => pure [(s!"i4: {e}", false)]
  | .ok (u, g, ob) =>
    let l3 := u.shape.l3Text
    let ids := upperIdents l3
    let probe := "\n".intercalate (ids.map (s!"#check @{·}"))
    let t0 : Triple := { inv := "True", measure := "0", result := "0" }
    let some refute := g.refuteText ob.id (.triple .discover t0) | return [("i4: a refute text", false)]
    let refOut ← leanOut dir "refute" (refute.replace "end Skel.Gen." (probe ++ "\nend Skel.Gen."))
    let chkOut ← leanOut dir "check" (beforeEnd (Skel.checkFile u.header g.modelText [] ob "by\n  sorry") probe)
    let bare := (Skel.Shape.identPieces l3).filterMap fun (b, t) => if b then some t else none
    pure
      [ (s!"i4: the L3 text of closestCopy has full names {ids}",
          ["Lift.Pilot.ShallowestSpec.eql", "Lift.Pilot.IsRetainedSpec.none64", "Lift.Pilot.Slot.word"].all ids.contains),
        (s!"i4 negative: no bare eql, none64 or Slot.word in the code of the L3 text",
          !(bare.any fun t => ["eql", "none64", "Slot.word", "Encode.encode"].contains t)),
        (s!"i4: each upper-case name of the L3 text resolves in the refute file {(errorLines refOut).take 3}",
          (errorLines refOut).isEmpty && !ids.isEmpty),
        (s!"i4: each upper-case name of the L3 text resolves in the check file {(errorLines chkOut).take 3}",
          (errorLines chkOut).isEmpty) ]


/-! ## I1: the toy with a rare new best -/

inductive TL where | head | cmp | upd | next | done deriving DecidableEq, Repr

structure TSt where
  (xs : List (BitVec 64)) (key : BitVec 64) (i : Nat) (best : Nat)

/-- The loop: the last index of an element equal to the key, or 1000. The edge `cmp -> upd` is the new best. -/
def toyBlocks : Lift.Sem.Leaf TL TSt Nat :=
  ⟨fun l x => match l with
    | .head => .ok (if x.i < x.xs.length then .goto .cmp x else .goto .done x)
    | .cmp => .ok (if x.xs[x.i]! = x.key then .goto .upd x else .goto .next x)
    | .upd => .ok (.goto .next { x with best := x.i })
    | .next => .ok (.goto .head { x with i := x.i + 1 })
    | .done => .ok (.ret x.best)⟩

abbrev TIn : Type := List (BitVec 64) × BitVec 64

/-- The spec: the last index of the key from `b` on, after the best `b0`. -/
def lastFrom (xs : List (BitVec 64)) (key : BitVec 64) (i b0 : Nat) : Nat :=
  ((xs.zipIdx.drop i).foldl (fun b (v, j) => if v = key then j else b) b0)

def toyState (inp : TIn) : TSt := ⟨inp.1, inp.2, 0, 1000⟩

def toyAdmitted (g : Coordinator.Dst.Rng) : TIn × TSt × Nat :=
  -- the key is a word of 63 random bits with the top bit: a drawn element (`Skel.Sample.word`) is almost never equal to it
  let key : BitVec 64 := BitVec.ofNat 64 ((g.stream 1).natIn 0 (2 ^ 62)).1 ||| (1 <<< 63)
  let inp : TIn := (Skel.Sample.Sample.draw (g.stream 0), key)
  (inp, toyState inp, lastFrom inp.1 inp.2 0 1000)

def toyFree (g : Coordinator.Dst.Rng) : TIn × TSt :=
  let (inp, _, _) := toyAdmitted g
  (inp, { toyState inp with i := Skel.Sample.counter (g.stream 2) 6 })

def toyOps : TL → TSt → List UInt64
  | .cmp, x => [UInt64.ofBitVec x.xs[x.i]!, UInt64.ofBitVec x.key]
  | _, _ => []

def toyGuide (ops : TL → TSt → List UInt64) : Skel.Refute.Guide TL TIn TSt Nat :=
  { mutant := fun _ m d gh => let inp := Skel.Sample.Mutate.mutate m d gh; some (inp, toyState inp, lastFrom inp.1 inp.2 0 1000)
    ops, render := fun gh x => s!"xs = {gh.1}, key = {gh.2}, i = {x.i}" }

def toyEdges : List (String × Skel.Refute.Edge TL) :=
  [("head->cmp", (.head, some .cmp)), ("head->done", (.head, some .done)), ("cmp->upd", (.cmp, some .upd)),
   ("cmp->next", (.cmp, some .next)), ("upd->next", (.upd, some .next)), ("next->head", (.next, some .head)),
   ("done->ret", (.done, none))]

/-- A right candidate: the input is fixed, the index is in range, and the result is the last match after the best so far. -/
def rightInv (g : TIn) (x : TSt) : Bool := x.xs == g.1 && x.key == g.2 && decide (x.i ≤ x.xs.length)
def rightMeasure (_ : TIn) (x : TSt) : Nat := x.xs.length - x.i
def rightOut (_ : TIn) (x : TSt) : Nat := lastFrom x.xs x.key x.i x.best
/-- A wrong result: the best so far, which a later match changes. -/
def wrongOut (_ : TIn) (x : TSt) : Nat := x.best

def i1ToyChecks : List (String × Bool) :=
  let plain := Skel.Refute.refuteLoopCov toyEdges toyBlocks .head 16 rightInv rightMeasure rightOut toyAdmitted toyFree 1 200
  let right := Skel.Refute.refuteLoopCovG toyEdges (toyGuide toyOps) toyBlocks .head 16 rightInv rightMeasure rightOut
    toyAdmitted toyFree 1 200
  let wrongPlain := Skel.Refute.refuteLoopCov toyEdges toyBlocks .head 16 rightInv rightMeasure wrongOut toyAdmitted toyFree 1 200
  let wrong := Skel.Refute.refuteLoopCovG toyEdges (toyGuide toyOps) toyBlocks .head 16 rightInv rightMeasure wrongOut
    toyAdmitted toyFree 1 200
  let shown : Nat → String := fun _ => ""
  [ (s!"i1: the plain refuter leaves the new best with no visit {repr plain}",
      match plain with | .uncovered _ _ ms => ms.contains "cmp->upd" | _ => false),
    (s!"i1: the guided search covers the new best and passes the right candidate {right.line shown}",
      match right with | .cov (.found (.pass _)) => true | _ => false),
    (s!"i1 negative: the plain refuter does not refute the wrong result {repr wrongPlain}",
      match wrongPlain with | .uncovered .. => true | _ => false),
    (s!"i1: the guided search refutes the wrong result with an admitted mutant {wrong.line shown}",
      match wrong with | .mutant .. => true | _ => false) ]

/-- The edges of the update path of closestCopy that no draw reached in HARNESS-LOOP2 (its ledger, round 1). -/
def updateEdges : List String := ["o72->o83", "o83->LBB29_7", "o83->LBB29_3"]

/-- On closestCopy: the refute text has the guide, and a mutant of the guided search reaches the update path. The search runs
with the counts of every other edge, a candidate that holds at each state (`I` true) and the measure 0, so the first mutant
whose run takes a missing edge stops the search with the failure of its measure. -/
def i1PilotChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop3-i1"
  let us ← Skel.Discover.Targets.unitsOf dir 180000 ["closestCopy"]
  let some (_, .ok u) := us.head? | return [("i1: the unit of closestCopy", false)]
  let some s := (sitesOf u).head? | return [("i1: a site of closestCopy", false)]
  match machineFor cfg u s (dir / "machine") with
  | .error e => return [(s!"i1: the machine of closestCopy: {e.text}", false)]
  | .ok m =>
    let ops := opsDecl u m.spec.stateTy
    let withStores := { u with blocks := u.blocks.map fun b =>
      { b with accesses := b.accesses ++ [.store 999 (.lit 0) .W8 (.lit 0)] } }
    let refusedOps := opsDecl withStores m.spec.stateTy
    let withStackLoads := { u with blocks := u.blocks.map fun b =>
      { b with accesses := b.accesses ++ [.load 999 (.reg .rsp) .W64] } }
    let stackOps := opsDecl withStackLoads m.spec.stateTy
    let t0 : Triple := { inv := "True", measure := "0", result := "0" }
    let some text0 := m.gen.refuteText m.ob.id (.triple .discover t0) | return [("i1: a refute text", false)]
    let some text := Skel.Discover.Cover.coverText m.edges text0 | return [("i1: a cover text", false)]
    let edgesT := Skel.Discover.Cover.universeText m.edges
    let counted := "(" ++ edgesT ++ ").filterMap fun (n, e) => if [" ++ ", ".intercalate (updateEdges.map (·.quote)) ++
      "].contains n then none else some (e, 1)"
    let search (ops : String) := s!"(Skel.Refute.guided {edgesT} blocksP Lbl.{m.head} 86 (fun _ _ => true) (fun _ _ => 0) " ++
      s!"refuteResult ⟨refuteMutant, {ops}, refuteRender⟩ 1 0 800 (Skel.Refute.seedsOf refuteAdmitted 1 16) ({counted}) []).1.isSome"
    let probe := "#eval IO.println (\"guided \" ++ toString " ++ search "refuteOps" ++ ")\n#eval IO.println (\"unguided \" ++ toString " ++
      search "(fun _ _ => [])" ++ ")"
    let out ← leanOut dir "guided" (text.replace "end Skel.Gen." (probe ++ "\nend Skel.Gen."))
    pure
      [ ("i1: the refute text of closestCopy runs the guided search", has text "Skel.Refute.refuteLoopCovG" &&
          has text "def refuteOps " && has text "def refuteMutant "),
        ("i1: branch operands of a memory plan load the current memory", u.plan.mem &&
          has ops "| .o51, x =>" && has ops "x.mem.loadB" && !has ops "x.input.heap"),
        ("i1 negative: a branch with a store gives no operand arm", refusedOps ==
          s!"def refuteOps : Lbl → {m.spec.stateTy} → List UInt64\n  | _, _ => []"),
        ("i1 negative: a branch with a stack load gives no operand arm", stackOps ==
          s!"def refuteOps : Lbl → {m.spec.stateTy} → List UInt64\n  | _, _ => []"),
        (s!"i1: a guided mutant of closestCopy reaches the update path {(errorLines out).take 2} {(out.takeEnd 300).toString}",
          has out "guided true"),
        ("i1 negative: with no operand words, no mutant reaches it", has out "unguided false") ]

/-- The proposed posts encode a field derived from the whole result, rather than its first component. -/
def projectionChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop3-result-projection"
  let names := ["emissionSwapWith", "emissionDup", "emissionPush"]
  let us ← Skel.Discover.Targets.fullUnitsOf dir 180000 names
  let checks ← us.mapM fun (fn, u) => do
    match u with
    | .error e => pure [(s!"projection: {fn} generates: {e}", false)]
    | .ok u =>
      let model := u.upper.generated.modelText
      let marker : Obligation :=
        { id := ⟨fn, "projectionCheck"⟩, cls := .contract, origin := .unit, statement := "True", deps := [], claim := .none }
      let out ← leanOut dir fn (Skel.checkFile u.header model [] marker "by trivial")
      let wrong := match u.shape.resultFn with
        | some f => model.replace s!"Lift.Trusted.Encode.encode (({f.s}) y)" "Lift.Trusted.Encode.encode y.1"
        | none => model
      let bad ← leanOut dir (fn ++ "-first-field") (Skel.checkFile u.header wrong [] marker "by trivial")
      pure
        [ (s!"projection: {fn} preserves the encoded result field", has model "Statement.result"),
          (s!"projection: {fn} model elaborates {(errorLines out).take 2}", (errorLines out).isEmpty),
          (s!"projection negative: {fn} cannot encode the first field", wrong != model && has bad "Encode" && !(errorLines bad).isEmpty),
          (s!"projection: {fn} shape round trip preserves its result function",
            (Skel.Gen.Shape.parse u.shape.toJson).toOption == some u.shape) ]
  pure checks.flatten

/-- Resolve keeps its typed L3 result and encodes the field that its post gives. -/
def typedResultChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop3-typed-result"
  let us ← Skel.Discover.Targets.fullUnitsOf dir 180000 ["plannerResolve"]
  let some (_, u) := us.head? | return [("typed result: Resolve input remains visible", false)]
  match u with
  | .error e => pure [(s!"typed result: Resolve generates: {e}", false)]
  | .ok u =>
    let model := u.upper.generated.modelText
    let marker : Obligation :=
      { id := ⟨u.fn, "typedResultCheck"⟩, cls := .contract, origin := .unit, statement := "True", deps := [], claim := .none }
    let out ← leanOut dir "resolve-model" (Skel.checkFile u.header model [] marker "by trivial")
    let loopChecks ← (u.upper.generated.obligations.filter (·.claim == .loop)).mapM fun ob => do
      let result ← leanOut dir ob.id.name (Skel.checkFile u.header model [] ob "by\n  sorry")
      pure (s!"typed result: Resolve row {ob.id.name} elaborates {(errorLines result).take 2}", (errorLines result).isEmpty)
    pure
      ([ ("typed result: Resolve shape keeps ExecutionOutcome", (u.shape.runResultType.map fun t => has t.s "FlatShuffler.Flat.ExecutionOutcome").getD false),
         ("typed result: Resolve model uses its result field", has model "ResolveStatement.result"),
         (s!"typed result: Resolve model elaborates {(errorLines out).take 2}", (errorLines out).isEmpty) ] ++ loopChecks)

/-- Full discovery names every derived function; a failed target must remain visible. -/
def fullTargetChecks : List (String × Bool) :=
  let names := Skel.Gen.Derived.shuffler.map fun p => Skel.IntQ.fnConstOf p.1
  [ ("full: the full target lists all shuffler functions", Skel.Discover.Targets.namesOf "full" == some names),
    ("full: a full function is a target", Skel.Discover.Targets.namesOf "shuffle" == some ["shuffle"]),
    ("full negative: an unknown function remains unknown", Skel.Discover.Targets.namesOf "absentFunction" == none) ]

def unknownUnitChecks : IO (List (String × Bool)) := do
  let dir ← DiscoverBlindTests.newDir "harnessloop3-unknown"
  let us ← Skel.Discover.Targets.unitsOf dir 180000 ["absentFunction"]
  pure [("full negative: an unknown input gives an error unit", match us with
    | [("absentFunction", .error _)] => true | _ => false)]

/-- The number of failed checks. The suite runs when `only` is none or `harnessloop3`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "harnessloop3" then return 0
  let checks := (← i3Checks) ++ i4PureChecks ++ (← i4LeanChecks) ++ i1ToyChecks ++ (← i1PilotChecks) ++ fullTargetChecks ++ (← unknownUnitChecks) ++ (← projectionChecks) ++ (← typedResultChecks)
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  harnessloop3: {name}"
  return failed

end HarnessLoop3Tests
