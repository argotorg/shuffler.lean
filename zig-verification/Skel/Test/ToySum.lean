import Skel.TempDir
import Skel.Source
import Skel.Render
import Skel.Io
import Skel.Driver
import Skel.Toy.Sum
import Skel.Toy.SumRefute
import Skel.Gen.Derived.Spike
import Skel.Gen.Generate
-- The check files import this module; the import makes `lake build` build it.
import Lift.Tactic.LoopClose
import Lift.Spike.Code

/-! The tests of `Skel/Toy/Sum.lean` (suite `toysum`): `lake exe skel-test --only toysum`. The tests that say so read
the two hand files from the repository root: `Lift/Spike/Sum.lean` and `Lift/Spike/Sites/Sum.lean`. Each test name
starts with `toysum.`. The check gives the failure message, or `none` when the test passes. -/

namespace ToySumTests

open Skel

/-- A test: its name, and its check. The check gives the failure message, or `none` when the test passes. -/
structure Test where
  name : String
  check : IO (Option String)

/-- `none` when the values are equal, else the message with both values. -/
private def eqMsg {α : Type} [BEq α] [Repr α] (actual expected : α) : Option String :=
  if actual == expected then none
  else some s!"expected {repr expected}, got {repr actual}"

/-- Whether `needle` occurs in `hay`. -/
private def occurs (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- The sources of the real hand files, read from the repository root, with the check `f`. -/
private def onReal (f : Skel.Toy.Sum.Sources → Option String) : IO (Option String) := do
  let sum ← IO.FS.readFile "Lift/Spike/Sum.lean"
  let sites ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean"
  return f { sum, sites }

/-- The check `f` on the generated result, or the error of the generator. -/
private def onGenerated (src : Skel.Toy.Sum.Sources) (f : Generated → Option String) : Option String :=
  match Skel.Toy.Sum.generate src with
  | .ok g => f g
  | .error e => some s!"generate failed: {e}"

/-- A test of the generated result of the real hand files. -/
private def onGen (name : String) (f : Generated → Option String) : Test :=
  { name, check := onReal fun src => onGenerated src f }

/-- A test that the generator fails on the real hand files changed by `f`, and that the error names `what`. -/
private def mustFail (name what : String) (f : Skel.Toy.Sum.Sources → Skel.Toy.Sum.Sources) : Test :=
  { name, check := onReal fun src =>
      match Skel.Toy.Sum.generate (f src) with
      | .ok _ => some "generate gave .ok"
      | .error e => if occurs what e then none else some s!"the error does not name {what}: {e}" }

private def sid (name : String) : ObId := { function := "sum", name := name }

/-- The target of `toySum` as the plan states it: the constants of `Lift/Spike/L1.lean` and `Lift/Spike/Sum.lean`. -/
private def sumTarget : Skel.Gen.Target :=
  { step := "L1.step", lo := "toyJobPC", hi := "toyEndPC", entryPC := "toySumPC",
    imports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.SysV", "Lift.Spike.L1"], callees := [] }

/-- The id with the function `sum`, the function of the table of 2.1. -/
private def toSum (i : ObId) : ObId := { i with function := "sum" }

/-- The fields of an obligation that the generator sets, for comparison. -/
private def fieldsOf (o : Obligation) : ObId × ObClass × Origin × String × List ObId × Claim :=
  (o.id, o.cls, o.origin, o.statement, o.deps, o.claim)

/-- The obligations and the det texts that `Skel.Gen.generate` gives for `toySum` (the function `toySum` of
`Lift.Spike.Code.code`), with the function of each id renamed to `sum`. -/
private def generatorOut : Except String (List Obligation × List (ObId × String)) :=
  match Skel.Gen.generate sumTarget Skel.Gen.Hints.none .storeChain Lift.Spike.Code.code (.derived Skel.Gen.Derived.spike) "toySum" with
  | .ok g => .ok (g.obligations.map (fun o => { o with id := toSum o.id, deps := o.deps.map toSum }),
      g.det.map fun (i, t) => (toSum i, t))
  | .error e => .error (reprStr e)

/-- The ledger in which the block rows are closed by their deterministic text (`by intros; lift_block`, rung 1 of
2.1), so that a check file of `decompiles_l2` has the four block answers. -/
private def blockClosed : Status :=
  .closed { rung := .liftBlock, triple := none, proof := "by intros; lift_block", axioms := ["propext"], ms := 1 }

private def blocksClosed (obs : List Obligation) : Ledger :=
  ⟨(Ledger.init obs).records.map fun r =>
    if r.ob.id.name.startsWith "block." then { r with status := blockClosed } else r⟩

/-- The outcome of real Lean on the check file of `decompiles_l2`: its det text, with the four block rows closed. -/
private def decompilesOutcome : IO (Option String) := do
  let sum ← IO.FS.readFile "Lift/Spike/Sum.lean"
  let sites ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean"
  let cfg : Config := { gate := .strict, limitMs := 180000, seed := 1, samples := 10 }
  match Skel.Driver.setup cfg .none { sum, sites } with
  | .error e => return some e
  | .ok s =>
    let obs := s.env.gen.obligations
    let some ob := obs.find? (·.id == sid "decompiles_l2") | return some "no row decompiles_l2"
    let some text := (s.env.gen.det.find? (·.1 == ob.id)).map (·.2) | return some "no det text for decompiles_l2"
    let dir ← Skel.tempDir "toysum-test-decompiles"
    let (o, _) ← Skel.Io.checker dir .strict (Skel.Driver.checkFileOf s.env (blocksClosed obs) ob text)
    match o with
    | .accepted _ => return none
    | _ => return some s!"expected an accepted check file, got {repr o}"

/-- The ids of 2.1, in table order. -/
private def expectedNames : List String :=
  ["block.entry", "block.LBB1_1", "block.o9", "block.LBB1_3", "decompiles_l2", "refines_l2p", "above_l2p", "loop",
    "refines_l3", "above_l3", "total", "decompiles", "decompiles_code", "contract"]

/-- The classes of 2.1, in table order. -/
private def expectedClasses : List ObClass :=
  [.block, .block, .block, .block, .block, .access, .access, .refine, .refine, .refine, .total, .link, .link,
    .contract]

/-- The origins of 2.1, in table order. -/
private def expectedOrigins : List Origin :=
  [.block "entry", .block "LBB1_1", .block "o9", .block "LBB1_3", .unit, .unit, .unit, .loop "LBB1_1", .unit, .unit,
    .unit, .unit, .unit, .unit]

/-- The claims of 2.1, in table order: row 8 `loop`, row 9 `models`, the others `none`. -/
private def expectedClaims : List Claim :=
  [.none, .none, .none, .none, .none, .none, .none, .loop, .models, .none, .none, .none, .none, .none]

/-- The deps of 2.1 by name, in table order. -/
private def expectedDeps : List (List String) :=
  [[], [], [], [], ["block.entry", "block.LBB1_1", "block.o9", "block.LBB1_3"], [], ["refines_l2p"], [], [],
    ["refines_l3"], [], ["decompiles_l2", "above_l2p", "above_l3"], ["decompiles"], ["total", "decompiles_code"]]

/-- The ids with a replay text (5.1, item 4): the rows 6 to 14 with no loop. -/
private def replayNames : List String := (expectedNames.drop 5).filter (· ≠ "loop")

/-- The statements of the rows 1, 9, 10, 11 and 8 (the loop), as Lean text. -/
private def expectedEntry : String :=
  "∀ {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData) {Q : MachineState → Prop} " ++
    "(hQ : ∀ f : StatusFlags, Q ⟨{ d with regs := { d.regs with rax := 0, rcx := 0 }, status := f }, toySumPC + 4⟩), " ++
    "Reaches L1.step policy Q ⟨d, toySumPC⟩"

private def expectedRefinesL3 : String :=
  "Refines SimArr (fun _ _ y r => r.toBitVec = y) (fun xs y => run xs = some y) l2p.returns"

private def expectedAboveL3 : String := "∀ (p : BitVec 64) (wr : Bool) (frame : Heap), Above l2p (l3 p wr frame)"

private def expectedTotal : String := "∀ xs, C xs → ∃ y, run xs = some y"

private def expectedLoop : String :=
  "∀ (xs : List (BitVec 64)) (a : In2p), SimArr xs a → blocksP.Returns noCall .LBB1_1 (init a) (UInt64.ofBitVec xs.sum)"

/-- The statement at index `i` of the generated obligations. -/
private def statementAt (g : Generated) (i : Nat) : Option String :=
  (g.obligations.map (·.statement))[i]?

/-- `none` when the ids of the obligations are the ids of 2.1, in table order. -/
private def ids (g : Generated) : Option String :=
  eqMsg (g.obligations.map (·.id)) (expectedNames.map sid)

private def tripleParts : List String :=
  ["x.rcx.toNat ≤ xs.length", "xs.length - x.rcx.toNat", "x.rax + UInt64.ofBitVec (xs.drop x.rcx.toNat).sum"]

/-- Whether each dep of each obligation is an obligation before it in the list. -/
private def depsEarlier : List Obligation → List ObId → Bool
  | [], _ => true
  | o :: os, seen => o.deps.all (seen.contains ·) && depsEarlier os (seen ++ [o.id])

/-- Each part of the hand triple (5.2, item 2) occurs in `Sum.lean` after `squash`. -/
private def tripleInFile (src : Skel.Toy.Sum.Sources) : Option String :=
  match tripleParts.find? fun p => !occurs (squash p) (squash src.sum) with
  | none => none
  | some p => some s!"the triple text {p} does not occur in Sum.lean after squash"

/-- The declarations of the model text of 5.4, copied from the plan (not from the production list). -/
private def modelDeclNames : List String :=
  ["In2", "In2p", "Lbl", "St", "init", "blocks", "blocksP", "post", "l2", "l2p", "run", "C", "l3", "At",
    "SimIn", "SimArr", "SimSt"]

/-- `none` when the model text has a line that starts a declaration of each name of `modelDeclNames`. -/
private def declsInModel (g : Generated) : Option String :=
  let lines := g.modelText.splitOn "\n"
  let declared (n : String) : Bool :=
    ["def ", "structure ", "inductive ", "abbrev "].any fun k => lines.any fun l => l.startsWith (k ++ n ++ " ")
  match modelDeclNames.find? (fun n => !declared n) with
  | none => none
  | some n => some s!"the model text has no declaration {n}"

/-- The lines 224 to 243 of `Lift/Spike/Sum.lean`: the step of the hand proof of the loop. -/
private def handStepLines (sum : String) : List String :=
  (((sum.splitOn "\n").drop 223).take 20).map (·.trimAscii.toString) |>.filter (· ≠ "")

/-- The proof text of the loop row of the triple `t`, from the generated loop statement. -/
private def loopProofOf (g : Generated) (t : Triple) : Option String :=
  (g.obligations.find? (·.claim == .loop)).map fun ob => loopProof ob.statement t

/-- The loop proof of the triple `t` has the call and the three terms, and none of the lines 224 to 243 of the hand
file. -/
private def loopProofShape (src : Skel.Toy.Sum.Sources) (t : Triple) : Option String :=
  onGenerated src fun g =>
    match loopProofOf g t with
    | none => some "no loop obligation"
    | some p =>
      let hand := handStepLines src.sum
      if hand.length < 15 then some s!"the hand lines are not 224 to 243: {hand.length} lines"
      else if !occurs "lift_loop!" p then some "no lift_loop! in the proof"
      else if !([t.inv, t.measure, t.result].all fun u => occurs s!"({u})" p) then some "a term is not in the proof"
      else
        match hand.find? (occurs · p) with
        | some l => some s!"the proof has the hand line {l}"
        | none => none

/-- The check file of the loop row with the triple `t`, made by the driver from the real sources. The proof text is the
one that the loop gives to the check of a triple: `loopProof` of the statement and `t`. -/
private def loopCheckFile (t : Triple) : IO LeanFile := do
  let sum ← IO.FS.readFile "Lift/Spike/Sum.lean"
  let sites ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean"
  let cfg : Config := { gate := .strict, limitMs := 180000, seed := 1, samples := 10 }
  match Skel.Driver.setup cfg .none { sum, sites } with
  | .error e => throw (IO.userError e)
  | .ok s =>
    let some ob := s.env.gen.obligations.find? (·.claim == .loop) | throw (IO.userError "no loop obligation")
    return Skel.Driver.checkFileOf s.env (Ledger.init s.env.gen.obligations) ob (loopProof ob.statement t)

/-- The outcome of real Lean on the check file of the loop row with the triple `t`. -/
private def loopOutcome (tag : String) (t : Triple) : IO Outcome := do
  let dir ← Skel.tempDir s!"toysum-test-{tag}"
  return (← Skel.Io.checker dir .strict (← loopCheckFile t)).1

private def tests : List Test := [
  onGen "toysum.ids" fun g => ids g,
  onGen "toysum.ids.distinct" fun g =>
    let idList := g.obligations.map (·.id)
    if idList.eraseDups.length == idList.length then none else some "two obligations have the same id",
  onGen "toysum.classes" fun g => eqMsg (g.obligations.map (·.cls)) expectedClasses,
  onGen "toysum.origins" fun g => eqMsg (g.obligations.map (·.origin)) expectedOrigins,
  onGen "toysum.claims" fun g => eqMsg (g.obligations.map (·.claim)) expectedClaims,
  onGen "toysum.deps" fun g => eqMsg (g.obligations.map (·.deps)) (expectedDeps.map (·.map sid)),
  onGen "toysum.deps.earlier" fun g =>
    if depsEarlier g.obligations [] then none else some "a dep comes after its obligation in the list",
  onGen "toysum.statements.nonEmptyNoProof" fun g =>
    let bad := g.obligations.find? fun o =>
      o.statement.isEmpty || o.statement.endsWith ":=" || occurs ":= by" o.statement || occurs " by " o.statement
    match bad with
    | none => none
    | some o => some s!"statement of {o.id.name} is empty or has a proof: {repr o.statement}",
  onGen "toysum.statement.entry" fun g => eqMsg ((statementAt g 0).map squash) (some expectedEntry),
  onGen "toysum.statement.loop" fun g => eqMsg (statementAt g 7) (some expectedLoop),
  onGen "toysum.statement.refinesL3" fun g => eqMsg (statementAt g 8) (some expectedRefinesL3),
  onGen "toysum.statement.aboveL3" fun g => eqMsg (statementAt g 9) (some expectedAboveL3),
  onGen "toysum.statement.total" fun g => eqMsg (statementAt g 10) (some expectedTotal),
  onGen "toysum.model.noTheorem" fun g =>
    if (g.modelText.splitOn "\n").any (·.startsWith "theorem") then some "the model text has a theorem" else none,
  onGen "toysum.model.decls" declsInModel,
  onGen "toysum.model.noSitesSum" fun g =>
    if occurs "Sites.Sum" g.modelText then some "the model text names Sites.Sum" else none,
  onGen "toysum.generated.rows" fun g =>
    match generatorOut with
    | .ok (rs, _) => eqMsg ((g.obligations.take 5).map fieldsOf) (rs.map fieldsOf)
    | .error e => some s!"the generator failed: {e}",
  onGen "toysum.det" fun g =>
    match generatorOut with
    | .ok (_, det) => eqMsg g.det det
    | .error e => some s!"the generator failed: {e}",
  { name := "toysum.io.decompilesCheck", check := decompilesOutcome },
  { name := "toysum.replies", check := pure (eqMsg Skel.Toy.Sum.replies []) },
  { name := "toysum.replayStore", check := onReal fun src =>
      match Skel.Toy.Sum.replayStore src with
      | .ok st => eqMsg (st.map (·.1)) (replayNames.map sid)
      | .error e => some s!"replayStore failed: {e}" },
  { name := "toysum.replayStore.noLoop", check := onReal fun src =>
      match Skel.Toy.Sum.replayStore src with
      | .ok st => if st.any (·.1 == sid "loop") then some "the replay store has a text for the loop" else none
      | .error e => some s!"replayStore failed: {e}" },
  { name := "toysum.io.generate", check := onReal fun src =>
      match Skel.Toy.Sum.generate src, Skel.Toy.Sum.replayStore src with
      | .ok _, .ok store => eqMsg store.length 8
      | .error e, _ => some s!"generate failed: {e}"
      | _, .error e => some s!"replayStore failed: {e}" },
  { name := "toysum.drift.tripleInFile", check := onReal fun src => tripleInFile src },
  { name := "toysum.loopProof.shape", check := onReal fun src => loopProofShape src Skel.Toy.Sum.template1 },
  { name := "toysum.loopProof.shape.hand", check := onReal fun src =>
      match Skel.Toy.SumRefute.handTriple src with
      | .ok t => loopProofShape src t
      | .error e => some e },
  { name := "toysum.loopProof.intro", check := onReal fun src =>
      onGenerated src fun g =>
        match loopProofOf g Skel.Toy.Sum.template1 with
        | some p => if occurs "by\n  intro xs a\n  intros\n  split_hyps\n  lift_loop! " p then none
          else some s!"unexpected introduction: {repr p}"
        | none => some "no loop obligation" },
  -- Real Lean: the template triple T1 gives a failed proof that names an open case of the tactic.
  { name := "toysum.loopProof.lean.t1", check := do
      match ← loopOutcome "t1" Skel.Toy.Sum.template1 with
      | .failed es =>
        let text := "\n".intercalate es
        if occurs "case back_1.dec" text || occurs "case nofault_1" text then return none
        else return some s!"the errors name no open case: {text}"
      | o => return some s!"expected a failed proof, got {repr o}" },
  -- Real Lean: the hand triple gives an accepted proof.
  { name := "toysum.loopProof.lean.hand", check := do
      let sum ← IO.FS.readFile "Lift/Spike/Sum.lean"
      let sites ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean"
      match Skel.Toy.SumRefute.handTriple { sum, sites } with
      | .error e => return some e
      | .ok t =>
        match ← loopOutcome "hand" t with
        | .accepted _ => return none
        | o => return some s!"expected an accepted proof, got {repr o}" },
  { name := "toysum.binders.names", check := pure (eqMsg
      (binderNames "(p : BitVec 64) (wr : Bool) (frame : Heap)") ["p", "wr", "frame"]) },
  { name := "toysum.binders.several", check := pure (eqMsg (binderNames "(a b : Nat) {c : Nat}") ["a", "b", "c"]) },
  { name := "toysum.binders.nested", check := pure (eqMsg
      (binderNames "{policy : P} (hx : A) (hQ : ∀ f : S, Q ⟨{ d with r := { d.r with a := 0 } }, h⟩)")
      ["policy", "hx", "hQ"]) },
  { name := "toysum.binders.none", check := pure (eqMsg (binderNames "") []) },
  { name := "toysum.binders.instance", check := pure (eqMsg (binderNames "[Foo α] (x : α)") ["_", "x"]) },
  { name := "toysum.intro.none", check := pure (eqMsg (Skel.Toy.Sum.introBinders [] "by\n  simp") "by\n  simp") },
  { name := "toysum.intro.block", check := pure (eqMsg (Skel.Toy.Sum.introBinders ["p", "q"] "by\n  simp\n  rfl")
      "by\n  intro p q\n  simp\n  rfl") },
  { name := "toysum.intro.oneLine", check := pure (eqMsg (Skel.Toy.Sum.introBinders ["p"] "by simp; rfl") "by intro p; simp; rfl") },
  { name := "toysum.intro.term", check := pure (eqMsg (Skel.Toy.Sum.introBinders ["p", "q"] "foo p q") "fun p q => foo p q") },
  { name := "toysum.replay.aboveL3.intro", check := onReal fun src =>
      match Skel.Toy.Sum.replayStore src with
      | .ok st => match st.find? (fun p => p.1 == sid "above_l3") with
        | some (_, t) => if t.startsWith "by\n  intro p wr frame\n  refine Above.ofRefines" then none
          else some s!"the replay text of above_l3 does not intro its binders: {repr (String.ofList (t.toList.take 80))}"
        | none => some "no replay text for above_l3"
      | .error e => some s!"replayStore failed: {e}" },
  { name := "toysum.replay.noGenerated", check := onReal fun src =>
      match Skel.Toy.Sum.replayStore src with
      | .ok st =>
        if st.any (fun p => p.1.name.startsWith "block." || p.1 == sid "decompiles_l2") then
          some "a generated row has a replay text"
        else none
      | .error e => some s!"replayStore failed: {e}" },
  { name := "toysum.replay.refinesL3.noIntro", check := onReal fun src =>
      match Skel.Toy.Sum.replayStore src with
      | .ok st => match st.find? (fun p => p.1 == sid "refines_l3") with
        | some (_, t) => if occurs "intro p" (String.ofList (t.toList.take 20)) then some "a binder-free statement gets an intro" else none
        | none => some "no replay text for refines_l3"
      | .error e => some s!"replayStore failed: {e}" },
  mustFail "toysum.sources.emptySum" "In2" fun s => { s with sum := "" },
  { name := "toysum.sources.sitesUnused", check := onReal fun src =>
      match Skel.Toy.Sum.generate src, Skel.Toy.Sum.generate { src with sites := "" } with
      | .ok a, .ok b =>
        eqMsg (a.modelText, a.obligations.map (·.statement)) (b.modelText, b.obligations.map (·.statement))
      | .error e, _ => some s!"generate failed: {e}"
      | _, .error e => some s!"generate with no sites failed: {e}" },
  mustFail "toysum.sources.missingBlocksP" "blocksP" fun s =>
    { s with sum := s.sum.replace "def blocksP" "def blocksQ" }
]

/-- Whether the test with `name` runs: all tests when `only` is `none`, else the names that start with `only`. -/
private def selected (only : Option String) (name : String) : Bool :=
  match only with
  | none => true
  | some prefixName => name.startsWith prefixName

/-- Runs the tests whose name starts with `only` (all when `only` is `none`). Prints one line for each failed test,
and gives the number of failed tests. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  let mut failed := 0
  for t in tests do
    if selected only t.name then
      let msg ← try t.check catch e => pure (some s!"exception: {e}")
      if let some m := msg then
        IO.println s!"FAIL {t.name}: {m}"
        failed := failed + 1
  return failed

end ToySumTests
