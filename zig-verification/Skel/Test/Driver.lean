import Skel.Driver

/-! The tests of `Skel/Driver.lean` (suite `driver`): `lake exe skel-test --only driver`. The pure checks use a
synthetic generator (statements are the names of the rows, the model text is `MODEL`, a refute text starts with
`REFUTE`) and the 14 rows of the table of `toySum`. A pure fake answers each action of the driver's step function. The IO
checks read `Lift/Spike/Sum.lean` and `Lift/Spike/Sites/Sum.lean` from the repository root; no Lean subprocess runs.
A check that does not hold prints one `FAIL` line. The property draws `cases` cases, the case `i` from the seed
`seed + i`. The suite gives the number of failed checks and cases. -/

namespace DriverTests

open Skel Skel.Driver
open Skel.Toy.Sum (rows sumId Sources template1 template2 templateTriples)

/-- The configuration of the tests: the strict gate, a limit of 4321 ms, seed 7 and 200 samples. -/
def cfg : Config := { gate := .strict, limitMs := 4321, seed := 7, samples := 200 }

/-- The 14 obligations of `toySum`, each with its id as statement. -/
def obs : List Obligation :=
  rows.map fun r =>
    { id := r.id, cls := r.cls, origin := r.origin, statement := s!"S_{r.id.name}", deps := r.deps, claim := r.claim }

/-- A synthetic generator. -/
def gen : Generated :=
  { modelText := "MODEL", obligations := obs,
    refuteText := fun ob c => some s!"REFUTE {ob.name} {reprStr c}" }

/-- The environment of the tests with the fault `f`. -/
def envWith (f : Skel.Fault) : Env := { cfg := cfg, fault := f, gen := gen }

/-- The environment with no fault. -/
def env : Env := envWith .none

/-- A hand triple for the replay rung (a text that differs from both templates). -/
def hand : Triple := { template2 with inv := "x.rcx.toNat ≤ xs.length ∧ True" }

/-- The ladders of the tests: the real rungs, a replay text for each row. -/
def lad : Ladders := ladders templateTriples { l2PlusText := "", l3Text := "", loopRule := "" } [] (rows.map fun r => (r.id, s!"by replay {r.id.name}")) [] hand

/-- The obligation of the row `name`. -/
def obOf (name : String) : Obligation :=
  match obs.find? (·.id == sumId name) with
  | some o => o
  | none => { id := sumId name, cls := .total, origin := .unit, statement := "", deps := [], claim := .none }

/-- Whether `s` has `sub` as a substring. -/
def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The position of the first occurrence of `sub` in `s`, as the length of the text before it. -/
def posOf (s sub : String) : Option Nat :=
  match s.splitOn sub with
  | a :: _ :: _ => some a.length
  | _ => none

/-- Whether `a` occurs in `s` before `b`. Both must occur. -/
def before (s a b : String) : Bool :=
  match posOf s a, posOf s b with
  | some i, some j => decide (i < j)
  | _, _ => false

/-- A closed record for the answer `proof`. -/
def closedWith (proof : String) : Status :=
  .closed { rung := .liftBlock, triple := none, proof := proof, axioms := ["propext"], ms := 1 }

/-- The ledger of the table in which the rows `names` are closed (proof `P_<name>`) and the others are pending. -/
def ledgerClosed (names : List String) : Ledger :=
  ⟨(Ledger.init obs).records.map fun r =>
    if names.contains r.ob.id.name then { r with status := closedWith s!"P_{r.ob.id.name}" } else r⟩

/-- A passed triple attempt. -/
def passAttempt (t : Triple) : Attempt :=
  { candidate := .triple .template t, result := .refuted (.pass 200), ms := 1 }

/-- The fake: the check of a pending gives an outcome, the refute gives a verdict. T1 gives `cti`; everything else passes
and is accepted. -/
def cexOf (p : Pending) : Cex :=
  { ob := p.ob, subject := (match p.candidate with | .triple _ t => .triple t | _ => .claim),
    seed := 7, index := 3, shown := "s", why := "w" }

/-- A `cti` attempt of a triple of the row `loop`. -/
def ctiAttempt (t : Triple) : Attempt :=
  let p : Pending := { ob := sumId "loop", candidate := .triple .template t }
  { candidate := p.candidate, result := .refuted (.cti (cexOf p)), ms := 1 }

/-- The ledger of the table with the row `loop` holding the attempts `as`. -/
def ledgerLoop (acts : List Attempt) : Ledger :=
  ⟨(Ledger.init obs).records.map fun r => if r.ob.id == sumId "loop" then { r with attempts := acts } else r⟩

/-- The `render` of the environment `e` on the row `name` with the candidate `c`, with the ledger `l`. -/
def renderOn (e : Env) (l : Ledger) (name : String) (c : Candidate) : LeanFile := render e l (obOf name) c

/-- The text of the check file of the row `name` with the proof text `p` of the rung `closing`. -/
def checkOn (e : Env) (l : Ledger) (name p : String) : LeanFile := renderOn e l name (.proof .closing p)

/-- The verdict of the fake. -/
def verdict (p : Pending) : Verdict :=
  match p.candidate with
  | .triple _ t => if t == template1 then .cti (cexOf p) else .pass 200
  | _ => .pass 200

/-- The actions of a run of the step function of the driver with the fake, until `done`; `none` when the fuel ends. -/
def drive (e : Env) (ls : Ladders) : Nat → Ledger → Event → List Action → Option (List Action × Ledger)
  | 0, _, _, _ => none
  | n + 1, l, ev, acc =>
    let (l', a) := stepFn e ls l ev
    match a with
    | .check p _ => drive e ls n l' (.checked p (.accepted ["propext"]) 1) (a :: acc)
    | .refute p _ => drive e ls n l' (.refuted p (verdict p) 1) (a :: acc)
    | .ask p _ => drive e ls n l' (.answered p none 1) (a :: acc)
    | .weaken .. => drive e ls n l' .start (a :: acc)
    | .done _ => some ((a :: acc).reverse, l')

/-- The run of the fake from the start. -/
def runAll (e : Env) (ls : Ladders) : Option (List Action × Ledger) := drive e ls 2000 (Ledger.init obs) .start []

/-- The files of the check actions of a run. -/
def checkFiles (acts : List Action) : List (ObId × LeanFile) :=
  acts.filterMap fun a => match a with
    | .check p f => some (p.ob, f)
    | _ => none

/-- The files of the refute actions of a run. -/
def refuteFiles (acts : List Action) : List (Pending × LeanFile) :=
  acts.filterMap fun a => match a with
    | .refute p f => some (p, f)
    | _ => none

/-- Whether the whole word `w` occurs in `s`, with letters and digits and `_` as word characters. -/
def hasWord (s w : String) : Bool :=
  let isW (c : Char) : Bool := c.isAlphanum || c == '_'
  let rec go : List Char → Bool
    | [] => false
    | cs@(_ :: rest) =>
      let wl := w.toList
      (cs.take wl.length == wl && (cs.drop wl.length).head?.all (fun c => !isW c)) || go rest
  -- the character before a hit is not checked: the slots are upper-case words in a text that has none of that form
  go s.toList

/-- The slot words of the loop skeleton. -/
def slotWords : List String := ["INV", "MEASURE", "RESULT", "STEP"]

/-! The checks. -/

/-- The tail of a ledger-free fault run: the files of the loop row in a full run. -/
def loopCheckFiles (e : Env) : List LeanFile :=
  match runAll e lad with
  | some (acts, _) => (checkFiles acts).filterMap fun (id, f) => if id == sumId "loop" then some f else none
  | none => []

/-- A message of the given severity. -/
def msg (severity : NxLift.Severity) (text : String) : NxLift.Message :=
  { severity := severity, file := "f.lean", line := 1, col := 0, text := text }

/-- The pure checks, each with its name. -/
def checks : List (String × Bool) :=
  let entry := checkOn env (Ledger.init obs) "block.entry" "by simp_all"
  let claimF := renderOn env (Ledger.init obs) "refines_l3" claimCandidate
  let tripleF := renderOn env (Ledger.init obs) "loop" (.triple .template template1)
  let l5 := ledgerClosed ["block.entry", "block.LBB1_1", "block.o9", "block.LBB1_3"]
  let row5 := checkOn env l5 "decompiles_l2" "by exact h"
  let l13 := ledgerClosed ["block.entry", "block.LBB1_1", "block.o9", "block.LBB1_3", "decompiles_l2", "refines_l2p",
    "above_l2p", "refines_l3", "above_l3", "decompiles", "total"]
  let row13 := checkOn env l13 "decompiles_code" "by exact h"
  let kept := ledgerLoop [passAttempt hand, passAttempt template1]
  let loopF := checkOn env kept "loop" (loopProof "S_loop" hand)
  let loopText := checkOn env kept "loop" "by intros; exact ⟨_, rfl⟩"
  let loopNone := checkOn env (ledgerLoop []) "loop" "by simp_all"
  let loopCti := checkOn env (ledgerLoop [ctiAttempt template1]) "loop" "by simp_all"
  let slowT := checkOn (envWith (.slow "total")) (Ledger.init obs) "total" "by simp_all"
  let slowOther := checkOn (envWith (.slow "total")) (Ledger.init obs) "block.entry" "by simp_all"
  let slowClaim := renderOn (envWith (.slow "refines_l3")) (Ledger.init obs) "refines_l3" claimCandidate
  let slowReplay := checkOn (envWith (.slow "block.entry")) (Ledger.init obs) "block.entry" "by exact (rfl : 0 = 1)"
  [ -- which kind of file
    ("a closing candidate gives a check file", has entry.text "#print axioms block.entry" && !has entry.text "REFUTE"),
    ("the check file of a block row has its theorem in a namespace", has entry.text "namespace block\ntheorem entry : S_block.entry := by simp_all\nend block"),
    ("the check file has the model text and its imports", has entry.text "MODEL" && has entry.text "import Lift.Tactic.Block" &&
      has entry.text "import Std.Tactic.BVDecide" && has entry.text "namespace Skel.Gen.Sum" && has entry.text "end Skel.Gen.Sum"),
    ("the check file does not import a hand module",
      !has entry.text "import Lift.Spike.Sum" && !has entry.text "import Lift.Spike.Sites.Sum"),
    ("the check file name is the full theorem name", entry.name == "Skel.Gen.Sum.block.entry"),
    ("the check file has the limit of the config", entry.limitMs == cfg.limitMs),
    ("the claim candidate gives a refute file", has claimF.text "REFUTE refines_l3" && !has claimF.text "#print axioms"),
    ("the claim candidate gives the name refute of the row", claimF.name == "Skel.Gen.Sum.refute.refines_l3"),
    ("the refute file has the limit of the config", claimF.limitMs == cfg.limitMs),
    ("a triple candidate gives a refute file", has tripleF.text "REFUTE loop" && !has tripleF.text "#print axioms"),
    ("a triple candidate gives a name below the row", has tripleF.name "Skel.Gen.Sum.refute.loop."),
    ("two triples give two names", (renderOn env (Ledger.init obs) "loop" (.triple .template template2)).name != tripleF.name),
    ("the same triple on another rung gives the same name",
      (renderOn env (Ledger.init obs) "loop" (.triple .replay template1)).name == tripleF.name),
    ("a proof with an empty text is the claim candidate: a refute file (boundary)",
      has (renderOn env (Ledger.init obs) "block.entry" (.proof .liftBlock "")).text "REFUTE"),
    ("a proof with a one-space text is a check file (boundary)",
      has (renderOn env (Ledger.init obs) "block.entry" (.proof .liftBlock " ")).text "#print axioms"),
    ("a refute file for a generator with no refute text names the row and has no verdict",
      let g : Generated := { gen with refuteText := fun _ _ => none }
      let f := render { env with gen := g } (Ledger.init obs) (obOf "refines_l3") claimCandidate
      has f.text "refines_l3" && !has f.text "#eval"),
    -- the answers of the deps
    ("the answer names of the block rows are their labels", answerName (obOf "block.entry") == "entry" &&
      answerName (obOf "block.LBB1_3") == "LBB1_3"),
    ("the answer name of another row is its name", answerName (obOf "refines_l2p") == "refines_l2p"),
    ("row 5 has the four block answers, bare and in table order, with no Sites.Sum",
      has row5.text "\ntheorem entry : S_block.entry := P_block.entry\n" && !has row5.text "Sites.Sum" &&
      before row5.text "theorem entry" "theorem LBB1_1" && before row5.text "theorem LBB1_1" "theorem o9" &&
      before row5.text "theorem o9" "theorem LBB1_3" && before row5.text "theorem LBB1_3" "theorem decompiles_l2"),
    ("the answers come after the model text", before row5.text "MODEL" "theorem entry"),
    ("row 5 has no answer of a row that is not a dep", !has row5.text "P_total"),
    ("an open dep gives no answer",
      let l := ledgerClosed ["block.entry", "block.LBB1_1", "block.o9"]
      !has (checkOn env l "decompiles_l2" "by exact h").text "theorem LBB1_3 : S_block.LBB1_3 :="),
    ("a row with no dep has no answer", !has (checkOn env l5 "total" "by simp_all").text "P_block.entry"),
    ("row 13 has the answers of its transitive deps", has row13.text ":= P_decompiles\n" && has row13.text ":= P_above_l3\n" &&
      has row13.text "P_block.entry" && has row13.text ":= P_refines_l3\n"),
    ("row 13 has no answer of a row that is not below it", !has row13.text "P_total"),
    ("the answers of row 13 are in table order", before row13.text "P_decompiles_l2" "P_refines_l2p" &&
      before row13.text "P_refines_l2p" "P_above_l2p" && before row13.text "P_above_l3" ":= P_decompiles\n"),
    -- the loop row
    ("the triple of the loop proof candidate is in the check file", has loopF.text "(x.rcx.toNat ≤ xs.length ∧ True)" &&
      slotWords.all (fun w => !hasWord loopF.text w)),
    ("the check file of a loop row has the loop proof of the candidate", has loopF.text "lift_loop!" &&
      has loopF.text (loopProof "S_loop" hand)),
    ("a loop row with a kept triple in the ledger has the text of the candidate as it is (R12)",
      has loopText.text ":= by intros; exact ⟨_, rfl⟩" && !has loopText.text "lift_loop!"),
    ("a loop row with no kept triple has the candidate as it is", !has loopNone.text "lift_loop!" &&
      has loopNone.text ":= by simp_all"),
    ("a loop row with a cti triple only has the candidate as it is", !has loopCti.text "lift_loop!"),
    ("the check file imports the tactic module", has loopF.text "import Lift.Tactic.LoopClose"),
    ("a loop check file has the loop statement and the theorem loop", has loopF.text "theorem loop : " &&
      has loopF.text "#print axioms loop"),
    -- the faults
    ("slow: a candidate of the row is wrapped", has slowT.text ":= by sleep 600000; exact (by simp_all)"),
    ("slow: another row is not wrapped", !has slowOther.text "sleep"),
    ("slow: the refute file of the row is not wrapped", !has slowClaim.text "sleep"),
    ("slow: the name of the file does not change", slowT.name == "Skel.Gen.Sum.total"),
    ("slow: the replay candidate of the row is wrapped as well", has slowReplay.text "exact (by exact (rfl : 0 = 1))"),
    ("no fault: no sleep", !has (checkOn env (Ledger.init obs) "total" "by simp_all").text "sleep"),
    ("bad-replay changes the store text of its row only",
      let store := rows.map fun r => (r.id, s!"by replay {r.id.name}")
      let s' := applyBadReplay "refines_l2p" store
      s'.length == store.length &&
      s'.lookup (sumId "refines_l2p") == some "by exact (rfl : 0 = 1)" &&
      (s'.filter fun p => p.1 != sumId "refines_l2p") == store.filter fun p => p.1 != sumId "refines_l2p"),
    ("bad-replay of a name that is not in the store changes nothing",
      let store := rows.map fun r => (r.id, s!"by replay {r.id.name}")
      applyBadReplay "nowhere" store == store),
    ("a fault with a row name is accepted", (checkFault obs (.slow "total")).toBool && (checkFault obs (.badReplay "block.entry")).toBool),
    ("no fault is accepted", (checkFault obs .none).toBool),
    ("a slow fault with a name that is not a row is an error", !(checkFault obs (.slow "nowhere")).toBool),
    ("a bad-replay fault with a name that is not a row is an error", !(checkFault obs (.badReplay "nowhere")).toBool),
    ("a fault name with the function prefix is an error", !(checkFault obs (.slow "sum.total")).toBool),
    ("the error of a bad fault names it", (match checkFault obs (.slow "nowhere") with
      | .error m => has m "nowhere"
      | .ok _ => false)),
    -- the step function of the driver
    ("a full run with the fake ends", (runAll env lad).isSome),
    ("a full run closes the 14 rows", match runAll env lad with
      | some (_, l) => l.records.all fun r => match r.status with | .closed _ => true | _ => false
      | none => false),
    ("the loop row is checked with a filled skeleton in a full run",
      let fs := loopCheckFiles env
      !fs.isEmpty && fs.all fun f => has f.text "x.rcx.toNat ≤ xs.length" && slotWords.all (fun w => !hasWord f.text w)),
    ("a full run gives the first check of row 5 the answer of the block that closed just before it",
      match runAll env lad with
      | some (acts, _) =>
        let fs := (checkFiles acts).filter fun (id, _) => id == sumId "decompiles_l2"
        !fs.isEmpty && fs.all fun (_, f) =>
          has f.text "\ntheorem LBB1_3 : S_block.LBB1_3 := by intros; lift_block\n" && !has f.text "Sites.Sum"
      | none => false),
    ("the loop row of a full run uses the triple that passed: T2", (loopCheckFiles env).all fun f => !has f.text "∧ True ∧"),
    ("the loop row of a full run has no `∧ True` of T1 in its invariant",
      (loopCheckFiles env).all fun f => !has f.text "x.input = a ∧ True"),
    ("a full run has a refute of T1 before the refute of T2",
      match runAll env lad with
      | some (acts, _) =>
        let ts := (refuteFiles acts).filterMap fun (p, _) => match p.candidate with | .triple _ t => some t | _ => none
        ts.take 2 == [template1, template2]
      | none => false),
    ("a full run has the claim refute of refines_l3 before its first check",
      match runAll env lad with
      | some (acts, _) =>
        let ks := acts.filterMap fun a => match a with
          | .refute p _ => if p.ob == sumId "refines_l3" then some "refute" else none
          | .check p _ => if p.ob == sumId "refines_l3" then some "check" else none
          | _ => none
        ks.head? == some "refute"
      | none => false),
    ("a bad-replay run: the replay text of the row is the fault text in the store",
      (applyBadReplay "total" [(sumId "total", "by x")]).lookup (sumId "total") == some "by exact (rfl : 0 = 1)"),
    -- the replay of a stored counterexample
    ("replay: no message is still fails", Replay.ofRun (.exited 0) #[] == .stillFails),
    ("replay: an info message is still fails", Replay.ofRun (.exited 0) #[msg .info "x"] == .stillFails),
    ("replay: an error message is no longer fails", Replay.ofRun (.exited 1) #[msg .error "guard failed"] ==
      .noLongerFails ["guard failed"]),
    ("replay: a time-out is a time-out", Replay.ofRun (.timedOut 7) #[] == .timedOut 7),
    ("replay: a time-out wins over an error", Replay.ofRun (.timedOut 7) #[msg .error "e"] == .timedOut 7),
    ("replay: the line of still fails", Replay.line "f.lean" .stillFails == "f.lean: still fails"),
    ("replay: the line of no longer fails", Replay.line "f.lean" (.noLongerFails []) == "f.lean: no longer fails"),
    -- the log of a run
    ("log: an accepted outcome", outcomeText (.accepted ["a", "b"]) == "accepted [a, b]"),
    ("log: a time-out outcome", outcomeText (.timedOut 5) == "timed out after 5 ms"),
    ("log: a failed outcome counts its errors", outcomeText (.failed ["e", "f"]) == "failed (2 errors)"),
    ("log: a verdict line", verdictText (.pass 200) == "pass (200 samples)"),
    ("log: a line has its kind, name, result and time", logLine "check" "n" "r" 5 == "check n r 5 ms")
  ]

/-- The refute targets of a setup built from the synthetic generator: for each refute action of a run, the name
resolves to its row and subject. -/
def targetsOk (ls : Ladders) (e : Env) (fk : Pending → Option Verdict) : Bool :=
  let t := targetsOf e [template1, template2, hand]
  let rec go : Nat → Ledger → Event → Bool
    | 0, _, _ => false
    | n + 1, l, ev =>
      let (l', a) := stepFn e ls l ev
      match a with
      | .check p _ => go n l' (.checked p (.accepted ["propext"]) 1)
      | .refute p f =>
        let subj : Subject := match p.candidate with | .triple _ x => .triple x | _ => .claim
        (t.find? (·.1 == f.name)).map (fun x => x.2 == (p.ob, subj)) == some true &&
          go n l' (.refuted p ((fk p).getD (.pass 1)) 1)
      | .ask p _ => go n l' (.answered p none 1)
      | .weaken .. => go n l' .start
      | .done _ => true
  go 2000 (Ledger.init obs) .start

/-- The targets of the real setup. -/
def realChecks : IO (List (String × Bool)) := do
  let src : Sources :=
    { sum := ← IO.FS.readFile "Lift/Spike/Sum.lean", sites := ← IO.FS.readFile "Lift/Spike/Sites/Sum.lean" }
  let okSetup := setup cfg .none src
  let bad := setup cfg (.badReplay "refines_l2p") src
  let nofn := setup cfg (.slow "nowhere") src
  let empty := setup cfg .none { src with sum := "" }
  let noTpl := setup { cfg with useTemplates := false } .none src
  -- the first proposal of the template rung of a loop row, with an empty history
  let firstTemplate (r : Except String Setup) : Option Proposal :=
    r.toOption.bind fun s => (s.ladders.triple.head?).bind fun (_, p) => p (obOf "loop") ⟨[], []⟩
  let some s := okSetup.toOption | return [("the setup of the real sources is ok", false)]
  let entry := render s.env (Ledger.init s.env.gen.obligations) (obOf "block.entry") (.proof .liftBlock "by intros; lift_block")
  let refuteL3 := render s.env (Ledger.init s.env.gen.obligations) (obOf "refines_l3") claimCandidate
  let hasReplay := (s.ladders.proof.map (·.1)) == [.liftBlock, .closing, .model, .replay]
  let badRep := match bad with
    | .ok b => (b.ladders.proof.getLast?.bind fun (_, p) =>
        p (obOf "refines_l2p") ⟨[], []⟩) == some "by exact (rfl : 0 = 1)"
    | .error _ => false
  let okRep := (s.ladders.proof.getLast?.bind fun (_, p) => p (obOf "refines_l2p") ⟨[], []⟩).any (· != "by exact (rfl : 0 = 1)")
  return
    [ ("the setup of the real sources is ok", true),
      ("the setup has the four proof rungs and the triple rungs template, houdini, model, replay",
        hasReplay && s.ladders.triple.map (·.1) == ([.template, .houdini, .model, .replay] : List InvRung)),
      ("the setup has 14 obligations", s.env.gen.obligations.length == 14),
      ("the bad-replay setup gives the fault text on the replay rung", badRep),
      ("the setup with no fault gives the real replay text", okRep),
      ("a fault with an unknown row is an error", !nofn.toBool),
      ("a setup with empty sources is an error", !empty.toBool),
      ("the setup has the targets of the claim, of the template T1, and of the 15 Houdini candidates (T2 and the hand triple are two of them)",
        s.targets.length == 17),
      ("the setup has a target for each Houdini candidate",
        houdiniSpec.all fun sp => sp.candidates.all fun t => s.targets.any (·.1 == refuteName (obOf "loop").id (.triple t))),
      ("the Houdini candidates are 15 triples, one of them the template T2",
        (houdiniSpec.map (·.candidates.length)) == some 15 && (houdiniSpec.map (·.candidates.contains template2)) == some true),
      ("the setup gives the first template to the template rung of a loop row",
        firstTemplate okSetup == some (.triple template1)),
      ("the setup with no templates gives nothing to the template rung of a loop row", firstTemplate noTpl == none),
      ("the setup with no templates has the targets of the claim and of the 15 Houdini candidates (the hand triple is one of them)",
        (noTpl.toOption.map (·.targets.length)) == some 16),
      ("the setup with no templates keeps the Houdini rung: it gives the full conjunction of atoms first",
        (noTpl.toOption.bind fun st => (st.ladders.triple.find? (·.1 == .houdini)).bind fun (_, p) => p (obOf "loop") ⟨[], []⟩).isSome),
      ("the real check file of a block row has the real statement", has entry.text "theorem entry : " && !has entry.text "MODEL"),
      ("the real check file has the real model text", has entry.text "structure In2" || has entry.text "In2"),
      ("the real refute file of the claim is wired to the refuter", has refuteL3.text "Skel.Refute.refuteClaim"),
      ("the real refute files of the triples have the wired seed and samples",
        match s.env.gen.refuteText (sumId "loop") (.triple .template template1) with
        | some t => has t "7 200" || has t " 7 200"
        | none => false)
    ]

/-- The names that resolve: the property of the refute targets with the fake of the property. -/
def propertyFailures (seed cases : Nat) : List Nat :=
  (List.range cases).filter fun i =>
    let k := seed + i
    let fk : Pending → Option Verdict := fun p =>
      match (hash (k, reprStr p)).toNat % 4 with
      | 0 => some (.real (cexOf p))
      | 1 => some (.cti (cexOf p))
      | _ => none
    !targetsOk lad env fk

/-- Gives the number of failed checks and failed cases. The suite runs when `only` is none or `driver`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "driver" then return 0
  let mut failed := 0
  for (name, ok) in checks ++ (← realChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  driver: {name}"
  if !targetsOk lad env (fun _ => none) then
    failed := failed + 1
    IO.println "FAIL  driver: the refute names of a full run resolve to their targets"
  for i in propertyFailures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  driver: case {i}: a refute name of a run with random verdicts does not resolve"
  return failed

end DriverTests
