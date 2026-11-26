import Skel.Ledger

/-! The tests of `Skel/Ledger.lean` (suite `ledger`): `lake exe skel-test --only ledger`. Each check is a value that must
hold. A check that does not hold prints one `FAIL` line. The property draws `cases` cases, the case `i` from the generator
of seed `seed + i`: a ledger with up to three random results applied, and one more random result. A case where `apply`
changes another record, or does not add exactly one attempt to the record of the pending candidate, prints one `FAIL`
line. The suite gives the number of failed checks and failed cases. -/

namespace LedgerTests

open Skel

/-- The configuration of the tests: the strict gate, a limit of 30000 ms, seed 7 and 200 samples. -/
def cfg : Config := { gate := .strict, limitMs := 30000, seed := 7, samples := 200 }

/-- The identity of an obligation of the function `f` with the statement name `name`. -/
def oid (name : String) : ObId := { function := "f", name := name }

/-- A block obligation with the name `name`, no dependency and the claim `claim`. -/
def ob (name : String) (claim : Claim := .none) : Obligation :=
  { id := oid name, cls := .block, origin := .unit, statement := s!"theorem {name}", deps := [], claim := claim }

/-- A triple, and a second triple that differs from it. -/
def triple : Triple := { inv := "True", measure := "0", result := "0" }
def triple2 : Triple := { inv := "x.i.toNat ≤ xs.length", measure := "xs.length - x.i.toNat", result := "x.acc" }

/-- A counterexample of the obligation `a` on the subject `subject`. -/
def cexOf (subject : Subject) : Cex :=
  { ob := oid "a", subject := subject, seed := 1, index := 2, shown := "s", why := "w" }

/-- A counterexample to the claim of `a`, and one to the triple `triple`. -/
def claimCex : Cex := cexOf .claim
def tripleCex : Cex := cexOf (.triple triple)

/-- A proof candidate on the replay rung. -/
def proofCand (text : String) : Candidate := .proof .replay text

/-- A pending candidate of the obligation `name`. -/
def pend (name : String) (c : Candidate) : Pending := { ob := oid name, candidate := c }

/-- A check result with the axioms `axs`. -/
def acc (axs : List String) : Result := .checked (.accepted axs)

/-- The status of a record closed on the rung `replay` with the proof `t`, the axiom `propext`, the triple `tr` and the
time `ms`. -/
def closedWith (tr : Option (InvRung × Triple)) (ms : Nat) : Status :=
  .closed { rung := .replay, triple := tr, proof := "t", axioms := ["propext"], ms := ms }

/-- The status of a record closed without a triple at `ms` milliseconds. -/
def closedStatus (ms : Nat) : Status := closedWith none ms

/-- The status of the record of `id`, or `none` when there is no record. -/
def statusOf (l : Ledger) (id : ObId) : Option Status :=
  (l.records.find? (·.ob.id == id)).map (·.status)

/-- The attempts of the record of `id`, newest first; `[]` when there is no record. -/
def attemptsOf (l : Ledger) (id : ObId) : List Attempt :=
  ((l.records.find? (·.ob.id == id)).map (·.attempts)).getD []

/-- Two records are the same: the same obligation (by its `repr`), the same status and the same attempts. -/
def sameRecord (a b : Record) : Bool :=
  reprStr a.ob == reprStr b.ob && a.status == b.status && a.attempts == b.attempts

/-- Two ledgers are the same: the same records in the same order. -/
def sameLedger (a b : Ledger) : Bool :=
  a.records.size == b.records.size &&
    (a.records.toList.zip b.records.toList).all fun (x, y) => sameRecord x y

/-- A ledger of the obligations `a` and `b`, all pending. -/
def ledger2 : Ledger := Ledger.init [ob "a", ob "b"]

/-- The pending proof candidate of `a`. -/
def pa : Pending := pend "a" (proofCand "t")

/-- The ledger after `a` is closed with the axiom `propext` at 5 ms. -/
def closedA : Ledger := Ledger.apply cfg ledger2 pa (acc ["propext"]) 5

/-- The ledger after two time-outs and a failure of `a`: the newest attempt has 2 ms. -/
def twoFails : Ledger :=
  Ledger.apply cfg (Ledger.apply cfg ledger2 pa (.checked (.failed ["e"])) 1) pa (.checked (.timedOut 100)) 2

/-- The ledger after a pass of the triple `triple` (template rung) and then of `triple2` (replay rung) on `a`. -/
def twoPasses : Ledger :=
  let l1 := Ledger.apply cfg ledger2 (pend "a" (.triple .template triple)) (.refuted (.pass 200)) 1
  Ledger.apply cfg l1 (pend "a" (.triple .replay triple2)) (.refuted (.pass 200)) 2

/-- The results that the property draws from: every kind of check outcome and every kind of verdict. -/
def resultPool : Array Result :=
  #[.checked (.accepted ["propext"]), .checked (.accepted ["sorryAx"]), .checked (.failed ["e"]),
    .checked (.timedOut 100), .checked (.gateRefused ["t._native.bv_decide.ax_1_5"]),
    .refuted (.pass 200), .refuted (.real (cexOf .claim)), .refuted (.cti (cexOf .claim)),
    .refuted (.real (cexOf (.triple triple))), .refuted (.cti (cexOf (.triple triple)))]

/-- The candidates that the property draws from: each rung and each invariant rung. -/
def candidatePool : Array Candidate :=
  #[.proof .liftBlock "by lift_block", .proof .replay "t", .proof .closing "by simp",
    .triple .template triple, .triple .replay triple2]

/-- An element of `xs` drawn by `g` (`x0` when `xs` is empty), and the next generator. -/
def pick {α : Type} (xs : Array α) (x0 : α) (g : StdGen) : α × StdGen :=
  let (i, g) := randNat g 0 (xs.size - 1)
  (xs.getD i x0, g)

/-- A case of the property: a ledger of 1 to 4 obligations `o0`, `o1`, ... with up to three random results applied, the
pending candidate of one obligation, its result and its time. -/
def genCase (g : StdGen) : Ledger × Pending × Result × Nat :=
  let (n, g) := randNat g 1 4
  let obs := (List.range n).map fun i => ob s!"o{i}"
  let (steps, g) := randNat g 0 3
  let (l, g) := (List.range steps).foldl (fun (acc : Ledger × StdGen) _ =>
      let (i, g) := randNat acc.2 0 (n - 1)
      let (c, g) := pick candidatePool (proofCand "") g
      let (r, g) := pick resultPool (.checked (.failed [])) g
      (Ledger.apply cfg acc.1 (pend s!"o{i}" c) r 1, g)) (Ledger.init obs, g)
  let (i, g) := randNat g 0 (n - 1)
  let (c, g) := pick candidatePool (proofCand "") g
  let (r, g) := pick resultPool (.checked (.failed [])) g
  let (ms, _) := randNat g 0 1000
  (l, pend s!"o{i}" c, r, ms)

/-- `apply` on one case: the records keep their order and their size; every other record is the same; the record of the
pending candidate has its obligation, and the new attempt on top of its old attempts. -/
def caseOk (l : Ledger) (p : Pending) (r : Result) (ms : Nat) : Bool :=
  let l' := Ledger.apply cfg l p r ms
  let pairs := l.records.toList.zip l'.records.toList
  let newAttempt : Attempt := { candidate := p.candidate, result := r, ms := ms }
  l'.records.size == l.records.size &&
    pairs.all (fun (a, b) => a.ob.id == p.ob || sameRecord a b) &&
    pairs.all (fun (a, b) => a.ob.id != p.ob ||
      (reprStr a.ob == reprStr b.ob && b.attempts == newAttempt :: a.attempts))

/-- The checks of the ledger, each with its name. -/
def checks : List (String × Bool) :=
  [ ("init gives all records pending",
      (Ledger.init [ob "a", ob "b"]).records.all (fun r => r.status == .pending)),
    ("init keeps the order of the obligations",
      ((Ledger.init [ob "a", ob "b"]).records.toList.map (·.ob.id.name)) == ["a", "b"]),
    ("init gives one record for each obligation", (Ledger.init [ob "a", ob "b"]).records.size == 2),
    ("init of an empty list is finished", Ledger.finished (Ledger.init [])),
    ("init of two obligations is not finished", !Ledger.finished ledger2),
    ("accepted with the strict gate closes the record",
      statusOf closedA (oid "a") == some (closedStatus 5)),
    ("accepted closes no other record", statusOf closedA (oid "b") == some .pending),
    ("accepted adds one attempt", (attemptsOf closedA (oid "a")).length == 1),
    ("accepted with a bv_decide axiom stays pending under strict",
      statusOf (Ledger.apply cfg ledger2 pa (acc ["t._native.bv_decide.ax_1_5"]) 5) (oid "a") == some .pending),
    ("accepted with sorryAx stays pending",
      statusOf (Ledger.apply cfg ledger2 pa (acc ["sorryAx"]) 5) (oid "a") == some .pending),
    ("gateRefused stays pending",
      statusOf (Ledger.apply cfg ledger2 pa (.checked (.gateRefused ["t._native.bv_decide.ax_1_5"])) 5) (oid "a")
        == some .pending),
    ("gateRefused adds one attempt",
      (attemptsOf (Ledger.apply cfg ledger2 pa (.checked (.gateRefused ["sorryAx"])) 5) (oid "a")).length == 1),
    ("failed keeps pending", statusOf twoFails (oid "a") == some .pending),
    ("failed and timedOut add their attempts", (attemptsOf twoFails (oid "a")).length == 2),
    ("timedOut keeps pending", statusOf (Ledger.apply cfg ledger2 pa (.checked (.timedOut 100)) 5) (oid "a")
      == some .pending),
    ("an unknown id gives the same ledger",
      sameLedger (Ledger.apply cfg ledger2 (pend "zz" (proofCand "t")) (acc ["propext"]) 5) ledger2),
    ("history gives the attempts newest first",
      ((Ledger.history twoFails (oid "a")).attempts.map (·.ms)) == [2, 1]),
    ("history of an unknown id has no attempts and no counterexamples",
      (Ledger.history ledger2 (oid "zz")).attempts.isEmpty && (Ledger.history ledger2 (oid "zz")).cexs.isEmpty),
    ("real on the claim refutes the record",
      statusOf (Ledger.apply cfg ledger2 pa (.refuted (.real claimCex)) 3) (oid "a") == some (.refuted claimCex)),
    ("real on the claim adds one attempt",
      (attemptsOf (Ledger.apply cfg ledger2 pa (.refuted (.real claimCex)) 3) (oid "a")).length == 1),
    ("cti on the claim gives no status change",
      statusOf (Ledger.apply cfg ledger2 pa (.refuted (.cti claimCex)) 3) (oid "a") == some .pending),
    ("pass on the claim gives no status change",
      statusOf (Ledger.apply cfg ledger2 pa (.refuted (.pass 200)) 3) (oid "a") == some .pending),
    ("real on a triple gives no status change",
      statusOf (Ledger.apply cfg ledger2 pa (.refuted (.real tripleCex)) 3) (oid "a") == some .pending),
    ("real on a triple goes to the history",
      (Ledger.history (Ledger.apply cfg ledger2 pa (.refuted (.real tripleCex)) 3) (oid "a")).cexs
        == [tripleCex]),
    ("cti on a triple goes to the history",
      (Ledger.history (Ledger.apply cfg ledger2 pa (.refuted (.cti tripleCex)) 3) (oid "a")).cexs
        == [tripleCex]),
    ("a checked accepted on a triple candidate closes nothing",
      statusOf (Ledger.apply cfg ledger2 (pend "a" (.triple .template triple)) (acc ["propext"]) 5) (oid "a")
        == some .pending),
    ("closed takes the triple of the newest pass",
      statusOf (Ledger.apply cfg twoPasses pa (acc ["propext"]) 5) (oid "a")
        == some (closedWith (some (.replay, triple2)) 5)),
    ("closed has no triple without a pass", statusOf closedA (oid "a") == some (closedWith none 5)),
    ("failed on a closed record keeps it closed",
      statusOf (Ledger.apply cfg closedA pa (.checked (.failed ["e"])) 6) (oid "a") == some (closedStatus 5)),
    ("failed on a closed record adds its attempt",
      (attemptsOf (Ledger.apply cfg closedA pa (.checked (.failed ["e"])) 6) (oid "a")).length == 2),
    ("accepted on a closed record keeps the first closure",
      statusOf (Ledger.apply cfg closedA pa (acc ["propext"]) 9) (oid "a") == some (closedStatus 5)),
    ("real on the claim of a closed record keeps it closed",
      statusOf (Ledger.apply cfg closedA pa (.refuted (.real claimCex)) 9) (oid "a") == some (closedStatus 5)),
    ("finished needs every record final",
      !Ledger.finished closedA && Ledger.finished (Ledger.apply cfg (Ledger.init [ob "a"]) pa (acc ["propext"]) 5)),
    ("finished counts blocked as finished",
      Ledger.finished ⟨#[{ ob := ob "a", status := .blocked [oid "b"], attempts := [] }]⟩),
    ("finished counts open as finished",
      Ledger.finished ⟨#[{ ob := ob "a", status := .«open» (Search.ofHistory cfg ⟨[], []⟩), attempts := [] }]⟩),
    ("Search.ofHistory of an empty history",
      Search.ofHistory cfg ⟨[], []⟩ ==
        { candidates := 0, timeouts := 0, seed := 7, samples := 200, limitMs := 30000 }),
    ("Search.ofHistory counts the attempts and the time-outs",
      Search.ofHistory cfg (Ledger.history twoFails (oid "a")) ==
        { candidates := 2, timeouts := 1, seed := 7, samples := 200, limitMs := 30000 })
  ]

/-- The property failures: the case numbers where `caseOk` does not hold, for the `cases` cases from `seed`. -/
def propertyFailures (seed cases : Nat) : List Nat :=
  (List.range cases).filter fun i =>
    let (l, p, r, ms) := genCase (mkStdGen (seed + i))
    !caseOk l p r ms

/-- Gives the number of failed checks and failed cases. The suite runs when `only` is none or `ledger`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "ledger" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  ledger: {name}"
  for i in propertyFailures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  ledger: apply breaks the property in case {i} (seed {seed + i})"
  return failed

end LedgerTests
