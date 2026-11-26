import Skel.Report
import Skel.Ledger

/-! The tests of `Skel/Report.lean` (suite `report`): `lake exe skel-test --only report`. Each check is a value that must
hold. A check that does not hold prints one `FAIL` line. The property draws `cases` ledgers, the case `i` from the generator
of seed `seed + i`: up to five records, each pending, blocked, refuted, closed on a random rung, or open with a random
number of candidates. A case where `belowReplay` is above `total`, where `total` is not the number of records, where
`belowReplay` is not the number of closed records below the rung `replay`, or where the number of lines is not the number
of records plus two, prints one `FAIL` line. The suite gives the number of failed checks and failed cases. -/

namespace ReportTests

open Skel

/-- The configuration of the tests: the strict gate, a limit of 30000 ms, seed 7 and 200 samples. -/
def cfg : Config := { gate := .strict, limitMs := 30000, seed := 7, samples := 200 }

/-- The identity of an obligation with the statement name `name` in the function `f`. -/
def oid (name : String) : ObId := { function := "f", name := name }

/-- A block obligation with the name `name`, no dependency and no claim. -/
def ob (name : String) : Obligation :=
  { id := oid name, cls := .block, origin := .unit, statement := s!"theorem {name}", deps := [], claim := .none }

/-- A triple, and the counterexample of the claim of `a`. -/
def triple : Triple := { inv := "True", measure := "0", result := "0" }
def claimCex : Cex := { ob := oid "a", subject := .claim, seed := 1, index := 2, shown := "s", why := "w" }

/-- A pending candidate of the obligation `name`. -/
def pend (name : String) (c : Candidate) : Pending := { ob := oid name, candidate := c }

/-- A check result with the axioms `axs`. -/
def acc (axs : List String) : Result := .checked (.accepted axs)

/-- A record of the obligation `name` with the status `s` and no attempts. -/
def rec (name : String) (s : Status) : Record := { ob := ob name, status := s, attempts := [] }

/-- An open record of the obligation `name` with `n` failed attempts; its search is the search of its history. -/
def openRec (name : String) (n : Nat) : Record :=
  let attempt : Attempt := { candidate := .proof .replay "t", result := .checked (.failed ["e"]), ms := 1 }
  let h : History := ⟨List.replicate n attempt, []⟩
  { ob := ob name, status := .«open» (Search.ofHistory cfg h), attempts := h.attempts }

/-- A ledger with two closed records: `a` on the rung `liftBlock` and `b` on the rung `replay`. -/
def closedLedger : Ledger :=
  let l0 := Ledger.init [ob "a", ob "b"]
  let l1 := Ledger.apply cfg l0 (pend "a" (.proof .liftBlock "by lift_block")) (acc ["propext"]) 5
  Ledger.apply cfg l1 (pend "b" (.proof .replay "t")) (acc ["propext", "Quot.sound"]) 7

/-- A ledger with one open record `c` of three attempts. -/
def openLedger : Ledger := ⟨#[openRec "c" 3]⟩

/-- A ledger with the two closed records, then a pending `p`, a refuted `r` and a blocked `k` record. -/
def mixedLedger : Ledger :=
  ⟨closedLedger.records ++ #[rec "p" .pending, rec "r" (.refuted claimCex), rec "k" (.blocked [oid "p"])]⟩

/-- A ledger with one record `a` closed on the rung `replay` with the triple `triple` (template rung) and no axioms. -/
def tripleLedger : Ledger :=
  let l1 := Ledger.apply cfg (Ledger.init [ob "a"]) (pend "a" (.triple .template triple)) (.refuted (.pass 200)) 1
  Ledger.apply cfg l1 (pend "a" (.proof .replay "t")) (acc []) 2

/-- The lines of the report of the ledger `l`. -/
def linesOf (l : Ledger) : List String := (Report.render (Report.ofLedger l)).splitOn "\n"

/-- The words of a line, separated by spaces. -/
def cells (line : String) : List String := (line.splitOn " ").filter (· != "")

/-- The cells of the header line. -/
def headerRow : List String := ["id", "class", "status", "rung", "triple", "attempts", "text", "axioms"]

/-- The rungs that the generator draws from. -/
def rungPool : Array Rung := #[.liftBlock, .closing, .model, .replay]

/-- A random record of the obligation `name`: pending, blocked, refuted, closed on a random rung, or open with a random
number of candidates. -/
def genRecord (g : StdGen) (name : String) : Record × StdGen :=
  let (k, g) := randNat g 0 4
  let (r, g) := randNat g 0 3
  let (n, g) := randNat g 0 5
  let status : Status := match k with
    | 0 => .pending
    | 1 => .blocked [oid "x"]
    | 2 => .refuted claimCex
    | 3 => .closed { rung := rungPool.getD r .replay, triple := none, proof := "t", axioms := ["propext"], ms := 1 }
    | _ => .«open» { candidates := n, timeouts := 0, seed := 7, samples := 200, limitMs := 30000 }
  ({ ob := ob name, status := status, attempts := [] }, g)

/-- A random ledger of up to five records. -/
def genLedger (g : StdGen) : Ledger :=
  let (n, g) := randNat g 0 5
  let (recs, _) := (List.range n).foldl (fun (acc : Array Record × StdGen) i =>
      let (r, g') := genRecord acc.2 s!"o{i}"
      (acc.1.push r, g')) (#[], g)
  ⟨recs⟩

/-- The number of closed records whose rung is not `replay`, counted from the records. -/
def closedBelow (l : Ledger) : Nat :=
  l.records.toList.countP fun r =>
    match r.status with
    | .closed c => c.rung != .replay
    | _ => false

/-- The checks of the report, each with its name. -/
def checks : List (String × Bool) :=
  [ ("an empty ledger gives below replay 0 of 0",
      (linesOf (Ledger.init [])).getLast? == some "below replay: 0 of 0"),
    ("an empty ledger gives the header and the below replay line only",
      (linesOf (Ledger.init [])).map cells == [headerRow, ["below", "replay:", "0", "of", "0"]]),
    ("two closed rows, liftBlock and replay, give below replay 1 of 2",
      (linesOf closedLedger).getLast? == some "below replay: 1 of 2"),
    ("two closed rows give B 1 and T 2",
      (Report.ofLedger closedLedger).belowReplay == 1 && (Report.ofLedger closedLedger).total == 2),
    ("the first line is the only header line",
      (linesOf closedLedger).head?.map cells == some headerRow &&
        ((linesOf closedLedger).filter (fun l => cells l == headerRow)).length == 1),
    ("a report has the rows plus two lines",
      (linesOf closedLedger).length == 4 && (linesOf mixedLedger).length == 7 && (linesOf openLedger).length == 3),
    ("a closed row shows its rung and its axioms",
      (linesOf closedLedger)[1]?.map cells == some ["f.a", "block", "closed", "liftBlock", "-", "1", "lift_block", "propext"] &&
        (linesOf closedLedger)[2]?.map cells ==
          some ["f.b", "block", "closed", "replay", "-", "1", "t", "propext", "Quot.sound"]),
    ("a closed row with no axioms ends with its text",
      (linesOf (Ledger.apply cfg (Ledger.init [ob "a"]) (pend "a" (.proof .replay "t")) (acc []) 1))[1]?.map cells
        == some ["f.a", "block", "closed", "replay", "-", "1", "t"]),
    ("a closed row with a triple shows the triple rung",
      (linesOf tripleLedger)[1]?.map cells == some ["f.a", "block", "closed", "replay", "template", "2", "t"]),
    ("an open row shows open and its candidates",
      (linesOf openLedger)[1]?.map cells == some ["f.c", "block", "open", "-", "-", "3", "-"]),
    ("an open row is not below replay",
      (Report.ofLedger openLedger).belowReplay == 0 && (Report.ofLedger openLedger).total == 1),
    ("a pending, a refuted and a blocked row count in T and not in B",
      (Report.ofLedger mixedLedger).belowReplay == 1 && (Report.ofLedger mixedLedger).total == 5),
    ("a pending, a refuted and a blocked row show their status",
      (((linesOf mixedLedger).drop 3).take 3).map (fun l => (cells l)[2]?) ==
        [some "pending", some "refuted", some "blocked"]),
    ("the rows are in the order of the ledger",
      (((linesOf mixedLedger).drop 1).take 5).map (fun l => (cells l).head?) ==
        [some "f.a", some "f.b", some "f.p", some "f.r", some "f.k"]),
    ("no line ends with a space", (linesOf mixedLedger).all fun l => !(l.endsWith " ")),
    -- the tag of the closing text (N14)
    ("the tag of the split block proof", proofTag "by intros; lift_block_split" == "lift_block_split"),
    ("the tag of the block proof", proofTag "by intros; lift_block" == "lift_block"),
    ("the tag of a proof with lines is the first word of its first tactic", proofTag "by\n  refine Decompiles.ofBlocks b" == "refine"),
    ("the tag of a closing text", proofTag "by intros; simp" == "intros" && proofTag "by simp" == "simp"),
    ("the tag of an empty text", proofTag "" == "-" && proofTag "by" == "-")
  ]

/-- The property failures: the case numbers where the report breaks the property, for the `cases` cases from `seed`. -/
def propertyFailures (seed cases : Nat) : List Nat :=
  (List.range cases).filter fun i =>
    let l := genLedger (mkStdGen (seed + i))
    let rep := Report.ofLedger l
    !(rep.belowReplay ≤ rep.total && rep.total == l.records.size &&
      rep.belowReplay == closedBelow l && (linesOf l).length == l.records.size + 2)

/-- Gives the number of failed checks and failed cases. The suite runs when `only` is none or `report`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "report" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  report: {name}"
  for i in propertyFailures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  report: the report breaks the property in case {i} (seed {seed + i})"
  return failed

end ReportTests
