import Skel.Gen.HeadTerm
import Skel.Gen.Sampler
import Skel.Gen.Template
import Skel.Report.Level3Pilot
import Skel.Test.GenLoop

/-! The tests of the head term of a loop head (`Skel/Gen/HeadTerm.lean`, task MAP-HEAD; suite `maphead`):
`lake exe skel-test --only maphead`. Each check that does not hold prints one `FAIL` line.

- A toy entry block: the minimum and the maximum of two loads, arithmetic of an input and a load: each has its term.
- Negative: a stack load, a load at a scaled address, a register that is no input, `rsp`, a shift and a signed compare have
  no term (each an error).
- The pilot `mapInPlace`: the value of `r15` at the head `LBB30_1` is the term of the minimum of the loads at `rdi + 24` and
  `rdi + 8`.
- The sampler: a term of one entry load has the text of the head value `.load` (the same value in the refute runs); the term
  of the minimum reads both loads in `a.heap`.
- The templates: a bound with a term head value gives the conjunct `x.r = <term over a>`.
- The plan (PIL-CALL5): a toy loop whose bound is the minimum of two loads has a plan, and the head value of the bound is the
  term of the minimum (`headVal` calls `headTerm`). -/

namespace MapHeadTests

open Skel Skel.Gen

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

def rdiPlus (n : UInt64) : Val := .add (.reg .rdi) (.lit n)

/-- A toy entry block: two loads from `rdi + 8` and `rdi + 24`. -/
def entry : List Access := [.load 0 (rdiPlus 8) .W64, .load 1 (rdiPlus 24) .W64]

def inputs : List Reg64 := [.rdi, .rsi]

def l8 : String := "(match x.input.heap.load (x.input.rdi.toBitVec + 8) .W64 with | .ok v => UInt64.ofBitVec v | _ => 0)"
def l24 : String := "(match x.input.heap.load (x.input.rdi.toBitVec + 24) .W64 with | .ok v => UInt64.ofBitVec v | _ => 0)"

/-- The minimum of the two loads, as `cmovb` gives it: `ite (v1 ≤ v0) v1 v0`. -/
def minVal : Val := .ite (.ule (.load 1) (.load 0)) (.load 1) (.load 0)

def minText : String := s!"(if {l24} ≤ {l8} then {l24} else {l8})"

def isErr (x : Except String String) : Bool := match x with | .error _ => true | .ok _ => false

/-- The blocks of the pilot function `mapInPlace` and the inputs of its summary. -/
def mapBlocks : Option (List Block × List Reg64) :=
  let pu := Skel.Report.Level3.smallUnit
  match pu.fns.find? (·.short == "mapInPlace") with
  | some f =>
    match blocksFrom pu.code (.derived pu.derived) f.entry with
    | .ok bs => some (bs, (vars bs (Skel.Report.Level3.targetOf pu f).callees).inputs)
    | .error _ => none
  | none => none

/-- The term of `r15` of the entry block of `mapInPlace`. -/
def mapR15 : Option (Except String String) := do
  let (bs, ins) ← mapBlocks
  let b ← bs.find? (·.offset == 0)
  let (_, v) ← b.regs.find? (·.1 == .r15)
  pure (headTerm ins b.accesses v)

/-- The plan of `toyFind` with the head value of its bound `rax` (`.input rsi`) replaced by the head value `v`. -/
def findWith (v : HeadVal) : Option UpperPlan :=
  GenLoopTests.findPlan.map fun p =>
    { p with heads := p.heads.map fun h =>
      { h with state := h.state.map fun (r, w) => if r == .rax then (r, v) else (r, w) } }

/-- A toy loop whose bound is the minimum of two loads (PIL-CALL5): the real `toySum` with an entry block that loads the words at
`rdi + 8` and `rdi + 24` and sets the bound `rsi` to their minimum. -/
def minSum : Option Summary := do
  let s ← GenUpperPlanTests.realSummary GenUpperPlanTests.sums "toySum"
  let b0 ← s.blocks.head?
  let n := b0.accesses.length
  let b0' := { b0 with accesses := b0.accesses ++ [.load n (rdiPlus 8) .W64, .load (n + 1) (rdiPlus 24) .W64],
                       regs := (.rsi, .ite (.ule (.load (n + 1)) (.load n)) (.load (n + 1)) (.load n)) :: b0.regs }
  pure (GenUpperPlanTests.mkSummary "minSum" (b0' :: s.blocks.drop 1))

/-- The plan of the toy `minSum`. -/
def minPlan : Except GenError UpperPlan :=
  match minSum with
  | some s => GenUpperPlanTests.runOn s (GenUpperPlanTests.sumFor s) GenUpperPlanTests.hintSum
  | none => .error (.shape 0 "fixture missing")

def pureChecks : List (String × Bool) :=
  [ ("the minimum of two entry loads has its term", (headTerm inputs entry minVal).toOption == some minText),
    ("the maximum of two entry loads has its term",
      (headTerm inputs entry (.ite (.ult (.load 0) (.load 1)) (.load 1) (.load 0))).toOption == some s!"(if {l8} < {l24} then {l24} else {l8})"),
    ("an input plus twice a load has its term",
      (headTerm inputs entry (.add (.reg .rsi) (.mul (.load 0) (.lit 2)))).toOption == some s!"(x.input.rsi + ({l8} * (2 : UInt64)))"),
    ("a negated condition has its term",
      (headTerm inputs entry (.ite (.not (.eq (.load 0) (.lit 0))) (.load 0) (.reg .rsi))).toOption ==
        some s!"(if ¬ ({l8} = (0 : UInt64)) then {l8} else x.input.rsi)"),
    ("a narrow load is extended to 64 bits",
      (headTerm inputs [.load 0 (rdiPlus 32) .W8] (.load 0)).toOption ==
        some "(match x.input.heap.load (x.input.rdi.toBitVec + 32) .W8 with | .ok v => UInt64.ofBitVec (BitVec.zeroExtend 64 v) | _ => 0)"),
    -- negative cases
    ("a stack load has no term", isErr (headTerm inputs [.load 0 (.add (.reg .rsp) (.lit 8)) .W64] (.load 0))),
    ("a load at a scaled address has no term",
      isErr (headTerm inputs [.load 0 (.add (.reg .rdi) (.mul (.reg .rsi) (.lit 8))) .W64] (.load 0))),
    ("a load that the entry block does not have has no term", isErr (headTerm inputs entry (.load 2))),
    ("a register that is no input has no term", isErr (headTerm inputs entry (.add (.reg .rcx) (.load 0)))),
    ("rsp has no term", isErr (headTerm (.rsp :: inputs) entry (.reg .rsp))),
    ("a shift has no term", isErr (headTerm inputs entry (.shr (.load 0) 3))),
    ("a signed compare has no term", isErr (headTerm inputs entry (.ite (.slt (.load 0) (.load 1)) (.load 0) (.load 1)))),
    -- the pilot
    ("mapInPlace: r15 at the head is the minimum of the loads at rdi + 24 and rdi + 8", (mapR15.bind (·.toOption)) == some minText),
    -- the plan (PIL-CALL5)
    ("a loop whose bound is the minimum of two loads: its plan is generated", GenUpperPlanTests.isOkPlan minPlan),
    ("a loop whose bound is the minimum of two loads: the head value of the bound is the term of the minimum",
      minPlan.toOption.any fun p => p.heads.any fun h => h.state.any fun (r, v) =>
        r == .rsi && match v with | .term t => t == minText | _ => false),
    -- the sampler
    ("the sampler: the term of one entry load has the text of the head value of that load, in parentheses",
      match headTerm inputs entry (.load 1) with
      | .ok t => headValText (.term t) == s!"({headValText (.load "x.input.rdi.toBitVec + 24" .W64)})"
      | .error _ => false),
    ("the sampler: the term of the minimum reads both loads in a.heap",
      match headTerm inputs entry minVal with
      | .ok t => let s := headValText (.term t)
        has s "a.heap.load (a.rdi.toBitVec + 24) .W64" && has s "a.heap.load (a.rdi.toBitVec + 8) .W64" && !has s "x.input."
      | .error _ => false),
    -- the templates
    ("the templates: a bound with a term head value gives x.rax = the term over a",
      match findWith (.term minText), GenUpperPlanTests.findShape with
      | some p, some sh =>
        let ts := loopTemplates p sh
        !ts.isEmpty && ts.all fun t => has t.inv s!"x.rax = ({minText.replace "x.input." "a."})"
      | _, _ => false),
    ("the templates: a bound with an input head value keeps x.rax = a.rsi",
      match findWith (.input .rsi), GenUpperPlanTests.findShape with
      | some p, some sh => (loopTemplates p sh).all fun t => has t.inv "x.rax = a.rsi"
      | _, _ => false) ]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "maphead" then return 0
  let mut n := 0
  for (name, ok) in pureChecks do
    unless ok do
      n := n + 1
      IO.println s!"FAIL  maphead: {name}"
  return n

end MapHeadTests
