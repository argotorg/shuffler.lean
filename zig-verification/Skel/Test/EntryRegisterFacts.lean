import Skel.Test.GenL2CallBlk

/-! Entry values stored to stack words after the entry block. -/

namespace EntryRegisterFactsTests

open Skel Skel.Gen
open GenUpperRoomTests (below above lit)
open GenVarsTests (rg)
open GenUpperPlanTests (blk goto ret)

/-- Save an input after the entry block, call, and restore it from the stack.
The restored value contributes to the result. -/
def summary (r : Reg64) : Except GenError Summary :=
  GenUpperCallTests.synthWith "EntryRegisterFacts" [GenUpperCallTests.calleeF]
    [ blk "entry" 0 [.store 0 (below 8) .W64 (rg .rbx)]
        [(.rsp, .sub (rg .rsp) (lit 8))] (goto 4),
      blk "o4" 4 [.store 0 (below 8) .W64 (rg r), .store 1 (below 16) .W64 (.retAddr 9)]
        [(.rsp, .sub (rg .rsp) (lit 16))] (.exit (.call "F" 9)),
      blk "o9" 9 [.load 0 (above 0) .W64, .load 1 (above 8) .W64, .load 2 (above 16) .W64]
        [(r, .load 0), (.rbx, .load 1), (.rax, .add (rg .rax) (.load 0)),
          (.rsp, .add (rg .rsp) (lit 24))] ret ]

def hasEntryFact (r : Reg64) : Bool :=
  match summary r with
  | .error _ => false
  | .ok s =>
    match (flows s).lookup 4 with
    | none => false
    | some flow => (atItems s.vars true false flow).contains (.entryEq r)

def noEntryFactAfterCall (r : Reg64) : Bool :=
  match summary r with
  | .error _ => false
  | .ok s =>
    match (flows s).lookup 9 with
    | none => false
    | some flow =>
      !(atItems s.vars true false flow).contains (.entryEq r) &&
      !(atItems s.vars true false flow).contains (.regS r)

-- Each dual register fact needs an equality before a call, including ABI
-- caller-saved registers. A call removes its old register fact.
#guard [Reg64.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11].all hasEntryFact
#guard [Reg64.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11].all noEntryFactAfterCall

-- Unknown entry values do not become invariant facts.
#guard !(atItems { inputs := [.rdx], state := [.rdx], mem := true } true false
  { regs := [(.rdx, ⟨false, true⟩)], slots := [], called := false }).contains (.entryEq .rdx)

def check (r : Reg64) : IO Unit := do
  let .ok text := GenL2CallBlkTests.toyFile (summary r) |
    throw (IO.userError s!"could not generate {repr r}")
  let dir ← Skel.tempDir "entry-register-facts"
  let file := dir / "check.lean"
  IO.FS.writeFile file text
  let (outcome, _) ← Skel.Io.checkFile .bvDecide file "L2CB.decompiles_l2" 120000
  unless GenL2CallBlkTests.accepted outcome do
    let reason := match outcome with
      | .failed errors => errors.headD "no diagnostic"
      | other => reprStr other
    throw (IO.userError s!"generated {repr r} proof rejected: {reason}; {file}")

#eval check .rdx
#eval check .rsi
#eval check .r8


/-- Only one path changes `rax`. Its value is not used before the call.
The join needs separate register equations, while `r` keeps both facts. -/
def summaryConj (r : Reg64) : Except GenError Summary :=
  GenUpperCallTests.synthWith "EntryRegisterFactsConj" [GenUpperCallTests.calleeF]
    [ blk "entry" 0 [.store 0 (below 8) .W64 (rg .rbx)]
        [(.rsp, .sub (rg .rsp) (lit 8))]
        (.branch (.eq (rg .rdi) (lit 0)) (.goto 2) (.goto 4)),
      blk "o2" 2 [] [(.rax, lit 0)] (goto 4),
      blk "o4" 4 [.store 0 (below 8) .W64 (rg r), .store 1 (below 16) .W64 (.retAddr 9)]
        [(.rsp, .sub (rg .rsp) (lit 16))] (.exit (.call "F" 9)),
      blk "o9" 9 [.load 0 (above 0) .W64, .load 1 (above 8) .W64, .load 2 (above 16) .W64]
        [(r, .load 0), (.rbx, .load 1), (.rax, .add (rg .rax) (.load 0)),
          (.rsp, .add (rg .rsp) (lit 24))] ret ]

def conjHasBoth (r : Reg64) : Bool :=
  match summaryConj r with
  | .error _ => false
  | .ok s =>
    match (flows s).lookup 4 with
    | none => false
    | some flow =>
      atConj flow && (atItems s.vars true false flow).contains (.regX r) &&
        (atItems s.vars true false flow).contains (.regS r) &&
        !(atItems s.vars true false flow).contains (.entryEq r)

#guard [Reg64.rdx, .rsi, .r8].all conjHasBoth

-- No equality is emitted when either fact is absent.
#guard !(atItems { inputs := [.rdx], state := [.rdx], mem := true } true false
  { regs := [(.rdx, ⟨true, false⟩)], slots := [], called := false }).contains (.entryEq .rdx)
#guard !(atItems { inputs := [.rdx], state := [.rdx], mem := true } true false
  { regs := [(.rdx, ⟨false, false⟩)], slots := [], called := false }).contains (.entryEq .rdx)

def checkConj (r : Reg64) : IO Unit := do
  let .ok text := GenL2CallBlkTests.toyFile (summaryConj r) |
    throw (IO.userError s!"could not generate conjunction fixture {repr r}")
  let dir ← Skel.tempDir "entry-register-conj"
  let file := dir / "check.lean"
  IO.FS.writeFile file text
  let (outcome, _) ← Skel.Io.checkFile .bvDecide file "L2CB.decompiles_l2" 120000
  unless GenL2CallBlkTests.accepted outcome do
    let reason := match outcome with
      | .failed errors => errors.headD "no diagnostic"
      | other => reprStr other
    throw (IO.userError s!"generated conjunction {repr r} proof rejected: {reason}; {file}")

#eval checkConj .rdx
#eval checkConj .rsi
#eval checkConj .r8

end EntryRegisterFactsTests
