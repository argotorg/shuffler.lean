import Skel.Test.GenUpperCall
import Skel.Test.LiveInputs

/-! The tests of the `decompiles_l2` cases of the blocks after a call and of an entry block that pushes and jumps (suite
`l2callblk`, task L2-CALLBLK): `lake exe skel-test --only l2callblk`.

The callee is `F` of `GenUpperCall.lean` (room 0, memory: a store through `rdi`). The memory form with a stack room
(`stackProof`) has the case of each block:

- `After`: the entry pushes `rbx`, sets `rbx := rdi` and calls `F`; the block after the call (`o5`) adds 1 to `rax` and jumps
  to `o9`, which loads the word at `rbx`, pops `rbx` and returns.
- `Loop3`: the entry pushes `r15`, `r14` and `rbx` (`rsp` 24 bytes lower) and jumps to the loop head `o4`; `o8` calls `F`;
  the block after the call (`o13`) adds 1 to `r14` and jumps back to `o4`; `o20` pops the three words and returns. The head
  is in the conjunction form of `At` (a call comes before it on a path).
- Negative: `Bad` is `After` with `rax := rcx` in `o5`: after the call `rcx` has no fact (a caller-saved register that the
  callee can change), so the case of `o5` is the named `fail`.
- The pilot `mapInPlace` (the call of `map` in its loop): no `fail` case.

The Lean checks: the model of `F`, the model of the caller, and `decompiles_l2` with the generated text, the block rows and the
`Decompiles` of `F` as hypotheses, are accepted with the standard axioms; for `mapInPlace` the same with the model of `map`.
Mutation: the `Loop3` text with the `rsp` fact `hrsp` of an arrival replaced by `rfl` is rejected. The check files have the
imports of `GenUpperCall.lean` and `GenCallMem.lean` only, so each name of the text must resolve with them; a pure check
says that the texts name no lemma of `Lift.Spike.Sites.Stack`. -/

namespace GenL2CallBlkTests

open Skel Skel.Gen
open GenUpperRoomTests (below above lit)
open GenVarsTests (rg)
open GenUpperPlanTests (blk goto ret)

def target : Target := GenUpperCallTests.target

def calleeTarget : Target := GenUpperCallTests.calleeTarget

/-- `After`: a call, then a goto from the block after the call. -/
def summaryAfter (o5 : List (Reg64 × Val) := [(.rax, .add (rg .rax) (lit 1))]) : Except GenError Summary :=
  GenUpperCallTests.synthWith "After" [GenUpperCallTests.calleeF]
    [ blk "entry" 0 [.store 0 (below 8) .W64 (rg .rbx), .store 1 (below 16) .W64 (.retAddr 5)]
        [(.rbx, rg .rdi), (.rsp, .sub (rg .rsp) (lit 16))] (.exit (.call "F" 5)),
      blk "o5" 5 [] o5 (goto 9),
      blk "o9" 9 [.load 0 (rg .rbx) .W64, .load 1 (above 0) .W64, .load 2 (above 8) .W64]
        [(.rax, .add (rg .rax) (.load 0)), (.rbx, .load 1), (.rsp, .add (rg .rsp) (lit 16))] ret ]

/-- Negative: `After` with `rax := rcx` after the call. -/
def summaryBad : Except GenError Summary := summaryAfter [(.rax, rg .rcx)]

/-- `Loop3`: three pushes in the entry, then a loop whose body calls `F`. -/
def summaryLoop3 : Except GenError Summary :=
  GenUpperCallTests.synthWith "Loop3" [GenUpperCallTests.calleeF]
    [ blk "entry" 0 [.store 0 (below 8) .W64 (rg .r15), .store 1 (below 16) .W64 (rg .r14), .store 2 (below 24) .W64 (rg .rbx)]
        [(.rbx, rg .rdi), (.r14, lit 0), (.r15, rg .rsi), (.rsp, .sub (rg .rsp) (lit 24))] (goto 4),
      blk "o4" 4 [] [] (.branch (.eq (rg .r14) (rg .r15)) (.goto 20) (.goto 8)),
      blk "o8" 8 [.store 0 (below 8) .W64 (.retAddr 13)] [(.rdi, rg .rbx), (.rsp, .sub (rg .rsp) (lit 8))] (.exit (.call "F" 13)),
      blk "o13" 13 [] [(.r14, .add (rg .r14) (lit 1))] (goto 4),
      blk "o20" 20 [.load 0 (above 0) .W64, .load 1 (above 8) .W64, .load 2 (above 16) .W64, .load 3 (above 24) .W64]
        [(.rax, lit 0), (.rbx, .load 0), (.r14, .load 1), (.r15, .load 2), (.rsp, .add (rg .rsp) (lit 32))] ret ]

/-- The model text and the `decompiles_l2` text of a summary. -/
def textsOf (t : Target) (s : Summary) : Except GenError (String × String) := do
  let memCall := s.blocks.any fun b => match b.term with
    | .exit (.call g _) => (t.callees.find? (·.name == g)).any (·.mem)
    | _ => false
  let fr ← frameText .storeChain (t.callees.map fun c => (c.name, c.room)) s memCall
  pure (modelText t s fr, decompilesProof t s fr)

def has (s part : String) : Bool := (s.splitOn part).length > 1

def detOf (s : Except GenError Summary) : String :=
  match (do textsOf target (← s)) with
  | .ok (_, d) => d
  | .error _ => "no text"

/-- The imports of the check files: those of the toys of `GenUpperCall.lean` and of the pilot of `GenCallMem.lean`. The
proof text must resolve each name with these alone: it states the facts of `Lift.Spike.Sites.Stack` itself (that module
imports `Lift.Spike.L1`, whose names clash with those of other units). -/
def imports : List String :=
  (GenUpperCallTests.imports ++ GenCallMemTests.imports).eraseDups

def replaceAll (s old new : String) : String := new.intercalate (s.splitOn old)

/-- The check file of a toy: `F` (model) in its namespace, the caller's model, and its `decompiles_l2` with the block rows
and `F.decompiles_l2` as hypotheses. `mutate` changes the proof text. -/
def toyFile (s : Except GenError Summary) (mutate : String → String := id) : Except GenError String := do
  let sF ← GenUpperCallTests.summaryF
  let (mF, _) ← textsOf calleeTarget sF
  let s ← s
  let (m, d) ← textsOf target s
  let rows ← rows target s
  let binders := rows.filterMap fun o => match o.origin with
    | .block l => some s!"({l} : {o.statement})"
    | _ => none
  let d := mutate (replaceAll d "F.decompiles_l2" "hcallee")
  pure ("\n".intercalate (imports.map (s!"import " ++ ·)) ++ s!"\n\nopen {GenUpperModelTests.sumOpens}\n\n" ++
    "namespace L2CB\n\nnamespace F\n\n" ++ mF ++ "\nend F\n\n" ++ m ++
    s!"\ntheorem decompiles_l2 {" ".intercalate binders} (hcallee : Decompiles {target.step} F.l2) :\n    Decompiles {target.step} l2 := by\n{d}\n\nend L2CB\n\n#print axioms L2CB.decompiles_l2\n")

/-- The mutation: the first `rsp` fact `hrsp` of an arrival replaced by `rfl`. -/
def noRsp (d : String) : String :=
  let wrapped := ", (by first | (sim_state => exact hrsp) | exact hrsp), "
  let pattern := if has d wrapped then wrapped else ", hrsp, "
  match d.splitOn pattern with
  | a :: b :: rest => a ++ ", rfl, " ++ pattern.intercalate (b :: rest)
  | _ => d


namespace LiveInput

def synth (name : String) (bs : List Block) (cs : List Callee) : Except GenError (Summary × FrameText) := do
  let ff ← frameFacts (cs.map fun c => (c.name, c.room)) bs
  let s : Summary := ⟨name, bs, modelVars bs cs ff, ff, some (heapWritesOf bs cs)⟩
  return (s, ← frameText .storeChain (cs.map fun c => (c.name, c.room)) s (cs.any (·.mem)))

/-- Two calls to a callee with a partial register write. A dead write must not
add a callee input. A live write must retain that input and refuse the second call. -/
def file (live : Bool := false) : Except GenError String := do
  let (sf, ff) ← synth "F" [
    blk "entry" 0 [] [(.rdx, .replaceLow .b8 (rg .rdx) (lit 1))] (goto 4),
    blk "o4" 4 [.load 0 (above 0) .W64]
      [(.rax, if live then rg .rdx else lit 0), (.rsp, .add (rg .rsp) (lit 8))] ret] []
  let c : Callee := ⟨"F", "F", sf.vars.inputs, calleeTarget.entryPC, sf.frame.room,
    sf.vars.mem, 0, some sf.heapWrites⟩
  let t := { calleeTarget with callees := [c] }
  let (s, fr) ← synth "Caller" [
    blk "entry" 0 [.store 0 (below 8) .W64 (rg .rbx), .store 1 (below 16) .W64 (.retAddr 5)]
      [(.rsp, .sub (rg .rsp) (lit 16))] (.exit (.call "F" 5)),
    blk "o5" 5 [.store 0 (below 8) .W64 (.retAddr 9)]
      [(.rsp, .sub (rg .rsp) (lit 8))] (.exit (.call "F" 9)),
    blk "o9" 9 [.load 0 (above 0) .W64, .load 1 (above 8) .W64]
      [(.rbx, .load 0), (.rsp, .add (rg .rsp) (lit 16))] ret] [c]
  let obs ← rows t s
  let binders := obs.filterMap fun o => match o.origin with
    | .block label => some s!"({label} : {o.statement})"
    | _ => none
  let proof := replaceAll (decompilesProof t s fr) "F.decompiles_l2" "hcallee"
  return "\n".intercalate (imports.map ("import " ++ ·)) ++
    s!"\n\nnamespace L2CB\nopen {GenUpperModelTests.sumOpens}\n\nnamespace F\n" ++
    modelText calleeTarget sf ff ++ "\nend F\n\n" ++ modelText t s fr ++
    "\ntheorem decompiles_l2 " ++ " ".intercalate binders ++
    s!" (hcallee : Decompiles {t.step} F.l2) : Decompiles {t.step} l2 := by\n" ++ proof ++
    "\nend L2CB\n#print axioms L2CB.decompiles_l2\n"

end LiveInput

def pureChecks : List (String × Bool) :=
  let failFree (d : String) := !has d "fail" && d != "no text"
  [ ("After and Loop3: record field proofs use sim_state before their direct proof",
      [detOf summaryAfter, detOf summaryLoop3].all (has · "sim_state => exact")),
    ("After: the case of each block (the goto after the call) has a text, no fail", failFree (detOf summaryAfter)),
    ("Loop3: the case of each block (three pushes and the jump to the loop head, the block after the call) has a text, no fail",
      failFree (detOf summaryLoop3)),
    ("Bad: the block after the call that reads rcx is the named fail",
      has (detOf summaryBad) "o5 =>\n    fail \"decompiles_l2: the case of this block is not generated: a read of a register with no fact after a call"),
    ("Bad: the return that depends on the unknown rcx value is also refused",
      has (detOf summaryBad) "o9 =>\n    fail \"decompiles_l2: the case of this block is not generated: a read of a register with no fact after a call" &&
        ((detOf summaryBad).splitOn "fail \"").length == 3),
    ("mapInPlace: no fail case", match GenCallMemTests.genMapInPlace with
      | .ok g => !has (GenCallMemTests.detOf g) "fail"
      | .error _ => false),
    ("mutation: the Loop3 text without hrsp differs", noRsp (detOf summaryLoop3) != detOf summaryLoop3),
    ("the texts of After, Loop3 and mapInPlace name no lemma of Lift.Spike.Sites.Stack (not in the imports of a check file)",
      [detOf summaryAfter, detOf summaryLoop3, match GenCallMemTests.genMapInPlace with
        | .ok g => GenCallMemTests.detOf g
        | .error _ => "Sites.Stack."].all (!has · "Sites.Stack.")) ] ++ Skel.Test.LiveInputs.checks ++
  [("a used partial register input is still refused after a call", match LiveInput.file true with
    | .ok text => has text "a read of a register with no fact after a call"
    | .error _ => false)]

def standard : List String := ["Classical.choice", "Quot.sound", "propext"]

def run1 (name text thm : String) : IO Outcome := do
  let dir ← Skel.tempDir s!"l2callblk-{name}"
  IO.FS.writeFile (dir / "check.lean") text
  pure (← Skel.Io.checkFile .bvDecide (dir / "check.lean") thm 300000).1

def accepted (o : Outcome) : Bool := match o with
  | .accepted axs => axs.all standard.contains
  | _ => false

def rejected (o : Outcome) : Bool := match o with
  | .failed _ => true
  | _ => false

/-- The check file of `mapInPlace`: the model of `map`, the model of `mapInPlace`, `decompiles_l2` with the block rows and the
`Decompiles` of `map` as hypotheses. -/
def mipFile (map g : Generated) : String :=
  let rows := g.obligations.filterMap fun o =>
    match o.origin with
    | .block l => some s!"({l} : {o.statement})"
    | _ => none
  let det := replaceAll (GenCallMemTests.detOf g) "mappingMap.decompiles_l2" "hcallee"
  "\n".intercalate (imports.map (s!"import " ++ ·)) ++
    "\n\nnamespace CallMem\nopen Lift.P2.Total Lift.Sem Lift.Spike Lift.Level3\n\nnamespace mappingMap\n\n" ++ map.modelText ++
    "\nend mappingMap\n\n" ++ g.modelText ++
    "\n" ++ detTheorem "decompiles_l2" (" ".intercalate rows ++ " (hcallee : Decompiles Lift.Level3.L1.step mappingMap.l2)")
      "Decompiles Lift.Level3.L1.step l2" det ++ "\n\nend CallMem\n\n#print axioms CallMem.decompiles_l2\n"

def ioChecks : IO (List (String × Bool × String)) := do
  let toy (label name : String) (f : Except GenError String) (want : Outcome → Bool) : IO (String × Bool × String) := do
    match f with
    | .error e => pure (label, false, s!"{repr e}")
    | .ok t => let o ← run1 name t "L2CB.decompiles_l2"; pure (label, want o, s!"{repr o}")
  let a ← toy "After: Lean accepts decompiles_l2 with the standard axioms" "after" (toyFile summaryAfter) accepted
  let l ← toy "Loop3: Lean accepts decompiles_l2 with the standard axioms" "loop3" (toyFile summaryLoop3) accepted
  let m ← toy "mutation: Loop3 with rfl for the rsp fact hrsp is rejected" "loop3-mut" (toyFile summaryLoop3 noRsp) rejected
  let mip ← match GenCallMemTests.genMap, GenCallMemTests.genMapInPlace with
    | .ok map, .ok g =>
      let o ← run1 "mip" (mipFile map g) "CallMem.decompiles_l2"
      pure ("mapInPlace: Lean accepts decompiles_l2 (block rows and the Decompiles of map as hypotheses) with the standard axioms",
        accepted o, s!"{repr o}")
    | _, _ => pure ("generate map and mapInPlace", false, "")
  let dead ← toy "Two calls: the dead partial-register write adds no input and the core checks"
    "live-input" (LiveInput.file false) accepted
  pure [a, l, m, mip, dead]

/-- Gives the number of failed checks. The suite runs when `only` is none or `l2callblk`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "l2callblk" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  l2callblk: {name}"
  for (name, ok, msg) in ← ioChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  l2callblk: {name}\n{msg}"
  return failed

end GenL2CallBlkTests
