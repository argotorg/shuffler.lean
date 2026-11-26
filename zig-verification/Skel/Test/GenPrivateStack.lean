import Skel.Gen.GenerateUpper
import Lift.Sem.Bridge
import Lift.Sem.StackPush
import Skel.Test.GenUpperModel

/-! Tests of production L2+ generation for private bytes, stack arguments, and carried flags. -/

namespace GenPrivateStackTests

open Skel.Gen GenUpperPlanTests

def summary (fn : String) (bs : List Block) : Except GenError Summary := do
  let ff ← frameFacts [] bs
  pure ⟨fn, bs, modelVars bs [] ff, ff, some false⟩

def spill (store : Bool) : Except GenError Summary := summary "spill"
  [blk "entry" 0 (if store then [.store 0 (.sub (.reg .rsp) (lit 8)) .W64 (lit 37)] else [])
    [(.rsp, .sub (.reg .rsp) (lit 8))] (goto 8),
   blk "o8" 8 [.load 0 (.reg .rsp) .W64]
    [(.rax, .load 0), (.rsp, .add (.reg .rsp) (lit 16))] ret]

/-- A later store replaces a word that entry saved. The saved entry register must not be forwarded. -/
def overwrite : Except GenError Summary := summary "overwrite"
  [blk "entry" 0 [.store 0 (.sub (.reg .rsp) (lit 8)) .W64 (.reg .rdi)]
    [(.rsp, .sub (.reg .rsp) (lit 8))] (goto 8),
   blk "o8" 8 [.store 0 (.reg .rsp) .W64 (lit 37)] [] (goto 16),
   blk "o16" 16 [.load 0 (.reg .rsp) .W64]
    [(.rax, .load 0), (.rsp, .add (.reg .rsp) (lit 16))] ret]

/-- A narrow store changes two bytes of a word saved in an earlier block. -/
def overlap : Except GenError Summary := summary "overlap"
  [blk "entry" 0 [.store 0 (.sub (.reg .rsp) (lit 8)) .W64 (lit 0x8877665544332211)]
    [(.rsp, .sub (.reg .rsp) (lit 8))] (goto 8),
   blk "o8" 8 [.store 0 (.add (.reg .rsp) (lit 2)) .W16 (lit 0xbbaa)] [] (goto 16),
   blk "o16" 16 [.load 0 (.reg .rsp) .W64]
    [(.rax, .load 0), (.rsp, .add (.reg .rsp) (lit 16))] ret]

/-- A byte store does not initialize the remaining bytes of a later word load. -/
def partialWord : Except GenError Summary := summary "partialWord"
  [blk "entry" 0 [.store 0 (.sub (.reg .rsp) (lit 8)) .W8 (lit 37)]
    [(.rsp, .sub (.reg .rsp) (lit 8))] (goto 8),
   blk "o8" 8 [.load 0 (.reg .rsp) .W64]
    [(.rax, .load 0), (.rsp, .add (.reg .rsp) (lit 16))] ret]

/-- An unused alignment word does not change a saved entry word. -/
def alignmentWord : Except GenError Summary := summary "alignmentWord"
  [blk "entry" 0 [.store 0 (.sub (.reg .rsp) (lit 8)) .W64 (.reg .rdi)]
    [(.rsp, .sub (.reg .rsp) (lit 8))] (goto 8),
   blk "o8" 8 [.store 0 (.sub (.reg .rsp) (lit 8)) .W64 (lit 99)] [] (goto 16),
   blk "o16" 16 [.load 0 (.reg .rsp) .W64]
    [(.rax, .load 0), (.rsp, .add (.reg .rsp) (lit 16))] ret]

/-- A model probe with overlapping words. Frame generation rejects the unaligned access because
`StackRoom` gives permissions only for aligned words. This probe tests byte selection and execution. -/
def wordOverlapBlocks : List Block :=
  [blk "entry" 0
    [.store 0 (.sub (.reg .rsp) (lit 16)) .W64 (lit 0x8877665544332211),
     .store 1 (.sub (.reg .rsp) (lit 12)) .W64 (lit 0xffeeddccbbaa9988),
     .load 0 (.sub (.reg .rsp) (lit 16)) .W64]
    [(.rax, .load 0), (.rsp, .add (.reg .rsp) (lit 8))] ret]

def wordOverlap : Except GenError Summary :=
  let ff : FrameFacts := ⟨[(0, 0)], 16⟩
  .ok ⟨"wordOverlap", wordOverlapBlocks, modelVars wordOverlapBlocks [] ff, ff, some false⟩

/-- An entry save after a load cannot initialize that load. -/
def readBeforeSave : Except GenError Summary := summary "readBeforeSave"
  [blk "entry" 0 [.load 0 (.sub (.reg .rsp) (lit 8)) .W64,
     .store 0 (.sub (.reg .rsp) (lit 8)) .W64 (.reg .rdi)]
    [(.rax, .load 0), (.rsp, .add (.reg .rsp) (lit 8))] ret]

/-- The final entry store replaces the saved input before the next block. -/
def entryOverwrite : Except GenError Summary := summary "entryOverwrite"
  [blk "entry" 0
    [.store 0 (.sub (.reg .rsp) (lit 8)) .W64 (.reg .rdi),
     .store 1 (.sub (.reg .rsp) (lit 8)) .W64 (lit 37)]
    [(.rsp, .sub (.reg .rsp) (lit 8))] (goto 8),
   blk "o8" 8 [.load 0 (.reg .rsp) .W64]
    [(.rax, .load 0), (.rsp, .add (.reg .rsp) (lit 16))] ret]

/-- Re-entry saves the current register, which can differ from its first input. -/
def entryLoop : Except GenError Summary := summary "entryLoop"
  [blk "entry" 0 [.store 0 (.sub (.reg .rsp) (lit 8)) .W64 (.reg .rdi)] [] (goto 8),
   blk "o8" 8 [.load 0 (.sub (.reg .rsp) (lit 8)) .W64]
    [(.rax, .load 0), (.rdi, .add (.reg .rdi) (lit 1))]
    (.branch (.ult (.reg .rdi) (lit 3)) (.goto 0) (.goto 16)),
   blk "o16" 16 [] [(.rsp, .add (.reg .rsp) (lit 8))] ret]

def stackArgSummary : Except GenError Summary := summary "stackArg"
  [blk "entry" 0 [.load 0 (.add (.reg .rsp) (lit 8)) .W64]
    [(.rax, .load 0), (.rsp, .add (.reg .rsp) (lit 8))] ret]

def flagSummary : Except GenError Summary := summary "flags"
  [{ blk "entry" 0 [] [] (goto 8) with flags := [(.zf, .eq (lit 1) (lit 1))] },
   blk "o8" 8 [] [] (.branch (.flag .zf) (.goto 16) (.goto 24)),
   blk "o16" 16 [] [(.rax, lit 37), (.rsp, .add (.reg .rsp) (lit 8))] ret,
   blk "o24" 24 [] [(.rax, lit 0), (.rsp, .add (.reg .rsp) (lit 8))] ret]

def generated (s : Summary) : Except GenError String := do
  let p := calleePlan s
  pure ((← GenModelTests.textOf GenModelTests.sumTarget [] s) ++ "\n" ++
    (← upperModelText GenModelTests.sumTarget s p) ++ "\n" ++ upperSimText p)

/-- The synthetic overlap probe checks upper execution only. This frame selects the input type
with `sp`; the probe keeps the production input, label, state, initialization and block declarations.
No representation, postcondition or proof is checked here. The separate negative check keeps the
production frame refusal for the unaligned word. -/
def upperOnlyGenerated (s : Summary) : Except GenError String := do
  let typesFrame : FrameText :=
    { repConjs := fun _ => [], frameDef := none, frameIntro := [], atConj := fun _ => none,
      rspAt := fun _ => none, post := "True", calleePost := "True", guardDefs := some "",
      storeGuard := fun _ _ _ => none, memSteps := fun _ => none }
  let lower := modelText GenModelTests.sumTarget s typesFrame
  let types ← ["In2", "Lbl", "St"].mapM fun name =>
    match declText lower name with
    | some text => pure text
    | none => throw (.shape 0 s!"the synthetic upper probe has no {name} declaration")
  let upper ← upperModelText GenModelTests.sumTarget s (calleePlan s)
  let execution ← ["In2p", "StP", "initP", "blocksP"].mapM fun name =>
    match declText upper name with
    | some text => pure text
    | none => throw (.shape 0 s!"the synthetic upper probe has no {name} declaration")
  pure ("\n\n".intercalate (types ++ execution))

def resultCheck (input : String) (expected : Nat := 37) : String :=
  s!"\nexample : (match blocksP.run (fun f => Empty.elim f) 8 .entry (initP ({input} : In2p)) with\n" ++
    s!"  | .ok r => r.toNat | _ => 0) = {expected} := by decide\n"

def missingCheck (input : String) : String :=
  s!"\nexample : (match blocksP.run (fun f => Empty.elim f) 8 .entry (initP ({input} : In2p)) with\n" ++
    "  | .stuck _ => true | _ => false) = true := by decide\n"

def checks : List (String × Bool) :=
  [("a cross-block spill carries initialized bytes", (spill true).toOption.any needsPrivateStack),
   ("a missing private word still uses the byte model", (spill false).toOption.any needsPrivateStack),
   ("an overwritten entry save uses the byte model", overwrite.toOption.any needsPrivateStack),
   ("an unused alignment word keeps entry-save forwarding", alignmentWord.toOption.any fun s => !needsPrivateStack s),
   ("overlapping full words use byte state", wordOverlap.toOption.any needsPrivateStack),
   ("negative: frame generation names the unaligned word boundary",
      match frameFacts [] wordOverlapBlocks with
      | .error (.frame 0 why) => (why.splitOn "not a multiple of 8").length > 1
      | _ => false),
   ("a later entry save does not initialize an earlier load", readBeforeSave.toOption.any needsPrivateStack),
   ("the final entry store replaces a saved input", entryOverwrite.toOption.any needsPrivateStack),
   ("entry re-entry saves the current register", entryLoop.toOption.any needsPrivateStack),
   ("stack argument count is retained", stackArgSummary.toOption.any fun s => (calleePlan s).stackArgs == 1),
   ("carried flags enter the plan", flagSummary.toOption.any fun s => (calleePlan s).flags == [.zf])]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genprivatestack" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL genprivatestack: {name}"
  for (name, source, assertion) in
      [("spill", spill true >>= generated, resultCheck "{ heap := [], sp := 4096 }"),
       ("missing byte", spill false >>= generated, missingCheck "{ heap := [], sp := 4096 }"),
       ("overwrite", overwrite >>= generated, resultCheck "{ heap := [], rdi := 1, sp := 4096 }"),
       ("overlapping widths", overlap >>= generated, resultCheck "{ heap := [], sp := 4096 }" 0x88776655bbaa2211),
       ("partly initialized word", partialWord >>= generated, missingCheck "{ heap := [], sp := 4096 }"),
       ("unused alignment word", alignmentWord >>= generated, resultCheck "{ heap := [], rdi := 37, sp := 4096 }"),
       ("overlapping full words", wordOverlap >>= upperOnlyGenerated,
         resultCheck "{ heap := [], sp := 4096 }" 0xbbaa998844332211),
       ("load before entry save", readBeforeSave >>= generated, missingCheck "{ heap := [], rdi := 1, sp := 4096 }"),
       ("repeated entry store", entryOverwrite >>= generated, resultCheck "{ heap := [], rdi := 1, sp := 4096 }"),
       ("entry back edge", entryLoop >>= generated, resultCheck "{ heap := [], rdi := 1, sp := 4096 }" 3),
       ("stack argument", stackArgSummary >>= generated, resultCheck "{ heap := [], stk0 := 37 }"),
       ("carried flag", flagSummary >>= generated, resultCheck "{ heap := [] }")] do
    match source with
    | .error e =>
      failed := failed + 1
      IO.println s!"FAIL genprivatestack: {name}: {repr e}"
    | .ok text =>
      let imports := (GenModelTests.sumTarget.imports ++ ["Lift.Sem.Bridge", "Lift.Sem.StackPush"]).eraseDups
      let body := GenUpperModelTests.checkFileWith GenUpperModelTests.sumOpens imports (text ++ assertion)
      let (ok, msg) ← GenFrameTests.leanCheck "genprivatestack" body "t"
      unless ok do
        failed := failed + 1
        IO.println s!"FAIL genprivatestack: {name}\n{msg}"
  return failed

end GenPrivateStackTests
