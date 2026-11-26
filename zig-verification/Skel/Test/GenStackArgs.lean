import Skel.Gen.GenerateUpper
import Skel.Test.GenUpperModel
import Lift.Sem.Bridge

/-! Stack argument reads after heap writes. The tests execute the production generated L2+ model.
Each byte comes from the current heap when an object covers it, and otherwise from the entry argument.
The cases include whole words, partial overlap, separate addresses, wrap, private bytes and a call. -/

namespace GenStackArgsTests

open Skel Skel.Gen
open GenUpperPlanTests (blk lit)

def below (n : Nat) : Val := .sub (.reg .rsp) (lit n)

def above (n : Nat) : Val := .add (.reg .rsp) (lit n)

def summary (name : String) (cs : List Callee) (bs : List Block) : Except GenError Summary := do
  let ff ← frameFacts (cs.map fun c => (c.name, c.room)) bs
  pure ⟨name, bs, modelVars bs cs ff, ff, some (heapWritesOf bs cs)⟩

def aliasSummary (w : Width) (value : Nat) (privateBytes : Bool := false) : Except GenError Summary :=
  let writes := [.store 0 (.reg .rdi) w (lit value)]
  let reads := [.load 0 (above 8) .W64, .load 1 (.reg .rsp) .W64]
  let finish := [(.rax, .load 0), (.rsp, above 8)]
  summary "alias" [] (if privateBytes then
    [blk "entry" 0 (writes ++ [.store 1 (below 8) .W8 (lit 37)]) [] (.exit (.goto 8)),
     blk "o8" 8 ([.load 2 (below 8) .W8] ++ reads) finish (.exit .ret)]
    else [blk "entry" 0 (writes ++ reads) finish (.exit .ret)])

def generated (t : Target) (s : Summary) : Except GenError String := do
  let memCall := s.blocks.any fun b => (exitsOfTerm b.term).any fun
    | .call f _ => (t.callees.find? (·.name == f)).any (·.mem)
    | _ => false
  let fr ← frameText .storeChain (t.callees.map fun c => (c.name, c.room)) s memCall
  pure (modelText t s fr ++ "\n" ++ (← upperModelText t s (calleePlan s)) ++ "\n" ++ upperSimText (calleePlan s))

def aliasCheck (addr old sp : Nat) (heap : String) (expected : Nat) : String :=
  "\ndef pol : CpuPolicy := ⟨fun _ => true⟩\n" ++
  s!"def input : In2p := \{ policy := pol, heap := {heap}, rdi := {addr}, stk0 := {old}, sp := {sp} }\n" ++
  "example : (match blocksP.run (fun f => Empty.elim f) 8 .entry (initP input) with\n" ++
  s!"  | .ok r => r.1.toNat | _ => 0) = {expected} := by decide\n"

def callFile (conditional : Bool := false) : Except GenError String := do
  let f ← aliasSummary .W64 23
  let cl : Callee := ⟨"F", "F", [.rdi], "toySumPC", 0, true, 1, some true⟩
  let t := { GenModelTests.sumTarget with callees := [cl] }
  let term := if conditional then .branch (.eq (.reg .rsi) (lit 0)) (.call "F" 8) (.call "F" 16)
    else .exit (.call "F" 8)
  let g ← summary "caller" [cl]
    ([blk "entry" 0 [.store 0 (below 16) .W64 (lit 23), .store 1 (below 24) .W64 (.retAddr 8)]
       [(.rsp, below 24)] term,
      blk "o8" 8 [.load 0 (above 16) .W64] [(.rsp, above 24)] (.exit .ret)] ++
      if conditional then [blk "o16" 16 [.load 0 (above 16) .W64] [(.rsp, above 24)] (.exit .ret)] else [])
  let fText ← generated GenModelTests.sumTarget f
  let gText ← generated t g
  let branchInput := if conditional then ", rsi := 0" else ""
  let execution (input : String) :=
    s!"example : (match blocksP.run (fun _ a => .ok (1337, a.heap)) 8 .entry (initP ({input})) with\n" ++
    "  | .ok r => r.1.toNat | _ => 0) = 1337 := by decide\n"
  pure ("namespace F\n" ++ fText ++ "\nend F\n" ++ gText ++
    s!"\ndef input : In2p := \{ policy := ⟨fun _ => true⟩, heap := [], rdi := 8192, sp := 4096{branchInput} }\n" ++
    "example : (match blocksP.step .entry (initP input) with\n" ++
    "  | .ok (.call _ a _) => a.sp = 4072 ∧ a.stk0 = 23\n" ++
    "  | _ => False) := by\n  dsimp [blocksP, initP, input]\n  decide\n" ++ execution "input" ++
    if conditional then execution "{ input with rsi := 1 }" else "")

def cases : List (String × Except GenError String) :=
  let build (w : Width) (v : Nat) (privateBytes : Bool) (check : String) : Except GenError String := do
    pure ((← generated GenModelTests.sumTarget (← aliasSummary w v privateBytes)) ++ check)
  [("full alias", build .W64 23 false (aliasCheck 4104 3 4096 "[Obj.words 4104 true .W64 [3]]" 23)),
   ("disjoint", build .W64 23 false (aliasCheck 8192 3 4096 "[Obj.words 8192 true .W64 [7]]" 3)),
   ("adjacent", build .W64 23 false (aliasCheck 4112 3 4096 "[Obj.words 4112 true .W64 [7]]" 3)),
   ("partial middle", build .W16 0xbbaa false
     (aliasCheck 4107 0x1122334455667788 4096 "[Obj.words 4107 true .W16 [0x4455]]" 0x112233bbaa667788)),
   ("partial last byte", build .W8 0xaa false
     (aliasCheck 4111 0x1122334455667788 4096 "[Obj.words 4111 true .W8 [0x11]]" 0xaa22334455667788)),
   ("private byte path", build .W64 23 true (aliasCheck 4104 3 4096 "[Obj.words 4104 true .W64 [3]]" 23)),
   ("argument address wraps", build .W64 23 false
     (aliasCheck 0 3 0xfffffffffffffff8 "[Obj.words 0 true .W64 [3]]" 23)),
   ("argument bytes wrap", build .W8 0xaa false
     (aliasCheck 0 0x1122334455667788 0xfffffffffffffff4 "[Obj.words 0 true .W8 [0x44]]" 0x112233aa55667788)),
   ("callee stack pointer and returned value", callFile false),
   ("conditional call returned value", callFile true)]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genstackargs" then return 0
  let mut failed := 0
  for (name, source) in cases do
    match source with
    | .error e =>
      failed := failed + 1
      IO.println s!"FAIL genstackargs: {name}: {repr e}"
    | .ok text =>
      let imports := (GenModelTests.sumTarget.imports ++ ["Lift.Sem.Bridge", "Lift.Sem.StackPush", "Lift.Sem.CallArm"]).eraseDups
      let body := GenUpperModelTests.checkFileWith GenUpperModelTests.sumOpens imports text
      let (ok, msg) ← GenFrameTests.leanCheck "genstackargs" body "t"
      unless ok do
        failed := failed + 1
        IO.println s!"FAIL genstackargs: {name}\n{msg}"
  return failed

end GenStackArgsTests
