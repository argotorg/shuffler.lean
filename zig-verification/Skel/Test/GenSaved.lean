import Skel.Test.GenStmt
import Skel.Test.Saved.L1
import Skel.Test.GenL2Gate

/-! The tests of the stack words of the proof of `decompiles_l2` (suite `gensaved`, task AF-B):
`lake exe skel-test --only gensaved`. A saved register is found by the depth of its stack word, for any number of pushes and
pops.

* IO checks (Lean must accept the check file with the three standard axioms): callers of `leaf` that push 2 or 4 registers
  (`Skel/Test/Saved/Code.lean`), with the store through a register before the call (`save2`, `save4`) and after it
  (`save2b`, `save4b`).
* A function with no store through a register has the frame form (`save2n`): its entry block and the block of the call
  load through a register (PIL-HEAP). `rep` has `SysV.Hidden` (the entry memory with the room unmapped), and Lean accepts the
  check file with the three standard axioms. Mutation: the same file with the `rep` conjunct `a.mem = s.data.dmem` (the form
  before PIL-HEAP) is rejected.
* PIL-HEAP, pure: a synthetic frame (room 16) with a push of a constant, one heap load and the pop has a proof with no `fail`
  that reads the heap with `SysV.Hidden.readRam`. Negative: a load through `rsp` in the room that no push gives takes the stack
  rule (the stuck case, no `Hidden.readRam`), and a load through `rsp` at the return word or above is the named `fail`.
* The frame form (G1-16): `frame8` (a slot of 8 bytes), `frame4` (a slot of 4 bytes) and `frameCall` (a push and a call of
  `leaf`): Lean accepts the check file with the three standard axioms, and the proofs have no `fail`.
* A pop into another register than the one pushed at its depth (`save2x`) gives the documented `fail` of the case of the
  block with the pops: `an exit or a fact that the proof does not cover`; the case of each other block has no `fail`.
* Property: for `1 ≤ n ≤ 8` saved registers, the proof of the synthetic function of `pushCall n` has no `fail`, and the
  function whose pops are in the order of the pushes has a `fail`. -/

namespace GenSavedTests

open Skel Skel.Gen GenStmtTests
open GenVarsTests (mkIdent)

/-! ## The cases of the code `Skel/Test/Saved/Code.lean` -/

/-- The callee `leaf`: `rax := rdi`, no stack room. -/
def leafCallee : Callee := ⟨".Lfix.leaf", "Leaf", [.rdi], "leafPC", 0, false, 0, none⟩

def savedImports : List String :=
  ["Std.Tactic.BVDecide", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.HeapLemmas", "Lift.Sem.SysV", "Skel.Test.Saved.L1",
    "Lift.Spike.Sites", "Lift.Tactic.Block", "Lift.Sem.StackRoom", "Lift.Spike.Sites.Stack", "Lift.Tactic.FrameMem"]

def savedTarget (pc : String) (callees : List Callee) : Target :=
  { step := "Skel.Test.Saved.L1.step", lo := "leafPC", hi := "savedEndPC", entryPC := pc, imports := [], callees := callees }

/-- `leaf`, the closed callee of the other cases. -/
def leafCase : IoCase :=
  { name := "leaf", target := savedTarget "leafPC" [], code := Skel.Test.Saved.Code.code, fn := "leaf",
    imports := savedImports, opens := "Skel.Test.Saved Lift.Spike" }

/-- The model of the generated `leaf` in its namespace `Leaf`, with its block lemmas and its `decompiles_l2`. -/
def leafPre : String :=
  ((partOf leafCase).map fun p => s!"namespace Leaf\n\n{p}\n\nend Leaf\n\n").getD ""

/-- A caller of `leaf`: the function `fn`, with the entry PC `fn ++ "PC"`. -/
def savedCase (fn : String) : IoCase :=
  { name := fn, target := savedTarget s!"{fn}PC" [leafCallee], code := Skel.Test.Saved.Code.code, fn := fn,
    imports := savedImports, opens := "Skel.Test.Saved Lift.Spike", rooms := [(leafCallee.name, 0)], pre := leafPre }

/-- The functions that Lean must accept. -/
def acceptedFns : List String := ["save2", "save2b", "save4", "save4b"]

/-- The functions of the frame form that Lean must accept (G1-16; `save2n` loads through a register, PIL-HEAP). -/
def frameFns : List String := ["frame8", "frame4", "frameCall", "save2n"]

/-- The mutation of PIL-HEAP: `save2n` with the `rep` of the input memory before the fix. Lean must reject it. -/
def save2nUnhidden : IoCase := { savedCase "save2n" with name := "save2n-unhidden", patch := GenL2GateTests.unhide }

def ioChecks : IO (List (String × Bool × String)) := do
  let oks ← (acceptedFns ++ frameFns).mapM fun fn => ioCheck (savedCase fn)
  let mut' ← match ← ioRun save2nUnhidden with
    | some (.failed _, _) => pure ("PIL-HEAP mutation: save2n with rep a.mem = s.data.dmem is rejected", true, "")
    | other => pure ("PIL-HEAP mutation: save2n with rep a.mem = s.data.dmem is rejected", false,
        s!"{repr (other.map (·.1))}")
  let hidden := (partOf (savedCase "save2n")).any fun t => (t.splitOn "SysV.Hidden s ").length == 2 && GenL2GateTests.unhide t != t
  pure (oks ++ [mut', ("PIL-HEAP: the rep of save2n has SysV.Hidden, and the mutation changes it", hidden, "")])

/-! ## The synthetic functions of the property -/

private def I (s : String) : Ident := mkIdent s

private def rspV : Val := .reg .rsp

private def minus (v : Val) (k : UInt64) : Val := .sub v (.lit k)

private def plus (v : Val) (k : UInt64) : Val := .add v (.lit k)

/-- `rsp` lowered `n` times by 8 (the symbolic execution does not fold constants). -/
private def downs (v : Val) (n : Nat) : Val := (List.range n).foldl (fun v _ => minus v 8) v

/-- `rsp` raised `n` times by 8. -/
private def ups (v : Val) (n : Nat) : Val := (List.range n).foldl (fun v _ => plus v 8) v

/-- The registers that a synthetic function saves, in the order of the pushes. -/
private def savedRegs : List Reg64 := [.rbx, .r14, .r15, .rbp, .r12, .r13, .rbx, .r14]

/-- A function with `n` saved registers: the entry pushes them, stores through `rdi`, and calls `f`; the continuation pops
them (`reverse` is the order of the pops: true is the order of the ABI) and returns. -/
def pushCall (n : Nat) (reverse : Bool) : Summary :=
  let saved := savedRegs.take n
  let pushes := (List.range n).map fun k => Access.store k (downs rspV (k + 1)) .W64 (.reg (saved.getD k .rbx))
  let entry : Block := ⟨I "entry", 0,
    pushes ++ [Access.store n (plus (.reg .rdi) 24) .W64 (.reg .rax), Access.store (n + 1) (downs rspV (n + 1)) .W64 (.retAddr 20)],
    [(.rsp, downs rspV (n + 1))], .exit (.call "f" 20), []⟩
  let pops := (List.range n).map fun k => Access.load k (ups rspV k) .W64
  let ret := Access.load n (ups rspV n) .W64
  let order := if reverse then saved.reverse else saved
  let popRegs := (List.range n).map fun k => (order.getD k .rbx, Val.load k)
  let o20 : Block := ⟨I "o20", 20, pops ++ [ret], popRegs ++ [(.rsp, ups rspV (n + 1))], .exit .ret, []⟩
  let bs := [entry, o20]
  ⟨"pushCall", bs, vars bs, ⟨[(0, 0), (20, 8 * n)], 8 * n + 8⟩, none⟩

/-- PIL-HEAP: a frame of room 16 in one block: a push of a constant, one load through `rdi` (at `rdi + off` when `heap`, else
the stack word `rsp - k`, or `rsp + k` for `k < 0`), the pop of the push into `rcx`, and the return. -/
def heapFrame (heap : Bool) (k : Int) : Summary :=
  let addr : Val := if heap then plus (.reg .rdi) 16
    else if k < 0 then plus rspV (UInt64.ofNat (-k).toNat) else minus rspV (UInt64.ofNat k.toNat)
  let accs := [Access.store 0 (minus rspV 8) .W64 (.lit 7), Access.load 0 addr .W64, Access.load 1 (minus rspV 8) .W64,
    Access.load 2 rspV .W64]
  let entry : Block := ⟨I "entry", 0, accs, [(.rax, .load 0), (.rcx, .load 1), (.rsp, plus rspV 8)], .exit .ret, []⟩
  let bs := [entry]
  ⟨"heapFrame", bs, vars bs, ⟨[(0, 0)], 16⟩, none⟩

/-- The target of the synthetic functions: the callee `f` has the room 0. -/
def synthTarget : Target :=
  { step := "L1.step", lo := "lo", hi := "hi", entryPC := "fPC", imports := [], callees := [⟨"f", "F", [.rdi], "fPC2", 0, false, 0, none⟩] }

/-- The text of the proof of a summary. -/
def proofOf (s : Summary) : Option String :=
  (frameText .storeChain [("f", 0)] s).toOption.map fun fr => decompilesProof synthTarget s fr

/-- The reasons of the `fail` calls of a text. -/
def failsOf (p : String) : List String :=
  ((p.splitOn "fail \"").tail).map fun s => (s.splitOn "\"").headD ""

def coverFail : String := "decompiles_l2: the case of this block is not generated: an exit or a fact that the proof does not cover"

/-! ## The checks -/

def pureChecks : List (String × Bool) :=
  let sizes := List.range 8 |>.map (· + 1)
  [ ("synthetic functions with 1 to 8 saved registers: the proof has no fail",
      sizes.all fun n => (proofOf (pushCall n true)).map (failsOf · |>.isEmpty) == some true),
    ("synthetic functions with 1 to 8 saved registers, pops in the order of the pushes: a pop of another register is a fail",
      sizes.all fun n =>
        if n == 1 then true
        else (proofOf (pushCall n false)).map (failsOf · == [coverFail]) == some true),
    ("save2x: the case of the block with the pops is the documented fail, and no other case has a fail",
      (caseProof (savedCase "save2x")).map (failsOf · == [coverFail]) == some true),
    ("save2n: the frame form, the entry and the block of the call load through a register: no fail, two reads by Hidden.readRam (PIL-HEAP)",
      (caseProof (savedCase "save2n")).map (fun p => (failsOf p).isEmpty && (p.splitOn "SysV.Hidden.readRam").length == 4) == some true),
    ("PIL-HEAP: a frame with a push, one heap load and the pop: no fail, one read by Hidden.readRam",
      (proofOf (heapFrame true 0)).map (fun p => (failsOf p).isEmpty && (p.splitOn "SysV.Hidden.readRam").length == 2) == some true),
    ("PIL-HEAP negative: a load through rsp in the room that no push gives takes the stack rule (stuck), not Hidden.readRam",
      (proofOf (heapFrame false 16)).map (fun p => (failsOf p).isEmpty && !p.contains "Hidden.readRam" && p.contains "all_goals cases hn") == some true),
    ("PIL-HEAP negative: a load through rsp at the return word is the named fail",
      (proofOf (heapFrame false 0)).map (fun p => failsOf p ==
        ["decompiles_l2: the case of this block is not generated: a stack load at or above the return word in the frame form"]) == some true),
    ("ARGS8 negative: a load of 8 bytes at rsp + 4 (above the return word, not a stack argument) has no frame text",
      (proofOf (heapFrame false (-4))).isNone),
    ("frame8, frame4, frameCall: the frame form: the proofs have no fail and no sorry",
      frameFns.all fun fn =>
        (caseProof (savedCase fn)).map (fun p => (failsOf p).isEmpty && !p.contains "sorry") == some true),
    ("save2, save2b, save4, save4b: the proofs have no fail and no sorry",
      acceptedFns.all fun fn =>
        (caseProof (savedCase fn)).map (fun p => (failsOf p).isEmpty && !p.contains "sorry") == some true) ]

def run (seed cases : Nat) (only : Option String) : IO Nat := do
  let _ := (seed, cases)
  if only.isSome && only != some "gensaved" then return 0
  let mut failed := 0
  for (name, ok) in pureChecks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  gensaved: {name}"
  for (name, ok, msg) in (← ioChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  gensaved: {name}\n{msg}"
  return failed

end GenSavedTests
