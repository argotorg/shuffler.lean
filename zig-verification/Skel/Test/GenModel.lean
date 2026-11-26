import Skel.Gen.Model
import Skel.Gen.Frame
import Skel.Gen.Vars
import Skel.Test.GenFrame
import Skel.Test.GenVars
import Lift.Spike.Code
import Lift.Toys.Code

/-! The tests of `Skel/Gen/Model.lean` (suite `genmodel`): `lake exe skel-test --only genmodel`. Each pure check is a value
that must hold. The declarations are compared after `squash`, so only the tokens count, not the layout. The hand text of
`toySum` is read from `Lift/Spike/Sum.lean` at run time. Where the field order differs from the hand text (the order of
`Reg64`), the expected text is a fixture here. The real checks write a Lean file for each text and run `lake env lean`
(through `GenFrameTests.leanCheck`): the text of `toySum` (no memory), of `toyFill` (memory), of a frame form, of a guarded
store, and of `toyJob` (a call). Each check file must be accepted. The property draws random block lists from the seed.
The suite gives the number of failed checks. -/

namespace GenModelTests

open Skel.Gen
open GenVarsTests (mkBlock rg ld st gotoT retT)

/-! ## Targets and summaries -/

/-- The target of `toySum`: the names of the constants of the hand chain (`Lift/Spike/L1.lean`, `Lift/Spike/Sum.lean`). -/
def sumTarget : Target :=
  { step := "L1.step", lo := "toyJobPC", hi := "toyEndPC", entryPC := "toySumPC",
    imports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.SysV", "Lift.Spike.L1"], callees := [] }

/-- The target of `toyJob`: the entry is `toyJobPC`; the callee `toySum` has the model `Sum`, with the inputs in the
order of `Reg64`. -/
def jobTarget : Target :=
  { step := "L1.step", lo := "toyJobPC", hi := "toyEndPC", entryPC := "toyJobPC",
    imports := ["Lift.Spike.Sum", "Lift.Sem.StackRoom", "Lift.Spike.L1"],
    callees := [⟨".Ltoy.toySum", "Sum", [.rsi, .rdi], "toySumPC", 0, false, 0, none⟩] }

/-- The summary of the function `fn` of `code`, with the frame facts of the callee rooms `rooms`. -/
def summaryOf (code : Executable) (fn : String) (rooms : List (String × Nat)) : Except GenError Summary := do
  let bs ← GenFrameTests.blocksOf code fn
  pure ⟨fn, bs, vars bs, ← frameFacts rooms bs, none⟩

/-- The model text of the summary `s`, with the frame text of the form `storeChain`. -/
def textOf (t : Target) (rooms : List (String × Nat)) (s : Summary) : Except GenError String := do
  let fr ← frameText .storeChain rooms s
  pure (modelText t s fr)

/-- The model text of the function `fn` of `code`. -/
def textFn (t : Target) (code : Executable) (fn : String) (rooms : List (String × Nat)) : Option String :=
  (summaryOf code fn rooms >>= textOf t rooms).toOption

/-- The summary of the blocks `bs`: the variables of `Skel.Gen.vars`, and the frame facts with no callee room. -/
def synth (name : String) (bs : List Block) : Option Summary :=
  (frameFacts [] bs).toOption.map fun ff => ⟨name, bs, vars bs, ff, none⟩

/-- A synthetic function: a push of `rbx`, a jump, and a pop of `rbx` before the return. The stack room is 8, and the
form is `frame`. -/
def frameSum : Option Summary :=
  synth "framed"
    [ mkBlock "entry" 0 [st (.sub (rg .rsp) (.lit 8)) (rg .rbx)] [(.rsp, .sub (rg .rsp) (.lit 8))] (gotoT 4),
      mkBlock "o4" 4 [ld (rg .rsp)] [(.rbx, .load 0), (.rax, .lit 0), (.rsp, .add (rg .rsp) (.lit 16))] retT ]

/-- A synthetic function: a push of `rbx`, then a store through `rdi` of `rax`, then a trap. The stack room is 8, the
memory is in the state, and the store through `rdi` is guarded. -/
def guardSum : Option Summary :=
  synth "guarded"
    [ mkBlock "entry" 0 [st (.sub (rg .rsp) (.lit 8)) (rg .rbx), st (rg .rdi) (rg .rax)]
        [(.rsp, .sub (rg .rsp) (.lit 8))] (.exit .trap) ]

/-- A synthetic function that writes `rax` with 5 and returns. -/
def oneBlockSum : Option Summary :=
  synth "one" [ mkBlock "entry" 0 [] [(.rax, .lit 5), (.rsp, .add (rg .rsp) (.lit 8))] retT ]

/-- A summary with no block. -/
def emptySum : Option Summary := synth "empty" []

/-! ## Helpers -/

/-- The declaration `name` of `text`, after `squash`. The empty string when there is none. -/
def decl (text name : String) : String := squash ((declText text name).getD "")

/-- Does the squashed declaration `d` have the field `name : UInt64`? -/
def hasField (d name : String) : Bool := (d.splitOn s!" {name} : UInt64").length > 1

/-- The lower-case name of a 64-bit register (the names of the fields). -/
def regLower : Reg64 → String
  | .rax => "rax" | .rbx => "rbx" | .rcx => "rcx" | .rdx => "rdx"
  | .rsi => "rsi" | .rdi => "rdi" | .rsp => "rsp" | .rbp => "rbp"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- The model text of `toySum`. -/
def sumText : Option String := textFn sumTarget Lift.Spike.Code.code "toySum" []

/-- The model text of `toyFill`: a store through a register, no stack use. -/
def fillText : Option String := textFn sumTarget Lift.Toys.Code.code "toyFill" []

/-- The model text of `toyJob`: a call of `toySum` with the callee room 0. -/
def jobText : Option String := textFn jobTarget Lift.Spike.Code.code "toyJob" [(".Ltoy.toySum", 0)]

/-- The model text of the frame form. -/
def frameText' : Option String := frameSum >>= fun s => (textOf sumTarget [] s).toOption

/-- The model text of the guarded form. -/
def guardText : Option String := guardSum >>= fun s => (textOf sumTarget [] s).toOption

/-- The model text of a summary with one block and no input. -/
def oneText : Option String := oneBlockSum >>= fun s => (textOf sumTarget [] s).toOption

/-- The model text of a summary with no block. -/
def emptyText : Option String := emptySum >>= fun s => (textOf sumTarget [] s).toOption

/-! ## The expected texts -/

/-- `In2` of `toySum` in the order of `Reg64`: `rsi` before `rdi`. The hand text has `rdi` first. -/
def sumIn2 : String := "structure In2 where policy : CpuPolicy mem : DataMem rsi : UInt64 rdi : UInt64"

/-- `l2` of `toySum` with the conjuncts in the order of `In2`. -/
def sumL2 : String := squash "def l2 : Model In2 UInt64 where
  rep policy a s := a.policy = policy ∧ a.mem = s.data.dmem ∧
    SysV.Entry policy toyJobPC toyEndPC toySumPC s ∧ s.data.regs.rsi = a.rsi ∧ s.data.regs.rdi = a.rdi
  returns a r := blocks.Returns noCall .entry (init a) r
  post := post"

/-- `At` of `toySum` (the E1 text of `docs/one-way-lift-g1-plan-20261118.md`, section 4.1). -/
def sumAt : String := "def At (s₀ : MachineState) : Lbl → St In2 → MachineState → Prop
  | .entry, _, s => s = s₀
  | .LBB1_1, x, s => ∃ f, s = ⟨{ s₀.data with regs := { s₀.data.regs with rax := x.rax, rcx := x.rcx }, status := f }, toySumPC + 4⟩
  | .o9, x, s => ∃ f, s = ⟨{ s₀.data with regs := { s₀.data.regs with rax := x.rax, rcx := x.rcx }, status := f }, toySumPC + 9⟩
  | .LBB1_3, x, s => ∃ f, s = ⟨{ s₀.data with regs := { s₀.data.regs with rax := x.rax, rcx := x.rcx }, status := f }, toySumPC + 18⟩"

/-- The text of a check file: the imports, the text in a namespace, and the axioms of `t`. -/
def checkFile (imports : List String) (body : String) : String :=
  "\n".intercalate (imports.map fun i => s!"import {i}") ++
    "\n\nopen Lift.P2.Total Lift.Sem Lift.Spike\n\nnamespace GenModelCheck\n\n" ++ body ++
    "\n\nend GenModelCheck\n\ntheorem t : True := trivial\n\n#print axioms t\n"

/-- The variables and the model texts of the random block lists of the seeds `seed .. seed + max 300 cases`. A list the
frame rules refuse has no text, and gives no pair. -/
def randomTexts (seed cases : Nat) : List (Vars × String) :=
  (List.range (max 300 cases)).filterMap fun i =>
    let bs := GenVarsTests.randomBlocks (seed + i)
    match frameFacts [] bs with
    | .error _ => none
    | .ok ff =>
      let s : Summary := ⟨"rand", bs, vars bs, ff, none⟩
      (textOf sumTarget [] s).toOption.map fun t => (s.vars, t)

/-- The arm of `At` of the label `lbl` in the model text `text` (the text of the arm after `| .`), or the empty text. -/
def atArmOf (text lbl : String) : String :=
  let arms := (((text.splitOn "def At").getD 1 "").splitOn "\n  | .").drop 1
  (arms.find? (·.startsWith (lbl ++ ","))).getD ""

/-- The pure checks, each with its name. -/
def pureChecks (hand : String) (seed cases : Nat) : List (String × Bool) :=
  let sumT := sumText.getD ""
  let fillT := fillText.getD ""
  let jobT := jobText.getD ""
  let frT := frameText'.getD ""
  let gT := guardText.getD ""
  let oneT := oneText.getD ""
  let emptyT := emptyText.getD ""
  [ -- toySum: the texts exist, and the hand declarations
    ("toySum: the text exists", sumText.isSome),
    ("toySum: Lbl is the hand Lbl", decl sumT "Lbl" == decl hand "Lbl"),
    ("toySum: St is the hand St (no memory)",
      decl sumT "St" == "structure St (I : Type) where input : I rax : UInt64 rcx : UInt64"),
    ("toySum: init is the hand init", decl sumT "init" == decl hand "init"),
    ("toySum: blocks is the hand blocks (the updates in the order of the hand)",
      decl sumT "blocks" == decl hand "blocks"),
    ("toySum: post is the hand post", decl sumT "post" == decl hand "post"),
    ("toySum: In2 in the order of Reg64", decl sumT "In2" == sumIn2),
    ("toySum: l2 in the order of In2", decl sumT "l2" == sumL2),
    ("toySum: At is the E1 text", decl sumT "At" == decl sumAt "At"),
    ("toySum: no frame text, no guard (room 0)", !sumT.contains "Frame" && !sumT.contains "sp : BitVec"),
    -- boundary and negative cases
    ("the empty block list gives the model of one entry label", decl emptyT "Lbl" == "inductive Lbl where | entry"),
    ("the empty block list: blocks gives no block", emptyT.contains "\"no block\""),
    ("one block, no input: In2 has no register field",
      decl oneT "In2" == "structure In2 where policy : CpuPolicy mem : DataMem"),
    ("one block, no input: St has no memory and one state field",
      decl oneT "St" == "structure St (I : Type) where input : I rax : UInt64"),
    ("one block, no input: init is polymorphic", decl oneT "init" == "def init {I : Type} (a : I) : St I := ⟨a, 0⟩"),
    ("one block, no input: the return value is the literal", (squash oneT).contains "| .entry, x => .ok (.ret 5)"),
    -- memory form (toyFill)
    ("toyFill: St has the memory parameter M", (decl fillT "St").startsWith "structure St (I M : Type) where input : I"),
    ("toyFill: St has the field mem of type M", (decl fillT "St").contains "mem : M"),
    ("toyFill: blocks is a Leaf over the pair with the memory",
      fillT.contains "def blocks : Leaf Lbl (St In2 DataMem) (UInt64 × DataMem) where"),
    ("toyFill: init copies the input memory", fillT.contains "⟨a, 0, a.mem⟩"),
    ("toyFill: post reads the memory of the result", (decl fillT "post").contains "t.data.dmem = r.2"),
    ("toyFill: At has the memory of the state", fillT.contains "dmem := x.mem"),
    ("toyFill: the guard at room 0: In2 has the field sp, and the store is guarded",
      (decl fillT "In2").contains "sp : BitVec 64" && fillT.contains "if Clear x.input.sp"),
    -- call form (toyJob)
    ("toyJob: blocks is the call form with the callee In2 of Sum",
      jobT.contains "def blocks : Blocks Lbl (St In2 DataMem) (UInt64 × DataMem) Unit (fun _ => Sum.In2) (fun _ => UInt64) where"),
    ("toyJob: the callee relation is the model of Sum", jobT.contains "(fun _ => Sum.l2.returns)"),
    ("toyJob: a call step with the policy and the memory of the call", jobT.contains ".call () ⟨x.input.policy, m"),
    ("toyJob: the store to total is guarded", jobT.contains "if Clear x.input.sp"),
    -- `At` of toyJob (G1-12): before the first write, after a call, and the stack words
    ("toyJob: At at o10 and LBB0_3 names rbx, rsi and rdi, and not rax",
      ["o10", "LBB0_3"].all fun l => (atArmOf jobT l).contains "rbx := x.rbx, rsi := x.rsi, rdi := x.rdi" &&
        !(atArmOf jobT l).contains "rax"),
    ("toyJob: At at o10 has the entry value of the callee-saved rbx", (atArmOf jobT "o10").contains "x.rbx = s₀.data.regs.rbx"),
    ("toyJob: At after the call (o26) names rax and rbx, and not rsi and rdi",
      let a := atArmOf jobT "o26"
      a.contains "s.data.regs.rax = x.rax" && a.contains "s.data.regs.rbx = x.rbx" && !a.contains "rsi" && !a.contains "rdi"),
    ("toyJob: At after the call keeps the callee-saved registers that the code does not write",
      let a := atArmOf jobT "o26"
      ["rbp", "r12", "r13", "r14", "r15"].all fun r => a.contains s!"s.data.regs.{r} = s₀.data.regs.{r}"),
    ("toyJob: At after the call has the rsp and the memory of the state",
      let a := atArmOf jobT "o26"
      a.contains "s.data.regs.rsp = s₀.data.regs.rsp - 8" && a.contains "s.data.dmem = x.mem"),
    ("toyJob: At after the call has the word of the pushed rbx",
      (atArmOf jobT "o26").contains "readRam x.input.policy x.mem (x.input.sp - 8) .W64 = .ok s₀.data.regs.rbx.toBitVec"),
    ("toyJob: the stack word is not in the arms before the push",
      ["o10", "LBB0_3"].all fun l => !(atArmOf jobT l).contains "readRam"),
    -- frame form
    ("frame form: Frame is defined over the memory",
      frT.contains "def Frame (policy : CpuPolicy) (s₀ : MachineState) (m : DataMem) : Prop"),
    ("frame form: At takes the policy",
      frT.contains "def At (policy : CpuPolicy) (s₀ : MachineState) : Lbl → St In2 → MachineState → Prop"),
    ("frame form: each At arm but the entry ends with the Frame conjunct, and the entry is s = s₀ (G1-16)",
      (frT.splitOn "∧ Frame policy s₀ s.data.dmem").length - 1 == 1 && frT.contains "| .entry, _, s => s = s₀\n"),
    ("frame form: an arm after the entry has the conjunction form, with the rsp of its depth (G1-16)",
      frT.contains "s.data.regs.rsp = s₀.data.regs.rsp - 8" && !frT.contains "∃ f, s ="),
    ("frame form: rep has the stack room", frT.contains "SysV.StackRoom policy s 8"),
    ("frame form: no guard without a heap store", !frT.contains "sp : BitVec"),
    ("frame form: init copies the entry rbx and sets rax to 0",
      decl frT "init" == "def init (a : In2) : St In2 := ⟨a, 0, a.rbx⟩"),
    ("frame form: a pop of the saved rbx reads the entry rbx", frT.contains "let v := x.input.rbx.toBitVec"),
    ("frame form: no stuck step for the saved register", !frT.contains "stack load"),
    -- guarded store
    ("guard: In2 has the field sp", (decl gT "In2").contains "sp : BitVec 64"),
    ("guard: St has the memory parameter", (decl gT "St").startsWith "structure St (I M : Type) where"),
    ("guard: a heap store is guarded by Clear", gT.contains "if Clear x.input.sp (x.input.rdi.toBitVec) then"),
    ("guard: the definitions of the private area",
      gT.contains "abbrev Private (sp b : BitVec 64) : Prop := (b - (sp - 8)).toNat < 16"),
    ("guard: rep has the sp conjunct", gT.contains "a.sp = s.data.regs.rsp.toBitVec"),
    ("guard: a trap is stuck", gT.contains ".stuck \"trap\""),
    ("guard: no frame form (the memory is in the state)", !gT.contains "def Frame"),
    -- the property: the fields of the text are the fields of Vars
    ("the random lists: each state register is a field of St, each input a field of In2, and St has M iff a store",
      (randomTexts seed cases).all fun (v, t) =>
        v.state.all (fun r => hasField (decl t "St") (regLower r))
          && v.inputs.all (fun r => hasField (decl t "In2") (regLower r))
          && ((decl t "St").startsWith "structure St (I M : Type)" == v.mem)),
    ("the random lists: at least 10 of the lists have a model text (the frame rules refuse the others)",
      (randomTexts seed cases).length ≥ 10) ]

/-! ## The real checks: Lean runs -/

/-- The Lean checks: each text, with its imports, is accepted. Gives the name, whether it is accepted, and the message. -/
def leanChecks : IO (List (String × Bool × String)) := do
  let frameImports := ["Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Sem.SysV", "Lift.Sem.StackRoom", "Lift.Tactic.FrameMemLemmas",
    "Lift.Spike.L1"]
  let cases : List (String × Option String × List String) :=
    [ ("toySum (no memory)", sumText, sumTarget.imports),
      ("toyFill (memory)", fillText, sumTarget.imports),
      ("the frame form", frameText', frameImports),
      ("the guarded form", guardText, frameImports),
      ("toyJob (a call)", jobText, jobTarget.imports) ]
  let mut out := []
  for (name, text, imports) in cases do
    match text with
    | none => out := out ++ [(name, false, "no text")]
    | some t =>
      -- a text with no `blocks` declaration would be an empty file, which Lean accepts
      if !t.contains "def blocks" then
        out := out ++ [(name, false, "no blocks declaration")]
      else
        let (ok, msg) ← GenFrameTests.leanCheck "genmodel" (checkFile imports t) "t"
        out := out ++ [(name, ok, msg)]
  return out

/-- Gives the number of failed checks. The suite runs when `only` is none or `genmodel`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genmodel" then return 0
  let hand ← IO.FS.readFile "Lift/Spike/Sum.lean"
  let mut failed := 0
  for (name, ok) in pureChecks hand seed cases do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genmodel: {name}"
  for (name, ok, msg) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genmodel: Lean accepts the text of {name}\n{msg}"
  return failed

end GenModelTests
