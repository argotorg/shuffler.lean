import Skel.Gen.UpperPlan
import Skel.Gen.Shape
import Skel.Gen.Model

/-! The text of the relations between L2 and L2⁺ and of the L3 link: `objsP`, `heapOf`, `outHeap`, `SimIn`, `SimSt`, `SimOut`,
`SimArr` and `l3` (`docs/one-way-lift-g3-plan-20261118.md`, sections 4.4 and 4.5, path B; task G3-08). The text is a function of
the target (the code range and the entry PC), the statement shape (the input, the arguments, the hypotheses and the objects, as
terms of the statement) and the plan (the fields, the kind, the parameters). The statement terms are copied, not interpreted.

The plan has no object kind: a statement whose objects are not given by its input and parameters is not checked here (the Lean
check of the file does that).

A `both` result of a function with a loop and one input also has `heapOf` (L3-U7): the heap of the input type that the refuter
and the templates give for the new contents `y.2` of a loop. A `both` result with no loop, or with several inputs, has none.

Decisions (the fixtures of section 2 decide them, or the rules name them):
* `outHeap <params> frame <inputs> y` is the output object function read from `post`, applied to `y`, mapped by `toObj`, then
  `++ frame`. `heapOf <params> frame y` keeps the input-object form for fixed templates and old shapes without run metadata.
* `l3` has the binders `<params> frame` and `pol` (for a heap result) in this order (4.5).
* A statement with one input (the toys) has the input as the input of the model. A statement with none or several inputs
  (`∀ dest i, C dest i → …`; `Shape.InputForm`) has them as binders of `objsP`, `SimArr` and `l3`, after the parameters and the
  frame (`l3 <params> frame <inputs> (pol)`); the model has the input type `Unit`, and `run` is applied to the inputs by name.
  Why: the statement applies `C`, `objects`, `post` and the arguments to the variables of the inputs, and a tuple could not
  hold `∀ {n} buf slot`, where the type of `buf` has `n`.
* The output of `l3` uses the run result type when the shape gives one. A heap result also needs its output object mapping.
  An old heap shape without either metadata field uses the type and objects of its sole input.
* The result kind `both` (L3-U3): the L3 result `y` is the pair (value, new contents), or a structure whose first field is the
  value (`PopSpec.Out`). The shape gives neither the type of `run` nor a term of the written objects of `y` (`post` is a name), so
  `l3` has the form `show Model T _ from { … }` (Lean takes the result type from `returns`), and `l3.post` states the value part
  as the value kind does, on `y.1`, and the memory part with the statement's `post` at the policy `pol` and the result field of
  `rax` (its `Mem.has` of the written objects), then the frame clause of the heap kind over `objsP … ++ frame`. There is no
  `heapOf`. `SimOut` relates the pairs: the same `rax`, and the heap part of the heap kind.
* The machine states of `l3` are `s` and `t`, primed when an input or a parameter has the name (`freshName`; the inputs of
  `MappingBuilder.map` are `dropped dest pos s t`).
* `run` of the L3 spec is the function that `post` names, as `#stmt_shape` reads it (`StmtShape.run`), else `<module of C>.run`
  (`StmtShape.runConst`); a statement with neither gives `GenError.shape`.
* A hypothesis of the statement is a conjunct in parentheses.
* `walkNodesProof` is the proof of the fixture helper `nodes` (W) against the statement's `nodes`; only the test uses it. -/

namespace Skel.Gen

/-- The argument registers of System V, in order (`Lift/Trusted/Call.lean`, `argRegs`). -/
private def argRegs : List Reg64 := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- The bit count of a width. A copy of `bitsOf` of `Model.lean`, which is private there. -/
private def bitsOf : Width → Nat
  | .W8 => 8 | .W16 => 16 | .W32 => 32 | .W64 => 64

/-- The name of the constructor of a width. -/
private def widthCtor : Width → String
  | .W8 => "W8" | .W16 => "W16" | .W32 => "W32" | .W64 => "W64"

/-- The Lean type of the L3 value of a value result: the output type of `l3`. -/
def ValueTy.outTy : ValueTy → String
  | .bits w => s!"(BitVec {bitsOf w})"
  | .bool => "Bool"

/-- The result field of the register value `r : BitVec 64` (`Fn.Return.result`): the low bits of the width of the value. -/
def ValueTy.field (v : ValueTy) (r : String) : String := s!"⟨.{widthCtor v.width}, {r}.setWidth {bitsOf v.width}⟩"

/-- The statement that the register value `r : BitVec 64` holds the L3 value `y` (4.4). A 64-bit result is the equation
`r = y`. A narrower result is the field of the low bits of `r` as `Encode` writes the value: the form of the `post` of the
trusted statements (`Encode.encode y = [r]` with `r = ⟨f.ret, rax.toBitVec.setWidth f.ret.bits⟩`, `Fn.Return.result`). -/
def ValueTy.rel (v : ValueTy) (r y : String) : String :=
  match v.width with
  | .W64 => s!"{r} = {y}"
  | w => s!"Lift.Trusted.Encode.encode {y} = [⟨.{widthCtor w}, {r}.setWidth {bitsOf w}⟩]"

/-- The encoded value of a result. A nontrivial projection comes from the statement's post. -/
def resultValueRel (v : ValueTy) (sh : StmtShape) (r y : String) (first : Bool := true) : String :=
  match sh.resultFn with
  | some f => s!"Lift.Trusted.Encode.encode (({f.s}) {y}) = [{v.field r}]"
  | none => v.rel r (if first then s!"{y}.1" else y)

/-- A projected value has its statement's run result type; other values use their ABI value type. -/
def resultValueTy (v : ValueTy) (sh : StmtShape) : String :=
  if sh.resultFn.isSome then (sh.runResultType.map (fun t => s!"({t.s})")).getD v.outTy else v.outTy

/-- A heap or a direct word has a term result in a loop row. A projected value needs a relation. -/
def termResult (p : UpperPlan) (sh : StmtShape) : Bool :=
  p.kind == .heap || (p.kind == .value && p.val.isWord && sh.resultFn.isNone)

/-- Whether `c` can continue an identifier. -/
private def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- The maximal runs of identifier characters and of other characters, in their order. -/
private def runsOf (s : String) : List String :=
  let step : List (String × Bool) → Char → List (String × Bool) := fun acc c =>
    match acc with
    | (w, b) :: rest => if isIdChar c == b then (w.push c, b) :: rest else (c.toString, isIdChar c) :: acc
    | [] => [(c.toString, isIdChar c)]
  ((s.toList.foldl step []).reverse).map (·.1)

/-- The text `s` with each identifier `old` renamed to `new` (a run of identifier characters equal to `old`). -/
def renameVar (old new s : String) : String :=
  String.join ((runsOf s).map fun w => if w == old then new else w)

/-- The Lean type of a parameter of `l3` (4.5). -/
private def tyText : BinderTy → String
  | .addr => "BitVec 64"
  | .addrs => "List (BitVec 64)"
  | .source type => type.s

/-- A parameter as a binder. -/
def binderText (b : Binder) : String := s!"({b.name.s} : {tyText b.ty})"

/-- The text of a term or a type as an operand: parentheses unless it is a name (`List.length x` and `List (BitVec 64)` need
them). -/
private def operand (t : String) : String :=
  if t.all (fun c => c.isAlphanum || c == '.' || c == '_') then t else s!"({t})"

/-- The type of the input of the model `l3`: the input type of the statement for one input, `Unit` otherwise (`InputForm`). -/
def modelTy (sh : StmtShape) : String :=
  match sh.form with
  | .one b => operand b.type.s
  | .flat _ => "Unit"

/-- The input of a heap result: the record that the heap function changes. A statement with no input or several has none: the
type of its heap is not an input type. -/
def heapInput (sh : StmtShape) : Except GenError ShapeBinder :=
  match sh.form with
  | .one b => .ok b
  | .flat bs => .error (.unsupported 0 s!"a heap result with {bs.length} inputs: the result heap is of the type of one input")

/-- The heap result type read from `post`. Old shapes without output metadata keep the input-type form. -/
def heapResultType (sh : StmtShape) : Except GenError String :=
  match sh.runResultType, sh.runOutputObjs with
  | some t, _ => .ok (operand t.s)
  | none, some _ => .error (.unsupported 0 "heap output objects have no run result type")
  | none, none => do pure (operand (← heapInput sh).type.s)

/-- The name `base`, primed when a variable of the statement (an input, a binder) or a parameter has it: a binder of a generated
text with this name does not hide a variable that the text copies (`freshAmong`). -/
def freshName (sh : StmtShape) (p : UpperPlan) (base : String) : String :=
  freshAmong (sh.names ++ p.params.map (·.name.s)) base

/-- The names that the generated texts use as they are, in every text and in the proof texts (`frame`, `pol`) or as constants
(`toObj`, `objsP`, `l3`, …): a variable of the statement with one of them would hide it, and a text cannot rename it. A name that
a text binds only locally (`a`, `y`, `policy`, `b`, `s`, `t`, `m`, …) is not here: `freshName` primes it. -/
def fixedNames : List String :=
  ["frame", "pol", "toObj", "objsP", "heapOf", "outHeap", "l3", "l2", "l2p", "SimArr", "SimIn", "SimSt", "SimOut", "In2", "In2p", "St", "StP",
   "blocksP", "noCall", "Model", "Refines", "Above", "Decompiles", "Reaches", "Private", "Covered", "Heap", "SysV", "CpuPolicy",
   "MachineState", "UInt64", "BitVec", "Unit", "Prop", "Nat", "Bool", resultRun]

/-- A variable of the statement or a parameter with a name of `fixedNames` is an error. -/
def checkNames (sh : StmtShape) (p : UpperPlan) : Except GenError Unit :=
  match (sh.names ++ p.params.map (·.name.s)).find? fixedNames.contains with
  | some n =>
    .error (.shape 0 s!"the name {n} of the statement is a name that the generated texts use as it is (frame, pol, a constant); a variable with it would hide it")
  | none => .ok ()

/-- The names of the parameters, in order. -/
private def paramNames (p : UpperPlan) : String := " ".intercalate (p.params.map (·.name.s))

/-- The names of the parameters and the inputs, in order: the arguments of `objsP`. -/
private def argNames (p : UpperPlan) (sh : StmtShape) : String := " ".intercalate (paramNames p :: sh.form.names)

/-- The heap of the result, keeping the entry inputs as arguments of the output mapping. Known result types need a mapping. -/
def heapResultExpr (p : UpperPlan) (sh : StmtShape) (y : String) : Except GenError String :=
  match sh.runResultType, sh.runOutputObjs with
  | some _, some _ => .ok (" ".intercalate (["outHeap"] ++ p.params.map (·.name.s) ++ ["frame"] ++ sh.form.names ++ [y]))
  | none, none => do
    let _ ← heapInput sh
    pure (" ".intercalate (["heapOf"] ++ p.params.map (·.name.s) ++ ["frame", y]))
  | some _, none => .error (.unsupported 0 "heap run result has no output object mapping")
  | none, some _ => .error (.unsupported 0 "heap output objects have no run result type")

/-- The conjunction of the parts, each part as written. -/
private def conj (parts : List String) : String := " ∧ ".intercalate parts

/-- The source contract and hypotheses, each in parentheses. A statement without a contract uses `True`. -/
private def hypParts (sh : StmtShape) : List String :=
  ((if sh.contract.s == "True" then [] else [sh.contract]) ++ sh.hyps).map fun h => s!"({h.s})"

/-- The equation of the register `r` with the argument `a`, over the object `obj` (4.5): the form `nat t` (the value is
`BitVec.ofNat 64 t`) gives `toNat = t`; the form `bv` with a 64-bit field gives `toBitVec = t`; a narrower width gives
`toBitVec.setWidth w = t`. -/
private def argEq (obj : String) (field : String) (a : ArgShape) : String :=
  let reg := s!"{obj}.{field}"
  match a.form, a.width with
  | .nat t, _ => s!"{reg}.toNat = {operand t.s}"
  | .bv, .W64 => s!"{reg}.toBitVec = {operand a.term.s}"
  | .bv, w => s!"{reg}.toBitVec.setWidth {bitsOf w} = {operand a.term.s}"

/-- The input fields hold the register arguments followed by the ABI stack arguments.
Call8 supplies its stack words separately. Their bit-vector equations need no bound on a natural-number term. -/
private def argEqs (obj : String) (p : UpperPlan) (sh : StmtShape) : List String :=
  (sh.args.zipIdx.filterMap fun (a, i) =>
    match argRegs[i]? with
    | some r => if sh.call.stack.isEmpty || p.inputs.contains r then some (argEq obj (regLower r) a) else none
    | none => some (argEq obj (stkName (i - argRegs.length)) a)) ++
  ((sh.call.stack.take p.stackArgs).zipIdx.map fun (a, i) =>
    s!"{obj}.{stkName i}.toBitVec = {operand a.term.s}")

/-- `objsP` (4.5): the statement's objects over the parameters and the inputs, mapped by `toObj`. -/
private def objsText (p : UpperPlan) (sh : StmtShape) : String :=
  s!"def objsP {" ".intercalate ((p.params.map binderText) ++ sh.form.binderTexts)} : Heap := ({sh.objs.s}).map toObj"

/-- `heapOf` (4.5, heap results): `objsP` with the input renamed to `y`, then the frame. -/
private def heapOfText (p : UpperPlan) (sh : StmtShape) (b : ShapeBinder) : String :=
  let y := freshName sh p "y"
  let binders := (p.params.map binderText) ++ ["(frame : Heap)", s!"({y} : {b.type.s})"]
  s!"def heapOf {" ".intercalate binders} : Heap := ({renameVar b.name.s y sh.objs.s}).map toObj ++ frame"

/-- The output objects from `post`, mapped to heap objects, followed by the frame. Entry inputs remain explicit. -/
private def outHeapText (p : UpperPlan) (sh : StmtShape) : Except GenError (List String) := do
  let some f := sh.runOutputObjs | return []
  let ty ← heapResultType sh
  let y := freshName sh p "y"
  let binders := (p.params.map binderText) ++ ["(frame : Heap)"] ++ sh.form.binderTexts ++ [s!"({y} : {ty})"]
  pure [s!"def outHeap {" ".intercalate binders} : Heap := (({f.s}) {y}).map toObj ++ frame"]

/-- The conjuncts of `SimIn` for a stack room with memory in the state (`UpperPlan.memRoom`, PIL-CALL3): no object of the heap
meets the room, and the L2 memory has the room (`SysV.RoomAt`, the `StackRoom` of `l2.rep`). The L2 model writes the pushes
into the memory and reads the pops from it; these facts give the writes, the reads, and `Holds` after a push. -/
def roomIn (p : UpperPlan) : List String :=
  if p.memRoom then [s!"(∀ c, SysV.Below b.sp {p.room} c → ¬ Covered a.heap c)", s!"SysV.RoomAt b.policy b.mem b.sp {p.room}"]
  else []

/-- The conjuncts of `SimSt` for a stack room with memory in the state: as `roomIn`, for the heap and the memory of the state. -/
def roomSt (p : UpperPlan) : List String :=
  if p.memRoom then
    [s!"(∀ b, SysV.Below y.input.sp {p.room} b → ¬ Covered x.mem b)", s!"SysV.RoomAt y.input.policy y.mem y.input.sp {p.room}"]
  else []

/-- `SimIn` (4.4): the policy iff the result has a heap, the registers of the inputs, then the heap holds the L2 memory, the
byte-range permission of the heap for `Fn.CallB` (D40), for a state with memory (a guarded store) no object covers the
private area of the L2 stack pointer, and the conjuncts of `roomIn`. -/
private def simInText (p : UpperPlan) : String :=
  let policy := if p.kind.hasPolicy then ["a.policy = b.policy"] else []
  let regs := p.inputs.map (fun r => s!"a.{regLower r} = b.{regLower r}") ++
    (List.range p.stackArgs).map (fun k => s!"a.{stkName k} = b.{stkName k}")
  let area := if p.mem then ["(∀ c, Private b.sp c → ¬ Covered a.heap c)"] else []
  let permits := p.call.permitsConj "a.heap" "b.policy"
  let sp := if p.mem then ["a.sp = b.sp"] else []
  s!"def SimIn (a : In2p) (b : In2) : Prop := {conj (policy ++ regs ++ ["a.heap.Holds b.policy b.mem"] ++ permits ++ area ++ roomIn p ++ sp)}"

/-- `SimSt` (4.4): `SimIn` of the inputs, one equation for each state register in the order of `St`, then the memory
conjuncts when the state has a memory. -/
private def simStText (p : UpperPlan) : String :=
  let stIn := p.stateType
  let stOut := if p.mem then "St In2 DataMem" else "St In2"
  let memParts := if p.mem then ["x.mem.Holds y.input.policy y.mem",
    let fc := if p.kind == .value then p.valueFrameClause "b" "y.input.sp" "y.mem" "y.input.mem"
      else p.frameClause "b" "x.input.heap" "y.input.sp" "y.mem" "y.input.mem"
    if p.memRoom then s!"({fc})" else fc] ++ roomSt p else []
  let regs := p.state.map (fun (r, _) => s!"x.{regLower r} = y.{regLower r}") ++
    p.flags.map (fun f => s!"x.{f.name} = y.{f.name}")
  let mem := if p.mem then "y.mem" else "y.input.mem"
  let stackParts := if p.privateStack then
    [s!"(∀ offset byte, x.stack offset = some byte → {mem}.get? (y.input.sp + BitVec.ofInt 64 offset) = some (UInt8.ofNat byte.toNat))"]
    else []
  s!"def SimSt (x : {stIn}) (y : {stOut}) : Prop := {conj (["SimIn x.input y.input"] ++ regs ++ memParts ++ stackParts)}"

/-- `SimOut` (4.4, heap results): the heap holds the L2 memory, and each byte outside the input heap is that of L2; for
`both`, the pairs have the same `rax` first. The stack clause of `Job.lean` is not generated: a function with a heap result and
a stack room and memory (`UpperPlan.memRoom`) excludes the room from the frame clause. -/
private def simOutText (p : UpperPlan) : String :=
  let heap (r r' : String) := s!"{r}.Holds x.policy {r'} ∧ {p.frameClause "b" "x.heap" "y.sp" r' "y.mem"}"
  match p.kind with
  | .value => s!"def SimOut (_ : In2p) (y : In2) (r : UInt64) (r' : UInt64 × DataMem) : Prop := r = r'.1 ∧ " ++
      p.valueFrameClause "b" "y.sp" "r'.2" "y.mem"
  | .both => "def SimOut (x : In2p) (y : In2) (r : UInt64 × Heap) (r' : UInt64 × DataMem) : Prop := r.1 = r'.1 ∧ " ++
      heap "r.2" "r'.2"
  | _ => s!"def SimOut (x : In2p) (y : In2) (r : Heap) (r' : DataMem) : Prop := {heap "r" "r'"}"

/-- The L2⁺ relations for a callee interface, independent of an L3 statement. -/
def upperSimText (p : UpperPlan) : String :=
  "\n\n".intercalate ([simInText p, simStText p] ++
    if p.kind.hasPolicy || p.mem then [simOutText p] else [])

/-- `SimArr` (4.5): the contract, the hypotheses, the argument equations over `a`, the heap is `objsP` with the frame, and some policy and
memory hold it (the policy is `a.policy` for a result with a heap, since `In2p` has it). -/
private def simArrText (p : UpperPlan) (sh : StmtShape) : Except GenError String := do
  let a := freshName sh p "a"
  let eqs := argEqs a p sh
  let holds := if p.kind.hasPolicy then s!"∃ m, {a}.heap.Holds {a}.policy m" else s!"∃ policy m, {a}.heap.Holds policy m"
  let parts := hypParts sh ++ eqs ++ [s!"{a}.heap = objsP {argNames p sh} ++ frame", holds]
  let binders := (p.params.map binderText) ++ ["(frame : Heap)"] ++ sh.form.binderTexts ++ [s!"({a} : In2p)"]
  pure s!"def SimArr {" ".intercalate binders} : Prop := {conj parts}"

/-- The conjunct of the stack arguments of `Call8` (L2-NORUN): the two read-only words `g` and `h` at `rsp + 8`, just above the
return word, as the hypothesis of `Call8` states them (`Lift.Level2z.Args8Statement.stackArgs`); none for the other forms. -/
def stackConj (policy s : String) : CallForm → List String
  | .call8 g h | .call8B g h =>
    [s!"Lift.Trusted.Mem.has {policy} {s}.data.dmem ⟨{s}.data.regs.rsp.toBitVec + 8, [⟨.W64, {g.term.s}⟩, ⟨.W64, {h.term.s}⟩], false⟩"]
  | _ => []

/-- `l3` (4.5): `rep` with the policy, the heap of the objects with the frame, its byte-range permission for `Fn.CallB` (D40),
the contract, the hypotheses, the entry, one register equation per argument, and the stack room of the code (`SysV.StackRoom policy s <room>`,
L3-U5; the entry state of `Fn.Entry` has the room). The result is a value (`ValueTy`: `BitVec 64`, or a narrower value compared on the low bits of `rax`), a
heap (the run result type, with the policy `pol`), or both (the type of `run`, with `pol`; see the top of the file). The binders are
the parameters, the frame, the inputs when there are none or several (`InputForm`: the model has the input type `Unit`), and
`pol` for a result with a heap. The machine states are `s` and `t` (`freshName`). -/
private def l3Text (tg : Target) (p : UpperPlan) (sh : StmtShape) : Except GenError String := do
  let s := freshName sh p "s"
  let t := freshName sh p "t"
  let y := freshName sh p "y"
  let b := freshName sh p "b"
  let policy := freshName sh p "policy"
  let hasPol := p.kind.hasPolicy
  let objs := s!"objsP {argNames p sh} ++ frame"
  let eqs := (argRegs.zip sh.args).map fun (r, arg) => argEq s!"{s}.data.regs" (regLower r) arg
  let parts := (if hasPol then [s!"{policy} = pol"] else []) ++
    [s!"Heap.Holds {policy} ({objs}) {s}.data.dmem"] ++ p.call.permitsConj s!"({objs})" policy ++ hypParts sh ++
    [s!"SysV.Entry {policy} {tg.lo} {tg.hi} {tg.entryPC} {s}"] ++ eqs ++
    (if p.mem then [s!"(∀ {b}, Private {s}.data.regs.rsp.toBitVec {b} → ¬ Covered ({objs}) {b})"] else []) ++
    p.belowConj b s!"{s}.data.regs.rsp.toBitVec" s!"({objs})" ++
    (if p.room == 0 then [] else [s!"SysV.StackRoom {policy} {s} {p.room}"]) ++ stackConj policy s sh.call
  let binders := (p.params.map binderText) ++ ["(frame : Heap)"] ++ sh.form.modelBinderTexts ++
    (if hasPol then ["(pol : CpuPolicy)"] else [])
  let pat := sh.form.pat
  let frameClause (h : String) : String :=
    p.frameClause b s!"({h})" s!"{s}.data.regs.rsp.toBitVec" s!"{t}.data.dmem" s!"{s}.data.dmem"
  let rax := s!"{t}.data.regs.rax.toBitVec"
  let rep := s!"rep {policy} {pat} {s} := {conj parts}"
  let returns := s!"returns {pat} {y} := {sh.returnsText y}"
  if sh.l3Form == .post then
    if p.kind != .both then
      throw (.unsupported 0 "a post-based L3 model needs a value and heap result")
    let post := s!"post {pat} _ {s} {t} := SysV.Exit {s} {t} ∧ " ++
      s!"{sh.post.s} pol {p.val.field rax} {t}.data.dmem ∧ {frameClause objs}"
    return s!"def l3 {" ".intercalate binders} : Model {modelTy sh} Unit where\n  {rep}\n  {returns}\n  {post}"
  match p.kind with
  | .both =>
    let post := s!"post {pat} {y} {s} {t} := SysV.Exit {s} {t} ∧ {resultValueRel p.val sh rax y} ∧ " ++
      s!"{sh.post.s} pol {p.val.field rax} {t}.data.dmem ∧ {frameClause objs}"
    pure (s!"def l3 {" ".intercalate binders} := show Model {modelTy sh} _ from\n" ++
      s!"  \{ {rep}\n    {returns}\n    {post} }")
  | .heap =>
    let ty ← heapResultType sh
    let out ← heapResultExpr p sh y
    let post := s!"post {pat} {y} {s} {t} := SysV.Exit {s} {t} ∧ ({out}).Holds pol {t}.data.dmem ∧ " ++ frameClause objs
    pure s!"def l3 {" ".intercalate binders} : Model {modelTy sh} {ty} where\n  {rep}\n  {returns}\n  {post}"
  | .value =>
    -- the bytes outside the stack room are those of the entry state, as the frame clause of `Fn.Return` says (L3-U5)
    let mem := if p.room == 0 then s!"{t}.data.dmem = {s}.data.dmem" else s!"SysV.Outside {s} {p.room} {t}.data.dmem"
    let post := s!"post _ {y} {s} {t} := SysV.Exit {s} {t} ∧ {mem} ∧ {resultValueRel p.val sh rax y false}"
    pure s!"def l3 {" ".intercalate binders} : Model {modelTy sh} {resultValueTy p.val sh} where\n  {rep}\n  {returns}\n  {post}"

/-- The `by` proof of the fixture helper `nodes` of `Lift/Toys/Fixtures/WalkL2p.lean` equals the statement's `nodes` mapped by
`toObj`. Only the test `genupperrel` uses it. -/
def walkNodesProof : String :=
  "by\n  induction vs generalizing ps with\n  | nil => cases ps <;> rfl\n  | cons v vs ih =>\n    cases ps with\n    | nil => rfl\n    | cons p ps =>\n      rw [nodes, WalkStatement.nodes, List.map_cons, ih]\n      congr 1\n      cases ps <;> rfl"

/-- The L3 function `resultRun` of a statement whose `post` gives the result as a term (`StmtShape.byResult`, L2-NORUN): the
result term of the inputs, for a value; the pair of the term and `()` for both, since the statement's `post` in `l3.post` states
the memory and `y.1` is the value. A heap result has no value term: an error. Any other shape has no declaration. -/
def resultRunText (sh : StmtShape) (p : UpperPlan) : Except GenError (List String) :=
  match sh.byResult, sh.result, p.kind with
  | true, some r, .value => .ok [s!"def {resultRun} {" ".intercalate sh.form.binderTexts} := some ({r.s})"]
  | true, some r, .both => .ok [s!"def {resultRun} {" ".intercalate sh.form.binderTexts} := some (({r.s}), ())"]
  | true, _, _ => .error (.unsupported 0 "a result term with a heap result: the heap result has no value for the term")
  | false, _, _ => .ok []

/-- The relation texts of a function (sections 4.4 and 4.5, path B), for the target `t`, the statement shape `sh` and the plan
`p`: `objsP`, then `heapOf` for a heap result, then `SimIn`, `SimSt`, `SimOut` for a result with a heap, `SimArr` and `l3`, each
after the ones it names. -/
def upperRelText (t : Target) (sh : StmtShape) (p : UpperPlan) : Except GenError String := do
  checkNames sh p
  let _ ← sh.runConst
  let arr ← simArrText p sh
  let l3 ← l3Text t p sh
  -- `heapOf` of a both result (L3-U7): the new contents of a loop are one input (`y.2` has the type of the input)
  let bothLoop := p.kind == .both && !p.heads.isEmpty && (match sh.form with | .one _ => true | .flat _ => false)
  let heapOfDecl := match sh.form with
    | .one bi => if p.kind == .heap || bothLoop then [heapOfText p sh bi] else []
    | .flat _ => []
  let outHeapDecl ← if p.kind == .heap then outHeapText p sh else pure []
  let decls := (← resultRunText sh p) ++ [objsText p sh] ++ heapOfDecl ++ outHeapDecl ++ [upperSimText p, arr, l3]
  pure ("\n\n".intercalate decls)

end Skel.Gen
