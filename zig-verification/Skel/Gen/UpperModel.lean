import Skel.Gen.UpperPlan
import Skel.Gen.Model
import Skel.Gen.Frame

/-! The text of the L2⁺ model: `In2p`, `initP`, `blocksP`, `postP` and `l2p` (`docs/one-way-lift-g3-plan-20261118.md`,
sections 4.2 to 4.4; task G3-07). The text is a function of the target (the code range and the entry PC), the summary (the
blocks) and the plan (the fields, the result kind, the memory). The plan and the summary must agree on the registers and the
memory.

The initialized private byte state is separate from the typed heap. A plan that needs spills across blocks uses `StP`,
which extends `St` with `PrivateStack`. It starts empty. Stores initialize bytes, and loads stop at an absent byte. The
state relation equates each initialized byte with the L2 memory at its signed offset from the entry stack pointer. A call
keeps the caller's private byte state; the callee has its own state and the call obligations establish memory preservation.

Other plans retain fixed stack forwarding: a load uses the latest word stored in the same block or the register saved by
entry. The plan uses byte state for narrow accesses and overwritten entry saves. Unused full-word stores need no byte state.
Stack arguments above the return word are separate input fields. With memory, each argument byte comes from the current
heap when it is covered, and otherwise from the entry field. The input keeps the entry stack pointer. A call passes its
stack pointer and the words from its argument stores.

The room is in `l2p.rep` (`SysV.StackRoom policy s <room>`), and `postP` preserves bytes outside the room. With memory in the
state, the frame clause excludes the room and `l2p.rep` states that no heap object meets it. Unknown stack addresses, stores
at or above the return word, and traps within branches have named errors. Missing deterministic proof text leaves the rows
for the prover rung.

Decisions (the fixtures of section 2 decide them):
* the register updates of a block are in the order of its register list, and the memory update is last (`FindL2p`,
  `WalkL2p`, `FillL2p`); the G1 text of `blocks` reverses the list instead (`Model.lean`, `updates`);
* the heap after the store `k` of a block is `h` for `k = 0` and `h<k>` otherwise (the loads are `v`, `v<k>`);
* `initP` has the form of the G1 `init`, and it always has the name `initP` (decision 4);
* the heap operations are those of the call form of the statement (`heapOps`, D40): `loadB` and `storeB` for `Fn.CallB`, whose
  `l2p.rep` also has the byte-range permission of the heap. -/

namespace Skel.Gen

/-- The names of the two heap operations of `blocksP` for the call form of the statement (D40): `load` and `store` of `Heap`
for `Fn.Call`, the byte fallback `loadB` and `storeB` for `Fn.CallB`. `loadB` and `storeB` give the results of `load` and
`store` where a cell of the width is at the address (`Heap.loadB_of_load`, `Heap.storeB_of_store`). -/
def heapOps (call : CallForm) : String × String :=
  if call.bytePermits then ("loadB", "storeB") else ("load", "store")

/-- The text of `n` spaces. -/
private def indent (n : Nat) : String := "".pushn ' ' n

/-- The plan and the summary agree on the inputs, the memory, the state registers and the stack room (the plan is made from the
summary). -/
private def checkAgree (s : Summary) (p : UpperPlan) : Except GenError Unit :=
  if p.inputs == s.vars.inputs && p.mem == s.vars.mem && p.state.map (·.1) == s.vars.state then
    if p.room != s.frame.room then .error (.shape 0 s!"the plan has a stack room of {p.room} bytes, the summary {s.frame.room}")
    else .ok ()
  else .error (.shape 0 "the plan and the summary differ in the inputs, the memory or the state")

/-- The result type of `blocksP` and of `l2p` (4.4): `UInt64` for a value, `Heap` for a heap, the pair for both. -/
private def resultTy : ResultKind → String
  | .value => "UInt64"
  | .heap => "Heap"
  | .both => "(UInt64 × Heap)"

/-- `In2p` (4.2): the policy iff the result has a heap, the heap, then the inputs in the order of `Reg64`. -/
private def in2pText (p : UpperPlan) : String :=
  "structure In2p where\n" ++ "\n".intercalate
    ((if p.kind.hasPolicy then ["  policy : CpuPolicy"] else []) ++ ["  heap : Heap"] ++
      p.inputs.map (fun r => s!"  {regLower r} : UInt64") ++
      (List.range p.stackArgs).map (fun k => s!"  {stkName k} : UInt64") ++
      (if p.mem then ["  sp : BitVec 64 := 0"] else []))

/-- The private byte state is separate from the typed heap. -/
private def privateStateText (p : UpperPlan) : List String :=
  if p.privateStack then
    [s!"structure StP extends {if p.mem then "St In2p Heap" else "St In2p"} where\n  stack : Lift.Sem.PrivateStack"]
  else []

/-- `initP` (4.2, decision 4): a state field is its input when it is an input, else `0`; the memory is the heap of the input.
The form is that of the G1 `init`: polymorphic when no field is an input and the state has no memory. -/
private def initPText (s : Summary) (p : UpperPlan) : String :=
  let vals := p.state.map fun (r, _) => if p.inputs.contains r then s!"a.{regLower r}" else "0"
  let copy := p.mem || p.state.any fun (r, _) => p.inputs.contains r
  if p.privateStack then
    let fields := ["input := a"] ++ (p.state.zip vals).map (fun ((r, _), v) => s!"{regLower r} := {v}") ++
      (stateFlags s.blocks).map (fun f => s!"{f.name} := false") ++
      (if p.mem then ["mem := a.heap"] else []) ++ ["stack := Lift.Sem.PrivateStack.empty"]
    s!"def initP (a : In2p) : StP := \{ {", ".intercalate fields} }"
  else if copy then
    let stTy := if p.mem then "St In2p Heap" else "St In2p"
    let memVal := if p.mem then ["a.heap"] else []
    s!"def initP (a : In2p) : {stTy} := ⟨{", ".intercalate (["a"] ++ vals ++ (stateFlags s.blocks).map (fun _ => "false") ++ memVal)}⟩"
  else "def initP {I : Type} (a : I) : St I := ⟨" ++ ", ".intercalate (["a"] ++ vals ++ (stateFlags s.blocks).map (fun _ => "false")) ++ "⟩"

/-- The context of the block `b`: as the G1 context of a block (`Model.lean`, `stepAt`). -/
private def ctxOf (t : Target) (s : Summary) (b : Block) : Ctx :=
  ⟨s.vars, t.entryPC, b.accesses, (s.frame.delta.lookup b.offset).getD 0⟩

/-- The name of the heap after the store `k` of a block: `h`, then `h<k>` (as `loadName` names the loads). -/
private def heapName (k : Nat) : String := if k == 0 then "h" else s!"h{k}"

/-! ## The stack words (4.3.4) -/

/-- Where the value of a pop comes from: a store of the same block, or the entry value of a register that the entry block saved. -/
inductive StackSrc where
  | pushed (v : Val)
  | saved (r : Reg64)

/-- The error of a stack address that is not `rsp` plus a constant. -/
private def stackErr (b : Block) : GenError :=
  .unsupported b.offset "a stack address that is not rsp plus a constant"

/-- The sources of the pops of the block `b` (the loads of stack words below the return word), by the index of the load, in the
order of the block. A load of the return word or above is not modelled and has no source. The stores and the loads are checked:
a store at or above the return word, an access of other than 8 bytes, and a pop that neither a store of the block nor the
saved registers `slots` give are errors. -/
def stackLoads (slots : List (Int × Reg64)) (c : Ctx) (b : Block) : Except GenError (List (Nat × StackSrc)) := do
  let (out, _) ← b.accesses.foldlM (init := (([] : List (Nat × StackSrc)), ([] : List Access))) fun (out, prior) a => do
    let out' ← match a with
      | .store _ addr w _ =>
        if !addr.usesRsp then pure out
        else match depthOf c.depth addr with
          | none => throw (stackErr b)
          | some d =>
            if d ≤ 0 then throw (.unsupported b.offset "a stack store at or above the return word")
            else if w != .W64 then throw (.unsupported b.offset s!"a stack store of {w.bits / 8} bytes: the stack words have 8 bytes")
            else pure out
      | .load k addr w =>
        if !addr.usesRsp then pure out
        else match depthOf c.depth addr with
          | none => throw (stackErr b)
          | some d =>
            if d ≤ 0 then pure out
            else if w != .W64 then throw (.unsupported b.offset s!"a stack load of {w.bits / 8} bytes: the stack words have 8 bytes")
            else match pushedVal c prior d with
              | some v => pure (out ++ [(k, .pushed v)])
              | none =>
                match slots.find? (·.1 == d) with
                | some (_, r) => pure (out ++ [(k, .saved r)])
                | none =>
                  throw (.unsupported b.offset s!"a stack load of the word at the depth {d} that no store of the block and no register saved by the entry block gives")
    pure (out', prior ++ [a])
  pure out

/-- The `BitVec 64` text of the value of a pop. -/
def srcText (c : Ctx) : StackSrc → String
  | .pushed v => (bvText c v).1
  | .saved r => s!"x.input.{regLower r}.toBitVec"

/-- The current argument bytes, with the entry word for bytes outside the heap. -/
private def stackArgText (p : UpperPlan) (cur : String) (j : Nat) : String :=
  let original := s!"x.input.{stkName j}.toBitVec"
  if p.mem then s!"Lift.Sem.StackArgs.overlay {cur} (x.input.sp + {8 * (j + 1)}) {original}"
  else original

/-- One access at `ind`, then `rest` with the heap after the access. A stack argument reads the current bytes.
A push is dropped, and a pop is a `let` of its source (`fwd`, from `stackLoads`). The return word is not modelled. -/
private def accessText (p : UpperPlan) (c : Ctx) (fwd : List (Nat × StackSrc)) (ind : Nat) (cur : String) (a : Access)
    (rest : Nat → String → Except GenError String) : Except GenError String := do
  let (opLoad, opStore) := heapOps p.call
  match a with
  | .load k addr w =>
    if addr.usesRsp then
      if let some j := stackArg c.depth a then do
        let body ← rest ind cur
        pure s!"{indent ind}let {loadName k} : BitVec 64 := {stackArgText p cur j}\n{body}"
      else match fwd.lookup k with
        | some src => do
          let body ← rest ind cur
          pure s!"{indent ind}let {loadName k} : BitVec 64 := {srcText c src}\n{body}"
        | none => rest ind cur
    else do
      let body ← rest (ind + 2) cur
      pure s!"{indent ind}match {cur}.{opLoad} {paren 1024 (bvText c addr)} {widthText w} with\n{indent ind}| .ok {loadName k} =>\n{body}\n{indent ind}| .stuck why => .stuck why\n{indent ind}| .noFuel => .noFuel"
  | .store k addr w v =>
    if addr.usesRsp then rest ind cur
    else do
      let body ← rest (ind + 2) (heapName k)
      pure s!"{indent ind}match {cur}.{opStore} {paren 1024 (bvText c addr)} {widthText w} {storeValue c w v} with\n{indent ind}| .ok {heapName k} =>\n{body}\n{indent ind}| .stuck why => .stuck why\n{indent ind}| .noFuel => .noFuel"

/-- The updates of the state after the block `b` (4.3.5): each register of the block in the order of its list, without
`rsp`, then the memory when the heap changed. The heap after the last access is `cur`. -/
private def updatesOf (c : Ctx) (b : Block) (cur stack : String) (p : UpperPlan) : List String :=
  b.regs.filterMap (fun (r, v) => if r == .rsp then none else some s!"{regLower r} := {(u64Text c v).1}") ++
    (setFlags b).map (fun (f, cond) => s!"{f.name} := decide ({(propText c cond).1})") ++
    (if p.mem && cur != "x.mem" then [s!"mem := {cur}"] else []) ++
    (if p.privateStack && stack != "x.stack" then [s!"stack := {stack}"] else [])

/-- The value of `.ret` as an operand: in parentheses when it has a space. `u64Text` gives an application such as
`UInt64.ofBitVec v` the precedence of an atom, and a sum has no outer parentheses. -/
private def retOperand (t : String) : String := if t.any (· == ' ') then s!"({t})" else t

/-! ## A call (PIL-CALL4, MULTI-CALLEE2)

A call of a callee with memory, room 0 and a result of a value and a heap: the caller passes its policy, its heap and the
arguments (`<F>.In2p`), and goes on with the heap and the value of the result (`mem := r.2, rax := r.1`), as the L2 model
goes on with the memory and the value. The meaning of the call is the callee's `l2p.returns` up to one permutation of the
heap (`CallFrame.PermLift`, L3-U6a). A callee with memory and a stack room is an error: its pushes are below the room of the
caller, so the frame clauses of the caller do not hold after the call.

A call of a callee with no memory (a value result): the caller passes its heap and the arguments, and goes on with its heap
and the value (`rax := r`), as the L2 model goes on with its memory. The meaning of the call is the callee's `l2p.returns`.

One callee has the callee type `Unit`. Two or more callees have the callee type `Cal` of the L2 model (MULTI-CALLEE, the
constructor `c<i>` for the callee `i` of `calledOf`) and the families `CalP.In`, `CalP.Out`, `CalP.rel`. -/

/-- The callees of the calls of the summary at L2⁺, in the order of `calledOf` (the order of `Cal`). A callee that the target
does not have, a callee with memory and a stack room, are errors. -/
def upperCallees (t : Target) (s : Summary) : Except GenError (List Callee) :=
  (calledOf s.blocks).mapM fun f => do
    let some c := t.callees.find? (·.name == f) | throw (.unsupported 0 s!"a call at L2+ of {f}: the target has no callee {f}")
    pure c

/-- The callees with memory of the calls of the summary at L2⁺ (`upperCallees`). -/
def memCallees (t : Target) (s : Summary) : Except GenError (List Callee) := do
  pure ((← upperCallees t s).filter (·.heapWrites))

/-- The L2⁺ input type of the callee `c`. -/
def calleeIn (c : Callee) : String := s!"{c.model}.In2p"

/-- The L2⁺ result type of the callee `c`: a value and a heap with memory, else a value. -/
def calleeOutP (c : Callee) : String := if c.heapWrites then "UInt64 × Heap" else "UInt64"

/-- The meaning of the call of `c` at L2⁺, a function of the input and the result: with memory its `l2p.returns` up to one
permutation of the heap, else its `l2p.returns`. -/
def calleeRelOf (c : Callee) : String :=
  if c.heapWrites then
    s!"(fun (x : {calleeIn c}) (r : UInt64 × Heap) => Lift.Sem.CallFrame.PermLift (fun k k' => {c.model}.l2p.returns \{ x with heap := k } (r.1, k')) x.heap r.2)"
  else s!"(fun (x : {calleeIn c}) (r : UInt64) => {c.model}.l2p.returns x r)"

/-- The arms `| .c<i> => <term c>` of a family over `Cal`. -/
def calArms (cs : List Callee) (term : Callee → String) : String :=
  String.join (cs.zipIdx.map fun (c, i) => s!"\n  | .c{i} => {term c}")

/-- The type arguments of `Blocks` for the callees `cs`. -/
def calleeTypes (cs : List Callee) : String :=
  match cs with
  | [c] => s!"Unit (fun _ => {calleeIn c}) (fun _ => {calleeOutP c})"
  | _ => "Cal CalP.In CalP.Out"

/-- The meaning of the calls in `l2p.returns`. -/
def calleeRel (cs : List Callee) : String :=
  match cs with
  | [c] => s!"(fun _ => {calleeRelOf c})"
  | _ => "CalP.rel"

/-- The families of the callees at L2⁺ for two or more callees: `CalP.In`, `CalP.Out`, `CalP.rel`. -/
def calPText (cs : List Callee) : List String :=
  match cs with
  | [] | [_] => []
  | _ =>
    [s!"def CalP.In : Cal → Type{calArms cs calleeIn}", s!"def CalP.Out : Cal → Type{calArms cs calleeOutP}",
     s!"def CalP.rel : (c : Cal) → CalP.In c → CalP.Out c → Prop{calArms cs calleeRelOf}"]

/-- The value of the callee type for the callee `f` of the callees `cs`: `()` for one callee, else `.c<i>`. -/
def calleeIxP (cs : List Callee) (f : String) : String :=
  match cs with
  | [_] => "()"
  | _ => s!".c{(cs.map (·.name)).idxOf f}"

/-- The register updates of a block that ends in a call: each register of the block in the order of its list, without `rsp`
and `rax` (the result of the call sets `rax`). -/
def callUpdates (b : Block) : List (Reg64 × Val) :=
  b.regs.filter fun (r, _) => r != .rsp && r != .rax

/-- The `Next` of the exit `e` of the block `b`, from the heap `cur` after its accesses (4.3.5). -/
private def nextText (cal : List Callee) (s : Summary) (p : UpperPlan) (c : Ctx) (b : Block) (cur stack : String) :
    Exit → Except GenError String
  | .goto n => pure s!".goto .{lblOf s n} {stateAfter (updatesOf c b cur stack p)}"
  | .ret => pure (match p.kind with
    | .value => s!".ret {retOperand (u64Text c (endVal b .rax)).1}"
    | .heap => s!".ret {cur}"
    | .both => s!".ret ({(u64Text c (endVal b .rax)).1}, {cur})")
  | .trap => pure ".stuck \"trap\""
  | .call f cont => do
    let some cl := cal.find? (·.name == f) | throw (.unsupported b.offset s!"a call of {f} at L2+ with no callee")
    if !p.mem then throw (.unsupported b.offset "a call at L2+ with no memory in the state")
    if !p.state.any (·.1 == .rax) then throw (.unsupported b.offset "a call at L2+: rax is not a field of the state")
    let stackArgs ← (List.range cl.stackArgs).mapM fun k =>
      match argStore b k with
      | some v => pure s!"UInt64.ofBitVec {paren 1024 (bvText c v)}"
      | none => throw (.unsupported b.offset s!"the call to {f} has no store for stack argument {k}")
    let args := cl.inputs.map (fun r => (u64Text c (endVal b r)).1) ++ stackArgs ++
      (if cl.mem then [(bvText c (endVal b .rsp)).1] else [])
    let regs := (callUpdates b).map (fun (r, v) => s!"{regLower r} := {(u64Text c v).1}") ++
      (setFlags b).map (fun (f, cond) => s!"{f.name} := decide ({(propText c cond).1})") ++
      (if p.privateStack && stack != "x.stack" then [s!"stack := {stack}"] else [])
    if cl.heapWrites then
      let upd := regs ++ ["mem := r.2", "rax := r.1"]
      pure s!".call {calleeIxP cal f} ⟨{", ".intercalate (["x.input.policy", cur] ++ args)}⟩ fun r => (.{lblOf s cont}, {stateAfter upd})"
    else
      let upd := regs ++ (if cur != "x.mem" then [s!"mem := {cur}"] else []) ++ ["rax := r"]
      pure s!".call {calleeIxP cal f} ⟨{", ".intercalate ([cur] ++ args)}⟩ fun r => (.{lblOf s cont}, {stateAfter upd})"

/-- The `Next` of an arm of a branch. A trap is an error there: `Next` has no `stuck`. -/
private def branchNext (cal : List Callee) (s : Summary) (p : UpperPlan) (c : Ctx) (b : Block) (cur stack : String) :
    Exit → Except GenError String
  | .trap => throw (.unsupported b.offset "a trap in a branch at L2+ (the type Next has no stuck)")
  | e => nextText cal s p c b cur stack e

/-- The term of the block `b` at the indent `ind`, after its accesses, from the heap `cur` (4.3.5). -/
private def termText (cal : List Callee) (s : Summary) (p : UpperPlan) (c : Ctx) (b : Block) (ind : Nat) (cur stack : String) :
    Term → Except GenError String
  | .exit .trap => pure s!"{indent ind}.stuck \"trap\""
  | .exit e => do
    let next ← nextText cal s p c b cur stack e
    pure s!"{indent ind}.ok ({next})"
  | .branch cond y n => do
    let yes ← branchNext cal s p c b cur stack y
    let no ← branchNext cal s p c b cur stack n
    pure s!"{indent ind}.ok (if {(propText c cond).1} then {yes} else {no})"

/-- An initialized private stack access. The byte offset is relative to the entry stack pointer. -/
private def privateAccessText (p : UpperPlan) (c : Ctx) (b : Block) (ind : Nat) (cur stack : String) (a : Access)
    (rest : Nat → String → Except GenError String) : Except GenError String := do
  let addr := match a with | .load _ addr _ | .store _ addr _ _ => addr
  let some d := depthOf c.depth addr | throw (stackErr b)
  match a with
  | .load k _ w =>
    if let some j := stackArg c.depth a then
      let body ← rest ind stack
      pure s!"{indent ind}let {loadName k} : BitVec 64 := {stackArgText p cur j}\n{body}"
    else if d ≤ 0 then rest ind stack
    else
      let body ← rest (ind + 2) stack
      pure (s!"{indent ind}match Lift.Sem.PrivateStack.load {stack} {widthText w} ({-d}) with\n" ++
        s!"{indent ind}| .ok {loadName k} =>\n{body}\n" ++
        s!"{indent ind}| .stuck why => .stuck why\n{indent ind}| .noFuel => .noFuel")
  | .store k _ w v =>
    if d ≤ 0 then throw (.unsupported b.offset "a stack store at or above the return word")
    let next := s!"stack{k}"
    let body ← rest ind next
    pure s!"{indent ind}let {next} := Lift.Sem.PrivateStack.store {stack} {widthText w} ({-d}) {storeValue c w v}\n{body}"

/-- The accesses of the block `b` in order, carrying the heap and initialized private bytes. -/
private def bodyText (cal : List Callee) (s : Summary) (p : UpperPlan) (c : Ctx) (b : Block) (fwd : List (Nat × StackSrc)) :
    List Access → Nat → String → String → Except GenError String
  | [], ind, cur, stack => termText cal s p c b ind cur stack b.term
  | a :: rest, ind, cur, stack =>
    let addr := match a with | .load _ addr _ | .store _ addr _ _ => addr
    if p.privateStack && addr.usesRsp then
      privateAccessText p c b ind cur stack a (fun ind' stack' => bodyText cal s p c b fwd rest ind' cur stack')
    else accessText p c fwd ind cur a (fun ind' cur' => bodyText cal s p c b fwd rest ind' cur' stack)

/-- The arm of `blocksP` for the block `b` (4.3): the accesses, then the term. The heap before the first access is the memory
of the state, or the heap of the input when the state has no memory. The layout is that of the hand text of `toySum`. -/
private def armText (cal : List Callee) (t : Target) (s : Summary) (p : UpperPlan) (b : Block) : Except GenError String := do
  let start := if p.mem then "x.mem" else "x.input.heap"
  let c := ctxOf t s b
  let fwd ← if p.privateStack then pure [] else stackLoads (entrySlots s) c b
  let body ← bodyText cal s p c b fwd b.accesses 6 start "x.stack"
  pure s!"    | .{b.name.s}, x =>\n{body}"

/-- `blocksP` (4.3): a `Leaf` over `St In2p`, or over `St In2p Heap` with the memory, with one arm for each block. -/
def blocksPText (t : Target) (s : Summary) (p : UpperPlan) : Except GenError String := do
  let res := resultTy p.kind
  let stTy := p.stateType
  let cal ← upperCallees t s
  let arms ← s.blocks.mapM (armText cal t s p)
  let steps := if s.blocks.isEmpty then "    | .entry, _ => .stuck \"no block\"" else "\n".intercalate arms
  let ty := if cal.isEmpty then s!"Leaf Lbl ({stTy}) {res}" else s!"Blocks Lbl ({stTy}) {res} {calleeTypes cal}"
  pure s!"def blocksP : {ty} where\n  step\n{steps}"

/-- `postP` (4.4): the return of a value, of a heap that the memory holds (with the policy of the input), or of both. -/
private def postPText (p : UpperPlan) : String :=
  let frame := p.frameClause "b" "a.heap" "s.data.regs.rsp.toBitVec" "t.data.dmem" "s.data.dmem"
  match p.kind with
  | .value =>
    -- the bytes outside the room are those of the entry state (`Fn.Return.frame`); at room 0 the memory does not change
    let mem := if p.room == 0 then "t.data.dmem = s.data.dmem" else s!"SysV.Outside s {p.room} t.data.dmem"
    s!"def postP \{A : Type} (_ : A) (r : UInt64) (s t : MachineState) : Prop :=\n  SysV.Exit s t ∧ {mem} ∧ t.data.regs.rax = r"
  | .heap => s!"def postP (a : In2p) (r : Heap) (s t : MachineState) : Prop :=\n  SysV.Exit s t ∧ r.Holds a.policy t.data.dmem ∧ {frame}"
  | .both => s!"def postP (a : In2p) (r : UInt64 × Heap) (s t : MachineState) : Prop :=\n  SysV.Exit s t ∧ t.data.regs.rax = r.1 ∧ r.2.Holds a.policy t.data.dmem ∧ {frame}"

/-- The conjunct of a guarded store (a state with memory, `Frame.lean`): no object of the heap covers the private area, which
is the return word at room 0. The guard `Clear` of the G1 text needs it. -/
private def areaConj (p : UpperPlan) : List String :=
  (if p.mem then ["(∀ b, Private s.data.regs.rsp.toBitVec b → ¬ Covered a.heap b)"] else []) ++
  -- PIL-HEAP: no object meets the room, so the heap holds in the L2 input memory `SysV.hide` (`Fn.Entry.apart`); U5b: the pushes
  -- of a state with memory write the room
  p.belowConj "b" "s.data.regs.rsp.toBitVec" "a.heap"

/-- `l2p` (4.4): the policy iff the result has a heap, the heap holds, the byte-range permission of the heap for `Fn.CallB`
(D40), the entry, each input register, and the area conjunct. -/
private def l2pText (t : Target) (p : UpperPlan) (res : String) (cal : List Callee) : String :=
  let conj := (if p.kind.hasPolicy then ["a.policy = policy"] else []) ++
    ["a.heap.Holds policy s.data.dmem"] ++ p.call.permitsConj "a.heap" "policy" ++
    [s!"SysV.Entry policy {t.lo} {t.hi} {t.entryPC} s"] ++
    p.inputs.map (fun r => s!"s.data.regs.{regLower r} = a.{regLower r}") ++
    (List.range p.stackArgs).map (stkConj "a") ++ areaConj p ++
    (if p.room == 0 then [] else [s!"SysV.StackRoom policy s {p.room}"]) ++
    (if p.mem then ["a.sp = s.data.regs.rsp.toBitVec"] else [])
  let callee := if cal.isEmpty then "noCall" else calleeRel cal
  s!"def l2p : Model In2p {res} where\n  rep policy a s := {" ∧ ".intercalate conj}\n  returns a r := blocksP.Returns {callee} .entry (initP a) r\n  post := postP"

/-- The L2⁺ model text of the function `s`, for the target `t` and the plan `p` (sections 4.2 to 4.4): the declarations
`In2p`, `initP`, `blocksP`, `postP` and `l2p`, in this order. -/
def upperModelText (t : Target) (s : Summary) (p : UpperPlan) : Except GenError String := do
  checkAgree s p
  let blocks ← blocksPText t s p
  let cal ← upperCallees t s
  pure ("\n\n".intercalate ([in2pText p] ++ privateStateText p ++ [initPText s p] ++ calPText cal ++ [blocks, postPText p, l2pText t p (resultTy p.kind) cal]) ++ "\n")

end Skel.Gen
