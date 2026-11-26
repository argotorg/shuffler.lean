import Skel.Gen.UpperPlan
import Skel.Gen.Hint
import Skel.Gen.Shape
import Skel.Gen.UpperRel
import Skel.Toy.RefuteCommon
import Skel.Lean.Admission

/-! The `RefuteSpec` of a function, generated from its plan (`UpperPlan`), its hint record and its statement shape
(`docs/one-way-lift-g3-plan-20261118.md`, section 5, task G3-12b). The refute file of a function reads its samplers from
this value (5.7). The generator is pure: `refuteSpec` gives the value, and `specLiteral` the text of the value.

The samplers draw with the library `Skel.Lean.Sample` (G3-12a). Two families (5.1, step 2): an array of words behind an
address binder (the hint gives `ptr .seq` of 64-bit words), and a chain of nodes behind a list binder (`ptr .one` to a
record: its size, the offset of `next` and the offset of the value cell come from the record of the hint, `Node`). Other
plans give `GenError.shape`.

Decisions of this file:
- the ghost is the L3 result `y` of the statement (a word, or the list of words of a heap result): the statement binds `y`
  with `run input = some y`, and a triple may use it. `y` is `(run input).getD _` of the input that the sampler drew, so that
  the refuter and the check give the names the same meaning (DS-FIX). Every other logical value of the four toys (the list,
  the key, the chain) is a function of the input `x.input` of the state, which is constant during a run (D35);
- the L3 input is one input of the statement (a list of words, or a record with one list field and scalar fields), or several
  (`InputForm.flat`): exactly one list of words and any number of words, as separate variables (`vals`, `key`). The scalars
  are drawn as the scalar fields of a record, and the argument that is the name of a scalar gives its register;
- the claim fuel is `(blocks on the cycle) × size + 8`. The head carries the blocks of the cycle (`Head.cycle`); its fuel
  is `6 × blocks + 8` (`Head.fuel`, 5.3);
- the names of the L2⁺ model (`ModelSpec`), the name of the namespace of the file and the extra opens come from the caller;
- a plan with no loop head, or with two, is an error (`GenError.shape`): the sampler draws the input of one loop;
- the result of the loop has one of four forms (`ResultForm`): a word (a value of 64 bits), a narrow value (the register that the
  loop returns holds the L3 value in its low bits: the spec has a projection `proj` that keeps the low bits, and the expected
  result is the word of the L3 value), a heap, and both (L3-U7: the pair of the narrow or word value and the heap of the array,
  as the heap form makes it from the second component of `run`; the array family with a state that has the memory);
- an array is writable when the state has the memory (`mem`): the plan has a memory only when the function writes it;
- the generated samplers import `Lift.Sem.HeapFast` (the fast heap functions, one definition `heapImport`). -/

namespace Skel.Gen

open Skel.Toy.RefuteCommon (RefuteSpec)

/-- The model that a refute file of the function needs, from the caller: the declarations of the L2⁺ model text (in the order
of `RefuteSpec.modelNames`), the modules that the model imports, the name `fn` of the namespace of the file (`Find`), and the
namespaces that the model text needs open besides those of the generator (`opens`). -/
structure ModelSpec where
  (names imports : List String)
  (fn : String)
  (opens : List String)

/-- The registers that carry the arguments of a call, in order: the C ABI (`argRegs` of `Lift/Trusted/Call.lean`). -/
def argOrder : List Reg64 := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- The module of the fast heap functions (`@[csimp]`, `Lift/Sem/HeapFast.lean`). The generated samplers import it, so the
compiled `Heap.load` and `Heap.store` are the fast ones. One definition: a change of the module is one line. -/
private def heapImport : String := "Lift.Sem.HeapFast"

/-! ## The statement: the L3 input and the arguments -/

private def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- The identifier that follows each occurrence of `inp ++ "."` in `t`, when the occurrence is not part of a longer name. -/
private def fieldsIn (inp t : String) : List String :=
  let parts := t.splitOn (inp ++ ".")
  (parts.zip parts.tail).filterMap fun (before, after) =>
    let free := match before.toList.getLast? with
      | some c => !(isIdChar c || c == '.')
      | none => true
    let name := String.mk (after.toList.takeWhile isIdChar)
    if free && !name.isEmpty then some name else none

/-- The shape of the L3 input: the one input `inp` of the type `inTy` that is a list of words, or a structure with one list
field and scalar fields; or several inputs (`inputs`: name and type), one of which (`list`) is a list of words, and the
others (the scalars) words. -/
inductive InShape where
  | list (inp inTy : String)
  | record (inp inTy : String) (listField : String) (scalars : List String)
  | flat (inputs : List (String × String)) (list : String)

/-- The scalar inputs of a flat shape: the inputs that are not the list. -/
def InShape.flatScalars (inputs : List (String × String)) (list : String) : List String :=
  (inputs.map (·.1)).filter (· != list)

/-- The shape of the one input `inp` of the type `inTy` from the texts of the arguments: its fields are the names that the
arguments give (`x.xs.length`, `x.key`). A field that is followed by `.length` is the list field. An input that no argument
names a field of is the list itself (`xs.length`, `List.length x`). The statement has no data on the fields of the input type,
so the texts are split. A field that a hypothesis names (`hyps`) of a structure input and that no argument names is an error:
the sampler would not draw it. -/
private def oneShapeOf (inp inTy : String) (args hyps : List String) : Except GenError InShape :=
  let fields := ((args.flatMap (fieldsIn inp)).eraseDups).filter (· != "length")
  if fields.isEmpty then .ok (.list inp inTy) else
  let missing := ((hyps.flatMap (fieldsIn inp)).eraseDups).filter fun f => f != "length" && !fields.contains f
  if !missing.isEmpty then
    .error (.shape 0 s!"the hypotheses name the fields {missing} of {inp}, which no argument names")
  else
  match fields.filter (fun f => args.any fun t => (t.splitOn s!"{inp}.{f}.length").length > 1) with
  | [l] => .ok (.record inp inTy l (fields.filter (· != l)))
  | _ => .error (.shape 0 s!"the fields {fields} of {inp} have no single list field")

/-- The text of a type without the spaces at its ends. -/
private def tyText (b : ShapeBinder) : String := b.type.s.trimAscii.toString

/-- The shape of several inputs: each input is a list of words (`List (BitVec 64)`) or a word (`BitVec 64`), and one is a
list. Another type is an error that names the input. -/
private def flatShapeOf (bs : List ShapeBinder) : Except GenError InShape := do
  if let some b := bs.find? fun b => tyText b != "List (BitVec 64)" && tyText b != "BitVec 64" then
    throw (.shape 0 s!"the input {b.name.s} has the type {b.type.s}: the sampler draws a list of words and words")
  match bs.filter fun b => tyText b == "List (BitVec 64)" with
  | [l] => pure (.flat (bs.map fun b => (b.name.s, tyText b)) l.name.s)
  | [] => throw (.shape 0 "no input is a list of words: the sampler draws one list")
  | ls => throw (.shape 0 s!"{ls.length} inputs are lists of words: the sampler draws one list")

/-- The shape of the L3 input of the statement `sh` (see `oneShapeOf` and `flatShapeOf`). -/
def inShapeOf (sh : StmtShape) : Except GenError InShape :=
  match sh.form with
  | .one b => oneShapeOf b.name.s b.type.s (sh.args.map (·.term.s)) (sh.hyps.map (·.s))
  | .flat bs => flatShapeOf bs

/-- The layout of a node of a chain, in bytes (read from the record of the hint, `nodeOf`): the size of the node, the offset
of the value cell, and the offset of the pointer to the next node. -/
structure Node where
  (size val next : Nat)

/-- The family of the samplers (5.1, step 2). -/
inductive Family where
  | array
  | chain (node : Node)

/-- The pointer parameter of the hint: the first parameter with a pointer type, with its target and its element type. -/
private def pointerOf (h : HintRecord) : Except GenError (HParam × PtrTarget × Nat) :=
  let found := h.params.findSome? fun q =>
    match h.types[q.ty]? with
    | some (HTy.ptr t to _ _) => some (q, t, to)
    | _ => none
  match found with
  | some r => .ok r
  | none => .error (.shape 0 "the hint has no pointer parameter")

/-- The one loop head of the plan: the sampler draws the input of one loop (4.6). -/
private def singleHead (p : UpperPlan) : Except GenError Head :=
  match p.heads with
  | [hd] =>
    if hd.generalized then .error (.shape 0 s!"{p.fn}: the head {hd.name.s} has generalized state")
    else if hd.state.any (·.2 == .carried) then .error (.shape 0 s!"{p.fn}: the head {hd.name.s} has a carried value")
    else .ok hd
  | [] => .error (.shape 0 s!"{p.fn} has no loop head")
  | _ => .error (.shape 0 s!"{p.fn} has {p.heads.length} loop heads, the sampler draws one loop")

/-- The layout of the node that the pointer type at the index `to` addresses (D37). The record has a size that is a multiple of
8. The pointer to the next node is the field whose type is a pointer to the record itself: the only one, or, when there are
several, the one at the offset of `Count.chain`. The value cell is the first field that is a 64-bit integer. The offsets of
both are multiples of 8 and inside the record. -/
private def nodeOf (fn : String) (h : HintRecord) (to : Nat) (count : Count) : Except GenError Node := do
  let bad (why : String) : GenError := .shape 0 s!"{fn}: the node record of the hint {why}"
  let some (.record _ size fields _) := h.types[to]? | throw (bad "is no record")
  let selfs := fields.filterMap fun (_, off, t) =>
    match h.types[t]? with
    | some (.ptr .one q _ _) => if q == to then some off else none
    | _ => none
  let next ← match count, selfs with
    | .chain off, _ => if selfs.contains off then pure off else throw (bad s!"has no pointer to the node at {off}")
    | _, [off] => pure off
    | _, _ => throw (bad s!"has {selfs.length} pointers to the node and no count that picks one")
  let words : List Nat := fields.filterMap fun (_, off, t) =>
    match h.types[t]? with
    | some (.int 64 _) => some off
    | _ => none
  let some val := words.min? | throw (bad "has no 64-bit integer field")
  unless size % 8 == 0 && val % 8 == 0 && next % 8 == 0 && val + 8 ≤ size && next + 8 ≤ size do
    throw (bad s!"has size {size}, value at {val}, next at {next}: not words inside the node")
  pure { size, val, next }

/-- The family of the samplers: the binder of the plan and the element of the hint (D37). An array is a `[*]u64` pointer
(`ptr .seq` of 64 bits) with one address binder. A chain is a `ptr .one` to a record (`nodeOf`) with one list binder. Any
other pair is an error. -/
private def familyOf (p : UpperPlan) (h : HintRecord) : Except GenError Family := do
  let (q, t, to) ← pointerOf h
  match t, h.types[to]?, p.params with
  | .seq, some (.int 64 _), [⟨_, .addr⟩] => pure .array
  | .one, some (.record ..), [⟨_, .addrs⟩] => pure (.chain (← nodeOf p.fn h to q.count))
  | _, _, _ => throw (GenError.shape 0 s!"{p.fn}: the hint and the binders give no array of words and no chain of nodes")

/-- The register of the pointer of the hint: the first register of its parameter. -/
private def ptrRegOf (h : HintRecord) : Except GenError Reg64 := do
  let (q, _, _) ← pointerOf h
  match q.regs with
  | r :: _ => pure r
  | [] => throw (GenError.shape 0 s!"the pointer parameter {q.name} has no register")

/-- The form of the result of the loop (L3-U7): a word (a value of 64 bits, the register is the value), a narrow value (the
register holds the value in its low bits), a heap, or both (the pair of the value and the heap). -/
inductive ResultForm where
  | word | narrow | heap | both
  deriving DecidableEq

/-- The L3 value `e` of a narrow or both result as a word (`UInt64`): the register that holds it in its low bits, with zero above
(L3-U7). A 64-bit value is `UInt64.ofBitVec`, a narrower `BitVec` is its number, and a `Bool` is 0 or 1. -/
def ValueTy.word (v : ValueTy) (e : String) : String :=
  match v with
  | .bool => s!"(if {e} then 1 else 0 : UInt64)"
  | .bits .W64 => s!"UInt64.ofBitVec ({e})"
  | .bits _ => s!"UInt64.ofNat ({e}).toNat"

/-- The value that stands for a missing result in `getD`: `false` for a `Bool`, else `0`. -/
def ValueTy.dflt : ValueTy → String
  | .bool => "false"
  | .bits _ => "0"

/-- The mask of the low bits of the result: `65535` for 16 bits. -/
def ValueTy.mask (v : ValueTy) : String :=
  let bits := v.width.bits
  if bits == 64 then "0xFFFFFFFFFFFFFFFF" else s!"{2 ^ bits - 1}"

/-- The projection of the results of the loop for the plan `p` (`RefuteSpec.proj`): none for a result in the whole register, the
low bits of the register for a narrow value, and the low bits of its first component for both. -/
def projText (p : UpperPlan) : String :=
  match p.kind with
  | .value => if p.val.isWord then "" else s!"(fun (r : UInt64) => r &&& {p.val.mask})"
  | .heap => ""
  | .both => if p.val.isWord then "" else s!"(fun (r : UInt64 × Heap) => (r.1 &&& {p.val.mask}, r.2))"

/-- The form of the result of the plan `p` with the family `family` (see `ResultForm`). A narrow value is a value with no
memory; a result with both is for an array whose state has the memory, so that the pair holds the array. -/
private def resultFormOf (p : UpperPlan) (family : Family) : Except GenError ResultForm :=
  match p.kind with
  | .value => .ok (if p.val.isWord then .word else .narrow)
  | .heap => .ok .heap
  | .both =>
    match family with
    | .array =>
      if p.mem then .ok .both
      else .error (.unsupported 0 s!"{p.fn}: a result that is a value and a heap has a sampler for a loop that writes the array, and the state has no memory")
    | .chain _ => .error (.unsupported 0 s!"{p.fn}: a result that is a value and a heap has a sampler for an array, not for a chain")

/-! ## The facts of the function -/

/-- The facts of the function that the texts read: the plan, the statement and the hint, as names and registers. -/
private structure Facts where
  fn : String                          -- the namespace of the file: `Find`
  head : Head
  family : Family
  inShape : InShape
  bn : String                          -- the name of the address binder: `p`, or `ps` for a chain
  params : List Binder                 -- the exact statement parameters captured by each claim input
  captureParams : Bool                 -- the run or result expression uses statement parameters in a loop slot
  runCall : String                     -- `run` applied to the input or inputs: `Lift.Toys.FindSpec.run x`
  admission : String                   -- executable contract and binder hypotheses, before the run
  args : List (Reg64 × String)         -- each argument of the call, with its register
  inputs : List Reg64                  -- the registers of `In2p` after `heap` (4.2)
  state : List (Reg64 × FieldClass)    -- the registers of `St`, in order (5.2)
  mem : Bool                           -- `St` has the memory
  form : ResultForm                    -- the form of the result of the loop
  val : ValueTy                        -- the L3 value of a value result and of the first part of both
  policy : Bool                        -- `In2p` has the policy (4.2)
  ptrReg : Reg64                       -- the register of the pointer
  ghosts : List Ghost                  -- the chain offsets of the plan (4.7)
  proj : String                        -- the projection of the results (`projText`), or empty
  runResultType : Option Src
  resultFn : Option Src

/-! ## The text of the samplers -/

private def lineBlock (ls : List String) : String := "\n  ".intercalate ls

/-- Test premises in statement order. An unavailable executable decision makes the refuter unknown. -/
private def admissionTest (sh : StmtShape) : String :=
  (sh.contract.s :: sh.hyps.map (·.s)).foldr
    (fun premise next => s!"if skel_decide% ({premise}) then ({next}) else false") "true"

private def admittedRunTest (admission runCall : String) : String :=
  s!"if ({admission}) then ({runCall}).isSome else false"

/-- A tuple type of the statement parameters. The claim keeps their sampled values even when no register does. -/
private def capturedType (ps : List Binder) : String :=
  match ps with
  | [] => "Unit"
  | _ => " × ".intercalate (ps.map fun p => match p.ty with
      | .addr => "BitVec 64"
      | .addrs => "List (BitVec 64)"
      | .source t => s!"({t.s})")

private def capturedValue (ps : List Binder) : String :=
  match ps with
  | [] => "()"
  | [p] => p.name.s
  | _ => "(" ++ ", ".intercalate (ps.map (·.name.s)) ++ ")"

private def claimInputType (inTy : String) (ps : List Binder) : String :=
  s!"{inTy} × In2p × ({capturedType ps})"

/-- Bind inputs and captured parameters before the copied run and result expressions. Primed helper names cannot
be statement identifiers. Keep the input and state before a statement variable named `x` can hide the claim argument. -/
private def claimScope (input : String) (ps : List Binder) (body : String) : String :=
  lineBlock ["let input' := x.1", "let state' := x.2.1", "let params' := x.2.2",
    s!"let {input} := input'", s!"let {capturedValue ps} := params'", body]

/-- Whether a copied expression names a statement parameter. Identifier boundaries are the same as `renameVar`. -/
private def usesParams (ps : List Binder) (runCall : String) (resultFn : Option Src) : Bool :=
  ps.any fun p => (runCall :: (resultFn.map (·.s)).toList).any fun t => renameVar p.name.s "" t != t

/-- A structure instance `{ f1, f2, ... }` of the fields `fs`, each a `name := value` text. -/
private def structText (fs : List String) : String := "{ " ++ ", ".intercalate fs ++ " }"

private def defText (head : String) (body : List String) : String := head ++ " :=\n  " ++ lineBlock body

/-- The text of the argument of the call that goes in the register `r`, or `0` when no argument does. -/
private def argOf (f : Facts) (r : Reg64) : String :=
  match f.args.find? (·.1 == r) with
  | some (_, t) => t
  | none => "0"

/-- The `let` lines of the L3 input and of the L2⁺ input `a`, drawn from the stream `g` (5.1): the words, the address of the
binder, the frame words, the heap, the L3 input, and `a`. The arguments of the call are the terms of the statement, with
their names bound here. -/
private def inputSetup (f : Facts) : List String × List String :=
  let ws := "let ws : List (BitVec 64) := Skel.Sample.Sample.draw (g.stream 0)"
  let frameWords := ["let before := Skel.Sample.word (g.stream 2)"]
  let scalarLets (l : String) (ss : List String) : List String := (List.range ss.length).map fun i =>
    let name := ss.getD i ""
    s!"let {name} : BitVec 64 := Skel.Sample.memberOr (g.stream {8 + 2 * i}) {l} (Skel.Sample.word (g.stream {9 + 2 * i}))"
  let inLets : List String := match f.inShape with
    | .list inp inTy => [s!"let {inp} : {inTy} := ws"]
    | .record inp inTy l ss =>
      let fields := (l :: ss).map fun n => s!"{n} := {n}"
      [s!"let {l} : List (BitVec 64) := ws"] ++ scalarLets l ss ++ [s!"let {inp} : {inTy} := {structText fields}"]
    | .flat inputs l => [s!"let {l} : List (BitVec 64) := ws"] ++ scalarLets l (InShape.flatScalars inputs l)
  let policyField := if f.policy then ["policy := ⟨fun _ => true⟩"] else []
  let regFields := f.inputs.map fun r => s!"{regName r} := UInt64.ofBitVec ({argOf f r})"
  let inA := s!"let a : In2p := {structText (policyField ++ ["heap := h"] ++ regFields)}"
  let arrayPart :=
    ([ws, s!"let {f.bn} := Skel.Sample.addrOf (g.stream 1)"] ++ frameWords,
      [s!"let h := Skel.Sample.arrayHeap {f.mem} {f.bn} ws before"])
  let chainPart (n : Node) :=
    let cells := (List.range (n.size / 8)).map fun i =>
      if 8 * i == n.next then s!"{f.bn}.getD (k + 1) 0" else if 8 * i == n.val then "ws.getD k 0" else "0"
    ([ws, "let base := Skel.Sample.addrOf (g.stream 1)"] ++ frameWords ++
      [s!"let {f.bn} := (Skel.Sample.slots (g.stream 4) ws.length).map fun s => base + BitVec.ofNat 64 ({n.size} * s)"],
      [s!"let nodes := (List.range ws.length).map fun k => Obj.words ({f.bn}.getD k 0) false .W64 [{", ".intercalate cells}]",
       s!"let h := nodes ++ Skel.Sample.frame base before"])
  let (draws, build) := match f.family with
    | .array => arrayPart
    | .chain n => chainPart n
  (draws ++ inLets, build ++ [inA])

/-- Draw logical inputs first. Construct no heap or ABI argument before admission. -/
private def admittedInputs (f : Facts) (body : List String) : List String :=
  let (draws, build) := inputSetup f
  draws ++ [s!"if !({f.admission}) then none else\n  " ++ lineBlock (build ++ body)]

/-- The pointer list of a sample: the address and `0` for an array, the node addresses and `0` for a chain. -/
private def ptrList (f : Facts) : String :=
  match f.family with
  | .array => s!"[{f.bn}, 0]"
  | .chain _ => s!"({f.bn} ++ [0])"

/-- The value of a state field of a free state (5.2) of the class `c`, drawn from the stream `20 + j`. -/
private def freeVal (f : Facts) (j : Nat) (c : FieldClass) : String :=
  match c with
  | .counter => s!"UInt64.ofNat (Skel.Sample.counter (g.stream {20 + j}) ws.length)"
  | .accumulator => s!"UInt64.ofBitVec (Skel.Sample.word (g.stream {20 + j}))"
  | .pointer => s!"UInt64.ofBitVec ((Skel.Sample.pointer (g.stream {20 + j}) {ptrList f}).getD 0)"

/-- The state of a sampler: the input `a`, the values of the state fields, and the memory when the state has one. -/
private def stateText (f : Facts) (vals : List (Reg64 × String)) (mem : String) : String :=
  structText (["input := a"] ++ vals.map (fun (r, v) => s!"{regName r} := {v}") ++
    (if f.mem then [s!"mem := {mem}"] else []))

/-- The value of a register at a loop head (4.6), over the input `a`: the input register, a literal, a term (`HeadVal.term`;
a head term of entry loads, `headTerm`, has the load form of `.load`), a load of the entry block. -/
def headValText (v : HeadVal) : String :=
  match v with
  | .input s => s!"a.{regName s}"
  | .lit n => s!"UInt64.ofNat {n.toNat}"
  | .term t => s!"({t.replace "x.input." "a."})"
  -- a load of the entry block (PIL-HEAP): the load in the heap of the input, `0` when it fails
  | .load addr w =>
    let v := if w == .W64 then "v" else "(BitVec.zeroExtend 64 v)"
    s!"(match a.heap.load ({addr.replace "x.input." "a."}) {widthText w} with | .ok v => UInt64.ofBitVec {v} | _ => 0)"
  -- a carried value (L2-LOOPS): `singleHead` refuses a head with one, so the sampler draws no such head
  | .carried => "0"

/-- The state type of the samplers: `St In2p`, or `St In2p Heap` when the state has the memory. -/
private def stateTy (f : Facts) : String := "St In2p" ++ (if f.mem then " Heap" else "")

/-- The result type of the samplers and of the claim: `UInt64`, `Heap`, or the pair. -/
private def resultTy (f : Facts) : String :=
  match f.form with
  | .word | .narrow => "UInt64"
  | .heap => "Heap"
  | .both => "(UInt64 × Heap)"

/-- The pair of the value and the new contents that `call` (an `Option`) gives, with the default `(0, [])` for none. -/
private def pairOf (f : Facts) (call : String) : String := s!"({call}.getD ({f.val.dflt}, []))"

/-- The register word of the statement's encoded result projection, or of its direct value. -/
def resultWord (val : ValueTy) (resultFn : Option Src) (y : String) (first : Bool := false) : String :=
  match resultFn with
  | some fn => s!"UInt64.ofNat (((Lift.Trusted.Encode.encode (({fn.s}) ({y}))).headD ⟨.W64, 0⟩).v.toNat)"
  | none => val.word (if first then s!"({y}).1" else y)

/-- A constructor term supplies the unused result of a free sample whose input has no run result. -/
private def resultDefault : String := "(by repeat' (first | exact default | constructor!))"

/-- The result of the loop for the full L3 result `y`. -/
private def expectedOf (f : Facts) (y : String) : String :=
  match f.form with
  | .heap => s!"Obj.words {f.bn} {f.mem} .W64 ({y}) :: h.tail"
  | .word | .narrow => resultWord f.val f.resultFn y
  | .both => s!"({f.val.word s!"({y}).1"}, Obj.words {f.bn} {f.mem} .W64 ({y}).2 :: h.tail)"

/-- The type of the ghost `y` (the L3 result of the statement): a word, a narrow value, the words of a heap result, or the pair. -/
private def yTy (f : Facts) : String :=
  match f.runResultType with
  | some ty => s!"({ty.s})"
  | none =>
    match f.form with
    | .heap => "List (BitVec 64)"
    | .word => "BitVec 64"
    | .narrow => f.val.outTy
    | .both => s!"({f.val.outTy} × List (BitVec 64))"

/-- A loop slot retains exact statement parameters when its copied expressions use them. -/
private def loopGhostTy (f : Facts) : String :=
  if f.captureParams then s!"({yTy f} × ({capturedType f.params}))" else yTy f

private def loopGhost (f : Facts) (y : String) : String :=
  if f.captureParams then s!"({y}, {capturedValue f.params})" else y

/-- The value of the ghost `y` of the input that the sampler drew: the L3 value (`getD` for an input that L3 does not
accept). -/
private def yText (f : Facts) : String :=
  if f.runResultType.isSome then s!"({f.runCall}).getD {resultDefault}" else match f.form with
  | .heap => s!"({f.runCall}).getD []"
  | .word | .narrow => s!"({f.runCall}).getD {f.val.dflt}"
  | .both => pairOf f s!"({f.runCall})"

/-- The sampler of the admitted samples: the head state of the plan, with the input, and the expected result. -/
private def admittedDef (f : Facts) : String :=
  let vals := f.head.state.map fun (r, v) => (r, headValText v)
  let memA := "a.heap"
  defText s!"def refuteAdmitted (g : Rng) : Option ({loopGhostTy f} × {stateTy f} × {resultTy f})"
    (admittedInputs f [s!"match {f.runCall} with\n  | none => none\n  | some y => some ({loopGhost f "y"}, {stateText f vals memA}, {expectedOf f "y"})"])

/-- The sampler of the free states (5.2): each state field by its class, the input of the stream, and the memory. -/
private def freeDef (f : Facts) : String :=
  let vals := (List.range f.state.length).map fun j =>
    let (r, c) := f.state.getD j (f.ptrReg, .accumulator)
    (r, freeVal f j c)
  let mem := s!"Skel.Sample.arrayHeap {f.mem} {f.bn} (Skel.Sample.Sample.draw (g.stream {20 + f.state.length}) : List (BitVec 64)) before"
  defText s!"def refuteFree (g : Rng) : Option ({loopGhostTy f} × {stateTy f})"
    (admittedInputs f [s!"some ({loopGhost f (yText f)}, {stateText f vals mem})"])

/-- The render of a state: the words of the input, and each state field. -/
private def renderDef (f : Facts) : String :=
  let parts := ["\"xs = \" ++ toString (xsOf x.input)"] ++
    f.state.map fun (r, _) => s!"\", {regName r} = \" ++ toString x.{regName r}"
  defText s!"def refuteRender (x : {stateTy f}) : String" [String.intercalate " ++ " parts]

/-- The helpers of the state: the words of the input, read from the pointer of the input. -/
private def helperDecls (f : Facts) : List String :=
  let ptr := s!"a.{regName f.ptrReg}.toBitVec"
  let words := match f.family with
    | .array => s!"wordsOf a.heap {ptr}"
    | .chain _ => s!"chainOf a.heap 64 {ptr}"
  let xsOfDef := s!"def xsOf (a : In2p) : List (BitVec 64) := {words}"
  match f.family with
  | .array =>
    [ "def wordsOf (h : Heap) (p : BitVec 64) : List (BitVec 64) :=\n  match h.find? (fun o => o.addr == p) with\n"
        ++ "  | some o => o.cells.filterMap (fun c => c.get .W64)\n  | none => []",
      xsOfDef ]
  | .chain n =>
    let cell (off : Nat) : String := if off == 0 then "p" else s!"(p + {off})"
    [ "def chainOf (h : Heap) : Nat → BitVec 64 → List (BitVec 64)\n  | 0, _ => []\n"
        ++ s!"  | n + 1, p =>\n    if p = 0 then [] else\n    match h.load {cell n.val} .W64, h.load {cell n.next} .W64 with\n"
        ++ "    | .ok v, .ok q => v :: chainOf h n q\n    | _, _ => []",
      xsOfDef ]

/-- The lets of the slots of a refute file: the input `a`, the words, the scalar fields of the L3 input (from the register of
their argument), and, for a chain, the chain from the register of each ghost (4.7). An array also has the ghosts of its
binder and of the frame (4.7: "each statement binder, and `frame`"): the binder is the pointer register, and the frame is the
tail of the heap (`Skel.Sample.arrayHeap` puts the array first). -/
private def slotLets (f : Facts) : List String :=
  let scalarLets := match f.inShape with
    | .list .. => []
    | .record inp _ _ ss => ss.filterMap fun n =>
      (f.args.find? fun (_, t) => (fieldsIn inp t).contains n).map fun (r, _) => s!"let {n} := a.{regName r}.toBitVec"
    | .flat inputs l => (InShape.flatScalars inputs l).filterMap fun n =>
      (f.args.find? fun (_, t) => t.trimAscii.toString == n).map fun (r, _) => s!"let {n} := a.{regName r}.toBitVec"
  let ghostLets := f.ghosts.map fun g => s!"let rest_{regName g.reg} := chainOf a.heap 64 x.{regName g.reg}.toBitVec"
  let frameLets := (if f.captureParams then [] else [s!"let {f.bn} := a.{regName f.ptrReg}.toBitVec"]) ++
    ["let frame := a.heap.tail"]
  let resultLets := if f.captureParams then
      ["let y := g.1", s!"let {capturedValue f.params} := g.2"] else ["let y := g"]
  let originalWords := if f.captureParams then match f.family with
    | .array => s!"wordsOf a.heap {f.bn}"
    | .chain _ => s!"chainOf a.heap 64 ({f.bn}.headD 0)"
    else "xsOf a"
  resultLets ++ ["let a := x.input", s!"let xs := {originalWords}"] ++ (match f.family with
    | .array => scalarLets ++ frameLets
    | .chain _ => ghostLets)

/-- The claim part of the refute file (`claimDecls`): the sampler `inputs` of the claim (the name the claim file calls), the
two sides of the claim, and the render of the claim input. The claim fuel is `cycle × size + 8` (5.3). -/
private def claimDecls (f : Facts) (cycle : Nat) : List String :=
  -- A claim input holds its L3 input, state and exact statement parameters. Several L3 inputs form a tuple,
  -- bound by a `let` pattern in each function (`_` for an input that the function does not read).
  let (inTy, inVal, bindIn, size, renderParts) : String × String × (List String → String → String) × String × List String :=
    match f.inShape with
    | .list inp inTy => (inTy, inp, fun _ t => t, "x.1", ["\"xs = \" ++ toString x.1"])
    | .record inp inTy l ss =>
      (inTy, inp, fun _ t => t, s!"x.1.{l}", (l :: ss).map fun n => s!"\"{n} = \" ++ toString x.1.{n}")
    | .flat inputs l =>
      let pattern (use : List String) : String :=
        "(" ++ ", ".intercalate (inputs.map fun (n, _) => if use.contains n then n else "_") ++ ")"
      ("(" ++ " × ".intercalate (inputs.map (·.2)) ++ ")", "(" ++ ", ".intercalate (inputs.map (·.1)) ++ ")",
        fun use t => s!"let {pattern use} := x.1\n  {t}", l,
        inputs.map fun (n, _) => s!"\"{n} = \" ++ toString {n}")
  let all : List String := match f.inShape with
    | .flat inputs _ => inputs.map (·.1)
    | _ => []
  let rhsCall := s!"({f.runCall})"
  let rhsWord := resultWord f.val f.resultFn "yRun"
  let rhs := match f.form with
    | .heap => s!"{rhsCall}.map fun ys => Obj.words state'.{regName f.ptrReg}.toBitVec {f.mem} .W64 ys :: state'.heap.tail"
    | .word | .narrow => s!"{rhsCall}.map fun yRun => {rhsWord}"
    | .both =>
      s!"{rhsCall}.map fun y => ({f.val.word "y.1"}, Obj.words state'.{regName f.ptrReg}.toBitVec {f.mem} .W64 y.2 :: state'.heap.tail)"
  let lhsRet := if f.proj.isEmpty then "r" else s!"({f.proj} r)"
  let inTyP := claimInputType inTy f.params
  let lhs := s!"match blocksP.run noRun ({cycle} * {size}.length + 8) Lbl.entry (initP x.2.1) with\n  | .ok r => some {lhsRet}\n  | _ => none"
  [ s!"def _root_.Skel.{f.fn}.inputs (g : Rng) : Option ({inTyP}) :=\n  " ++
      lineBlock (admittedInputs f [s!"some ({inVal}, a, {capturedValue f.params})"]),
    s!"def claimValid (x : {inTyP}) : Bool :=\n  " ++ claimScope inVal f.params f.admission,
    s!"def claimLhs (x : {inTyP}) : Option {resultTy f} :=\n  if !claimValid x then none else\n  " ++ bindIn [size] lhs,
    s!"def claimRhs (x : {inTyP}) : Option {resultTy f} :=\n  if !claimValid x then none else\n  " ++ claimScope inVal f.params rhs,
    s!"def claimRender (x : {inTyP}) : String :=\n  " ++ bindIn all (String.intercalate " ++ \", \" ++ " renderParts) ]

/-! ## The value and its text -/

/-- The text of a list of strings, as Lean literals. -/
private def strs (xs : List String) : String := "[" ++ ", ".intercalate (xs.map String.quote) ++ "]"

/-- The text of a `RefuteSpec` value: a structure instance with each field, in the form of `Skel/Toy/*Refute.lean`. -/
def specLiteral (r : RefuteSpec) : String :=
  "{\n  " ++ ",\n  ".intercalate
    [ s!"fn := {r.fn.quote}", s!"imports := {strs r.imports}", s!"opens := {r.opens.quote}",
      s!"modelNames := {strs r.modelNames}", s!"loopLabel := {r.loopLabel.quote}", s!"fuel := {r.fuel}",
      s!"helpers := {strs r.helpers}", s!"ghostTy := {r.ghostTy.quote}", s!"stateTy := {r.stateTy.quote}",
      s!"resultTy := {r.resultTy.quote}", s!"lets := {strs r.lets}", s!"admitted := {r.admitted.quote}",
      s!"free := {r.free.quote}", s!"render := {r.render.quote}", s!"claimDecls := {strs r.claimDecls}" ] ++
    (if r.proj.isEmpty then "" else s!",\n  proj := {r.proj.quote}") ++ "\n}"

/-! ## The family `objects` (DISC-RESULT)

An input that is no list of words behind one binder and no chain of nodes (such as a structure with an array of structures,
`Vector Slot 1024`, behind several address binders): the samplers draw the L3 input by its type (`Skel.Sample.drawWhere`,
with `#derive_sample` of `Skel/Lean/SampleObj.lean` for its structures), with redraws until `run` gives a value, draw an
address for each binder, and make the heap from the objects of the statement (`objsP <binders> <input>`, the definition of the
model). Several inputs are drawn as the tuple of their types. The registers of the input are the arguments of the statement.
The ghost is the L3 result, the input (or the tuple) and the list of the binders; the slots bind `y`, `a`, `inp` (one input)
or each input by its name (several inputs), and each binder by its name. The family uses address binders and has a value result
or a value with a heap. Memory in the state is independent of the result kind. A paired result compares its value only. -/

/-- The modules of the constants that the frame text of the model names (`Skel/Gen/Frame.lean`: `SysV.Outside`,
`SysV.StackRoom` and `SysV.Mapped` in `Frame` and `post`). The check files have them; a refute file holds the same model text,
so it needs them too (HARNESS-LOOP D2: without them each refute file of the pilot had two errors, an unknown identifier
`SysV.Mapped`). -/
def frameImports : List String := ["Lift.Sem.StackRoom", "Lift.Sem.StackPush", "Lift.Tactic.FrameMemLemmas"]

/-- The words of a ghost of the family `objects`: the L3 result, the input of the type `inTy`, and the binders. -/
private def objGhostTy (yTy inTy : String) : String := s!"({yTy} × {inTy} × List (BitVec 64))"

/-- The slot of the one input of the family `objects` when the statement has one input (a structure): the refute spec binds it
as `inp`, since `x` is the state. -/
def objectsInputSlot : String := "inp"

/-- The refute spec of the family `objects` (see above), or the error `err` of the other families when the plan is not of this
family. -/
private def objectsSpec (p : UpperPlan) (sh : StmtShape) (m : ModelSpec) (runConst : String) (hd : Head) (err : GenError) :
    Except GenError RefuteSpec := do
  -- A memory state can have a scalar result. Only `both` returns the memory as part of its result.
  let withMem := p.mem && p.kind == .both
  unless (p.kind == .value || withMem) && !p.params.isEmpty && p.params.all (·.ty == .addr) && p.ghosts.isEmpty do
    throw err
  unless sh.args.length ≤ argOrder.length do throw err
  -- one input: its name, its type, and the slot `inp`; several inputs: the tuple of their names, the product of their types,
  -- and a slot for each name
  let (inp, inTy, objArgs, slotLet, names) : String × String × String × String × List String := match sh.form with
    | .one b => (b.name.s, tyText b, b.name.s, s!"let {objectsInputSlot} := g.2.1", [b.name.s])
    | .flat bs =>
      let ns := bs.map (·.name.s)
      ("(" ++ ", ".intercalate ns ++ ")", "(" ++ " × ".intercalate (bs.map tyText) ++ ")", " ".intercalate ns,
        "let (" ++ ", ".intercalate ns ++ ") := g.2.1", ns)
  let ps := p.params.map (·.name.s)
  let taken := ["g", "h", "a", "inp", "before"] ++ (if names.length > 1 then ["x", "y"] else [])
  if let some n := (names ++ ps).find? taken.contains then
    throw (GenError.shape 0 s!"{p.fn}: the name {n} of the statement is a name of the sampler")
  let args := argOrder.zip (sh.args.map (·.term.s))
  let runCall := sh.runApplication
  let val := p.val
  let form : ResultForm := if val.isWord then .word else .narrow
  -- with the memory, the refuter compares the value only: the family has no expected memory (the L3 result does not say which
  -- objects it writes), so the memory of the result is dropped on both sides
  let proj := if withMem then s!"(fun (r : UInt64 × Heap) => (r.1{if val.isWord then "" else s!" &&& {val.mask}"}, ([] : Heap)))"
    else projText p
  let yTy := match sh.runResultType with
    | some ty => s!"({ty.s})"
    | none => if form == .word then "BitVec 64" else val.outTy
  let gTy := objGhostTy yTy inTy
  -- a register of the input that no argument gives: the statement does not fix it, so a drawn word; an argument narrower
  -- than 64 bits is zero-extended
  let argOfR (r : Reg64) : String := ((args.find? (·.1 == r)).map (·.2)).getD
    s!"Skel.Sample.word (g.stream {40 + ((p.inputs.findIdx? (· == r)).getD 0)})"
  let paramLets := ps.zipIdx.map (fun (n, i) => s!"let {n} := Skel.Sample.addrOf (g.stream {i + 1})")
  let afterInput : List String :=
    [s!"let h : Heap := objsP {" ".intercalate ps} {objArgs}",
     s!"let a : In2p := {structText ((if p.kind.hasPolicy then ["policy := ⟨fun _ => true⟩"] else []) ++ ["heap := h"] ++
        p.inputs.map fun r => s!"{regName r} := UInt64.ofBitVec (BitVec.setWidth 64 ({argOfR r}))")}"]
  let admission := admissionTest sh
  let accepted := admittedRunTest admission runCall
  let sampledBody (body : String) : List String := paramLets ++
    [s!"match Skel.Sample.drawWhere? (α := {inTy}) (fun {inp} => {accepted}) (g.stream 0) with\n  | none => none\n  | some {inp} =>\n    " ++
      "\n    ".intercalate (afterInput ++ [body])]
  -- with the memory, the L3 result is a tuple whose first part is the value
  let yText := if sh.runResultType.isSome then s!"({runCall}).getD {resultDefault}"
    else if withMem then s!"(match {runCall} with | some y => y.1 | none => {val.dflt})"
    else s!"({runCall}).getD {val.dflt}"
  let word := resultWord val sh.resultFn yText (withMem && sh.runResultType.isSome)
  let expected := if withMem then s!"({word}, ([] : Heap))" else word
  let resTy := if withMem then "UInt64 × Heap" else "UInt64"
  let ghost := s!"({yText}, {inp}, [{", ".intercalate ps}])"
  let stTy := p.stateType
  let vals := hd.state.map fun (r, v) => (r, headValText v)
  let state (vs : List (Reg64 × String)) : String :=
    structText (["input := a"] ++ vs.map (fun (r, v) => s!"{regName r} := {v}") ++ (if p.mem then ["mem := h"] else []))
  let freeVals := p.state.zipIdx.map fun ((r, c), j) => (r, match c with
    | .counter => s!"UInt64.ofNat (Skel.Sample.counter (g.stream {20 + j}) 6)"
    | .accumulator => s!"UInt64.ofBitVec (Skel.Sample.word (g.stream {20 + j}))"
    | .pointer => s!"UInt64.ofBitVec ((Skel.Sample.pointer (g.stream {20 + j}) [{", ".intercalate ps}, 0]).getD 0)")
  let rhsWord := resultWord val sh.resultFn "y" withMem
  let rhs := s!"({runCall}).map fun y => " ++
    (if withMem then s!"({rhsWord}, ([] : Heap))" else rhsWord)
  let lhsRet := if proj.isEmpty then "r" else s!"({proj} r)"
  let claimTy := claimInputType inTy p.params
  let claim :=
    [ s!"#derive_sample {inTy}",
      s!"def _root_.Skel.{m.fn}.inputs (g : Rng) : Option ({claimTy}) :=\n  " ++ lineBlock (sampledBody s!"some ({inp}, a, {capturedValue p.params})"),
      s!"def claimValid (x : {claimTy}) : Bool :=\n  " ++ claimScope inp p.params admission,
      s!"def claimLhs (x : {claimTy}) : Option ({resTy}) :=\n  if !claimValid x then none else\n  match blocksP.run noRun ({hd.cycle} * 1032 + 8) Lbl.entry (initP x.2.1) with\n  | .ok r => some {lhsRet}\n  | _ => none",
      s!"def claimRhs (x : {claimTy}) : Option ({resTy}) :=\n  if !claimValid x then none else\n  " ++ claimScope inp p.params rhs,
      s!"def claimRender (x : {claimTy}) : String :=\n  \"input of \" ++ toString x.2.1.heap.length ++ \" objects\"" ]
  let specModule := moduleOf runConst
  let imports := (["Skel.Lean.Refute", "Skel.Lean.Sample", "Skel.Lean.SampleObj", "Skel.Lean.Admission", heapImport] ++
    (if withMem then ["Lift.Sem.HeapDec"] else []) ++ m.imports ++ frameImports ++ [specModule, moduleOf sh.fn.term.s]).eraseDups
  -- the admitted sampler: a draw that the spec refuses is no admitted sample (HARNESS-LOOP2, the cause of H3: `drawWhere`
  -- gave such a draw after its redraws, and the refuter compared the result term with the default value at a state that no
  -- entry reaches)
  let admittedBody := lineBlock (sampledBody s!"some ({ghost}, refuteHeadState a h, {expected})")
  -- the head state is its own declaration: in the body of the sampler, a head value with nested matches (the `min` of two loads
  -- of mapInPlace) reached the maximum recursion depth of the elaborator
  let headDef := defText s!"def refuteHeadState (a : In2p) (h : Heap) : {stTy}" [s!"let _ := h", state vals]
  -- the admitted sample of an input (HARNESS-LOOP3): the guided search of the refuter builds the sample of a mutated input
  let buildDef := s!"def refuteBuild (g : Rng) (inpB : {inTy}) : Option ({gTy} × {stTy} × {resTy}) :=\n  " ++
    lineBlock (paramLets ++ [s!"let {inp} := inpB", s!"if ({accepted}) then\n    " ++
      "\n    ".intercalate (afterInput ++ [s!"some ({ghost}, refuteHeadState a h, {expected})"]) ++ "\n  else none"])
  let mutantDef := s!"def refuteMutant (g m : Rng) (d : List UInt64) (gh : {gTy}) : Option ({gTy} × {stTy} × {resTy}) :=\n  " ++
    "refuteBuild g (Skel.Sample.Mutate.mutate m d gh.2.1)"
  -- the render of a sample: the registers, then the L3 result and the inputs of the ghost (HARNESS-LOOP2, H4)
  -- the state is `stR`: the one input of the statement can have the name `x`
  let ghostParts := ("\", y = \" ++ Skel.Sample.showGhost 300 g.1") :: names.map fun n => s!"\", {n} = \" ++ Skel.Sample.showGhost 300 {n}"
  let templateSlots := match inShapeOf sh with
    | .ok (.list ..) => ["let xs := g.2.1"]
    | .ok (.record _ _ l ss) => s!"let xs := g.2.1.{l}" :: ss.map fun s => s!"let {s} := g.2.1.{s}"
    | .ok (.flat _ l) => if l == "xs" then [] else [s!"let xs := {l}"]
    | .error _ => []
  pure
    { fn := m.fn, imports, opens := " ".intercalate (["Lift.P2.Total", "Lift.Sem", moduleOf specModule] ++ m.opens),
      modelNames := m.names, loopLabel := hd.name.s, fuel := hd.fuel,
      helpers := [s!"#derive_sample {inTy}", s!"#derive_repr {inTy}", "def xsOf (_ : In2p) : List (BitVec 64) := []", headDef,
        s!"#derive_mutate {inTy}", buildDef, mutantDef],
      ghostTy := gTy, stateTy := stTy, resultTy := resTy,
      lets := ["let y := g.1", "let a := x.input", slotLet] ++ templateSlots ++
        ps.zipIdx.map (fun (n, i) => s!"let {n} := g.2.2.getD {i} 0"),
      admitted := s!"def refuteAdmitted (g : Rng) : Option ({gTy} × {stTy} × {resTy}) :=\n  " ++ admittedBody,
      free := defText s!"def refuteFree (g : Rng) : Option ({gTy} × {stTy})"
        (sampledBody s!"some ({ghost}, {state freeVals})"),
      render := defText s!"def refuteRender (g : {gTy}) (stR : {stTy}) : String"
        [s!"let {inp} := g.2.1",
         String.intercalate " ++ " ("\"state\"" :: p.state.map (fun (r, _) => s!"\", {regName r} = \" ++ toString stR.{regName r}")
           ++ ghostParts)],
      claimDecls := claim, proj, l3Text := sh.l3Text }

/-- The refute spec of an array of words or a chain of nodes (the family `family`). -/
private def listSpec (p : UpperPlan) (h : HintRecord) (sh : StmtShape) (m : ModelSpec) (runConst : String) (hd : Head)
    (family : Family) : Except GenError RefuteSpec := do
  let ptrReg ← ptrRegOf h
  let form ← resultFormOf p family
  let argTexts := sh.args.map (·.term.s)
  let inShape ← inShapeOf sh
  -- the expected heap of a heap result is the words of the L3 result in the array of the binder (`expectedText`): the result is
  -- the list of words, the input is the list that the array holds, and the family is an array
  if form == .heap then
    match family, inShape with
    | .array, .list .. => pure ()
    | .array, _ => throw (.unsupported 0 s!"{p.fn}: a heap result has a sampler for a list input only; the input is not the list that the array holds (a record or several inputs)")
    | .chain _, _ => throw (.unsupported 0 s!"{p.fn}: a heap result has a sampler for an array only; the family is a chain of nodes")
  unless sh.args.length ≤ argOrder.length do throw (GenError.shape 0 s!"{p.fn}: more arguments than registers")
  let args := argOrder.zip argTexts
  unless p.inputs.all (fun r => args.any (·.1 == r)) do
    throw (GenError.shape 0 s!"{p.fn}: an input register has no argument")
  let bn ← match p.params with
    | [b] => pure b.name.s
    | _ => throw (GenError.shape 0 s!"{p.fn}: the samplers draw one binder, the plan has {p.params.length}")
  let specModule := moduleOf runConst
  unless specModule != "" do throw (GenError.shape 0 s!"{p.fn}: the run {runConst} has no module")
  -- several inputs are variables of the generated text: none has the name of a name of the sampler, and each scalar is an argument
  if let .flat inputs l := inShape then
    let taken := ["g", "ws", "before", "after", "h", "a", "x", "xs", "base", "nodes", "frame", bn]
    if let some n := (inputs.map (·.1)).find? fun n => taken.contains n && !(n == "xs" && n == l) then
      throw (GenError.shape 0 s!"{p.fn}: the input {n} has the name of a name of the sampler")
    if let some n := (InShape.flatScalars inputs l).find? fun n => !argTexts.any (·.trimAscii.toString == n) then
      throw (GenError.shape 0 s!"{p.fn}: no argument is the scalar input {n}, which gives its register")
  let ghostsOk := match family with
    | .array => p.ghosts.isEmpty
    | .chain n => p.ghosts == [({ reg := ptrReg, off := n.next } : Ghost)]
  unless ghostsOk do throw (GenError.shape 0 s!"{p.fn}: the ghosts are not the chain of the pointer")
  let captureParams := usesParams p.params sh.runApplication sh.resultFn
  if captureParams then
    let reserved := ["g", "ws", "before", "after", "h", "a", "x", "xs", "base", "nodes", "frame", "y"] ++
      p.ghosts.map (s!"rest_{regName ·.reg}")
    if let some b := p.params.find? fun b => reserved.contains b.name.s then
      throw (.shape 0 s!"{p.fn}: the name {b.name.s} of the statement parameter is a name of a sampler slot")
  let f : Facts :=
    { fn := m.fn, head := hd, family, inShape, bn, params := p.params, captureParams,
      runCall := sh.runApplication, admission := admissionTest sh, args, inputs := p.inputs, state := p.state, mem := p.mem,
      form, val := p.val, policy := p.kind.hasPolicy, ptrReg, ghosts := p.ghosts, proj := projText p,
      runResultType := sh.runResultType, resultFn := sh.resultFn }
  let imports := (["Skel.Lean.Refute", "Skel.Lean.Sample", "Skel.Lean.Admission", heapImport] ++ m.imports ++ frameImports ++
    [specModule, moduleOf sh.fn.term.s]).eraseDups
  pure
    { fn := f.fn, imports, opens := " ".intercalate (["Lift.P2.Total", "Lift.Sem", moduleOf specModule] ++ m.opens),
      modelNames := m.names, loopLabel := hd.name.s, fuel := hd.fuel, helpers := helperDecls f,
      ghostTy := loopGhostTy f, stateTy := stateTy f, resultTy := resultTy f, lets := slotLets f,
      admitted := admittedDef f, free := freeDef f, render := renderDef f,
      claimDecls := claimDecls f hd.cycle, proj := f.proj, l3Text := sh.l3Text }

/-- The `RefuteSpec` value of the function of the plan `p`, with the hint `h`, the statement `sh` and the model `m`. The
fuel is the fuel of the one loop head (5.3). A plan of no array of words and no chain of nodes has the family `objects`
(`objectsSpec`) when it fits it. -/
def refuteSpec (p : UpperPlan) (h : HintRecord) (sh : StmtShape) (m : ModelSpec) : Except GenError RefuteSpec := do
  if p.privateStack then
    throw (.unsupported 0 s!"{p.fn}: the sampler does not construct private stack states")
  if p.stackArgs > 0 then
    throw (.unsupported 0 s!"{p.fn}: the sampler does not construct stack arguments")
  if sh.l3Form == .post then
    throw (.unsupported 0 s!"{p.fn}: the sampler does not construct existential run witnesses")
  if sh.resultFn.isSome && sh.runResultType.isNone then
    throw (.unsupported 0 s!"{p.fn}: the result projection has no run result type")
  let runConst ← sh.runConst
  let hd ← singleHead p
  if p.kind == .both && sh.resultFn.isSome then
    return ← objectsSpec p sh m runConst hd
      (.unsupported 0 s!"{p.fn}: the projected result has no list memory sampler")
  match familyOf p h with
  | .error e => objectsSpec p sh m runConst hd e
  | .ok family => listSpec p h sh m runConst hd family

end Skel.Gen
