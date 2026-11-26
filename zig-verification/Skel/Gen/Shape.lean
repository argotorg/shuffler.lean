import Skel.Gen.Types
import Lean.Data.Json

/-! The shape of a trusted statement (`docs/one-way-lift-g3-plan-20261118.md`, sections 1.1 and 4.1, task G3-03).

A trusted statement has the form `∀ inputs, C inputs → <binders and hypotheses> → f.Call args objs post`, with `f.CallB` in
place of `f.Call` for some functions. The inputs are the variables before the contract `C`: one record `x` of a toy, or
several variables (`∀ dest i, C dest i → …`); a statement with no variable before `C` has no input (`C → f.Call …`), and a
statement with no hypothesis has no contract (the text `True`) and no input. The command `#stmt_shape`
(`Skel/Lean/Shape.lean`) reads the constant and prints one JSON object. `Shape.parse` turns this JSON into a
`StmtShape`; it is the only way to make one from text. The terms are Lean source text. Each is printed with full
names, so it does not depend on the `open` commands of the file that uses it. This module holds no name of a fixture.

The JSON object has the keys `inputs`, `contract`, `binders`, `hyps`, `call`, `fn`, `args`, `objs` and `post`, and the key
`run` when `post` names the function `run` of L3 (`StmtShape.runConst` has the rule when it does not): each of `inputs` and each of `binders` is `{"name", "type"}`; `contract` is the text of `C x`, or `True`; `call` is `"call"`,
`"callB"` or `"call8"`; `hyps` is a list of texts, in the
order of the statement, without `C x`; `fn` is `{"term", "room", "ret"}` with `ret` the number of bits (8, 16, 32 or
64); each of `args` is `{"bits", "term", "form"}`, the width, the value and the form of the value of one field (`form` is
`{"kind": "bv"}` or `{"kind": "nat", "term": t}`, see `ArgForm`); `objs`, `post` and `run` are texts. The key `stack` is the list of the two stack arguments (as `args`), present exactly when `call` is
`"call8"`. The key `result` is the text of the term that `post` equates to the result field (`Encode.encode result = [r]`); it is
read when `post` names no `run`, and `Shape.parse` reads it as it is. -/

namespace Skel.Gen

open Lean (Json)

/-- A text of Lean source that has a character other than white space. -/
def Src.valid (s : String) : Bool := s.toList.any (fun c => !c.isWhitespace)

/-- A term or a type, as Lean source text that is not blank. The only ways to make one are `Src.parse` and this
constructor with its proof. -/
structure Src where (s : String) (ok : Src.valid s = true)
  deriving DecidableEq, Repr

/-- The text `s` as a `Src`, when it is not blank. -/
def Src.parse (s : String) : Option Src :=
  if h : Src.valid s = true then some ⟨s, h⟩ else none

instance : BEq Src := ⟨fun a b => a.s == b.s⟩

/-- A bound variable of the statement, with the text of its type. -/
structure ShapeBinder where (name : Ident) (type : Src)

instance : BEq ShapeBinder := ⟨fun a b => a.name.s == b.name.s && a.type == b.type⟩

/-- The form of the value of an argument. `nat t`: the value is `BitVec.ofNat 64 t` exactly (a 64-bit field), so the register
holds `t` as a natural number when `t < 2 ^ 64`. `bv`: any other term, which the relation states as an equality of bit
vectors. `Skel/Lean/Shape.lean` decides the form from the structure of the term. -/
inductive ArgForm where
  | nat (t : Src)
  | bv
  deriving BEq, DecidableEq, Repr

/-- One argument of the call: the width of the field, the text of its value and the form of its value. A `nat` form has
the width 64 (`Shape.parse` checks it). -/
structure ArgShape where (width : Width) (term : Src) (form : ArgForm)
  deriving BEq, DecidableEq, Repr

/-- The function of the call: its text, the stack room in bytes and the width of its result. -/
structure FnShape where (term : Src) (room : Nat) (ret : Width)
  deriving BEq

/-- The form of the call: `Fn.Call`, `Fn.CallB` (`Lift.Pilot.Call`: `Fn.Call` with the permission of each access of each
width inside each object), or `Call8` (`Lift.Level2z.Args8Statement.Call8`: `Fn.Call` with two stack arguments `g` and `h`, the
seventh and the eighth argument, which the entry state has at `rsp + 8` and `rsp + 16`; the six register arguments are in
`StmtShape.args`). A `call8` has exactly two stack arguments. -/
inductive CallForm where
  | call
  | callB
  | call8 (g h : ArgShape)
  | call8B (g h : ArgShape)
  deriving BEq, DecidableEq, Repr

def CallForm.name : CallForm → String
  | .call => "call"
  | .callB => "callB"
  | .call8 .. => "call8"
  | .call8B .. => "call8B"

/-- The stack arguments of the call form, in order: two for `call8`, none for the others. -/
def CallForm.stack : CallForm → List ArgShape
  | .call8 g h | .call8B g h => [g, h]
  | _ => []

/-- The call entry supplies byte-range permissions for its objects and stack room. -/
def CallForm.bytePermits : CallForm → Bool
  | .callB | .call8B .. => true
  | .call | .call8 .. => false

/-- The conjunct of the byte-range permission of the heap `heap` (an operand) under the policy `policy` (decision D40), in `l2p.rep`,
`SimIn` and `l3.rep`: `Fn.CallB` gives it (`Lift.Sem.Bridge.Fn.EntryB.holds_permits`), and the proofs of `Heap.loadB` and
`Heap.storeB` need it; `Fn.Call` gives none. -/
def CallForm.permitsConj (cf : CallForm) (heap policy : String) : List String :=
  if cf.bytePermits then [s!"Heap.Permits {policy} {heap}"] else []

/-- Functional posts return one L3 value. A post with extra existential run witnesses is proved as a whole. -/
inductive L3Form where
  | functional
  | post
  deriving BEq, DecidableEq, Repr

/-- The statement `∀ inputs, contract → ∀ binders, hyps → fn.Call args objs post`. The binders come first and the
hypotheses after them: no binder type depends on a hypothesis. A toy has one input, a record. `call` is the call form. `run` is
the function of L3 that `post` names (`∃ y, run x = some y ∧ …`), as `#stmt_shape` reads it from the body of `post`; none when
`post` names no such function (`StmtShape.runConst` has the rule for that case). `result` is the term that `post` equates to the
result field, `Encode.encode result = [r]`, in the variables of the statement. It is read only when `post` names no `run`: a
statement with no contract and no `run` states the result as a term of its variables (`(run cells i pos mode).1`); the shape does
not make a `run` of it. `l3Text` is the source text of the L3 definitions that the contract, the objects and `post` name
(`#stmt_shape` reads it, HARNESS-LOOP D4): the prompts of the models show it; empty when it was not read.
`resultFn` preserves a nontrivial encoded result term as a function of the existential L3 result of `post`.
`runResultType` is the type of the existential L3 result, including direct-value and heap posts.
`runOutputObjs` maps that result to the objects in direct conjunctive `Mem.has` clauses of the post.
`runCall` is the actual run expression in the variables of the statement. It excludes variables
bound inside the post; old shapes without it use the input application rule. -/
structure StmtShape where
  (inputs : List ShapeBinder) (contract : Src) (binders : List ShapeBinder) (hyps : List Src)
  (fn : FnShape) (args : List ArgShape) (objs post : Src) (call : CallForm := .call) (run : Option Src := none)
  (result : Option Src := none) (l3Text : String := "") (resultFn : Option Src := none)
  (runResultType : Option Src := none)
  (runOutputObjs : Option Src := none)
  (l3Form : L3Form := .functional)
  (runCall : Option Src := none)
  deriving BEq

/-- How the inputs of the statement reach the L3 model (`Model A R` has one input type `A`). One input is the input of the model:
a record `x`, as in the toys. No input, or several (`∀ dest i, C dest i → …`), are parameters of the model, as the statement
has them: the model has the input type `Unit`, and `run` is applied to the inputs by name (the parameters of `run` have the
names of the inputs). The statement applies `C`, `objects`, `post` and the arguments to the variables of the inputs, so the
texts of the generators, which copy these terms, need the variables in scope; a tuple of the inputs could not hold a binder
whose type depends on another (`∀ {n} buf slot`). -/
inductive InputForm where
  | one (b : ShapeBinder)
  | flat (bs : List ShapeBinder)

def StmtShape.form (s : StmtShape) : InputForm :=
  match s.inputs with
  | [b] => .one b
  | bs => .flat bs

/-- The module of a qualified name: `Lift.Toys.FindSpec` for `Lift.Toys.FindSpec.C`. -/
def moduleOf (s : String) : String := ".".intercalate ((s.splitOn ".").dropLast)

/-- The function `run` of L3 of a statement (the shape has the `run` that `post` names), or, when `post` names none, the `run`
in the module of the contract: the contract is an application `<Module>.C args` of a constant named `C`, as in each spec module
of the trusted statements (`C` and `run` are side by side: `FindSpec.C`, `FindSpec.run`). A contract that is no application of a
`C` of a module (`True`, a proposition, a conjunction) has no `run` by this rule, and the shape has no `run`: an error. -/
def StmtShape.runConst (s : StmtShape) : Except GenError String :=
  match s.run with
  | some r => .ok r.s
  | none =>
    let head := (s.contract.s.splitOn " ").headD ""
    match head.splitOn "." |>.reverse, s.result with
    | "C" :: _ :: _, _ => .ok (moduleOf head ++ ".run")
    | _, some r =>
      .error (.shape 0 s!"no run of L3: post gives the result as the term {r.s} of the variables, and the contract {s.contract.s} is no application of a C of a module")
    | _, none =>
      .error (.shape 0 s!"no run of L3: post names no run, and the contract {s.contract.s} is no application of a C of a module")

/-- The name of the L3 function of a statement whose `post` gives the result as a term (`StmtShape.result`, L2-NORUN): the
relation text declares it (`UpperRel`, `resultRunText`). -/
def resultRun : String := "run3"

/-- The shape of a statement whose `post` gives the result as a term and names no `run` (L2-NORUN), as the upper generators
read it: the binders are inputs, since the result term is a function of them and the L3 function `resultRun` takes them by
name, and `run` is `resultRun`. A shape with a `run`, with no result term, or with a contract `C` of a module is as it is. -/
def StmtShape.resultForm (s : StmtShape) : StmtShape :=
  match s.run, s.result, s.runConst with
  | none, some _, .error _ => { s with inputs := s.inputs ++ s.binders, binders := [], run := Src.parse resultRun }
  | _, _, _ => s

/-- The shape is the form of `resultForm` of a statement with a result term: its `run` is `resultRun`. -/
def StmtShape.byResult (s : StmtShape) : Bool := s.result.isSome && s.run.map (·.s) == some resultRun

/-- The `run` of L3 as a name, for the texts: the name of `runConst`, empty when there is none. The generators have checked
`runConst` before they build a text, so a text has no empty name. -/
def runName (s : StmtShape) : String := (s.runConst.toOption).getD ""

/-- The names of the variables of the statement: the inputs, then the binders. -/
def StmtShape.names (s : StmtShape) : List String := (s.inputs ++ s.binders).map (·.name.s)

/-- The name `base`, primed when `taken` has it: a binder of a generated text with this name does not hide a variable that the
text copies. The primed name is free: an `Ident` has no `'`. -/
def freshAmong (taken : List String) (base : String) : String :=
  if taken.contains base then base ++ "'" else base

namespace InputForm

/-- The inputs, in the order of the statement. -/
def binders : InputForm → List ShapeBinder
  | .one b => [b]
  | .flat bs => bs

/-- The names of the inputs. -/
def names (f : InputForm) : List String := f.binders.map (·.name.s)

/-- The inputs as binders of a definition: `(x : T)`. -/
def binderTexts (f : InputForm) : List String := f.binders.map fun b => s!"({b.name.s} : {b.type.s})"

/-- The binders of the inputs that are parameters of the model `l3`: all of them for `flat`, none for `one`. -/
def modelBinderTexts : InputForm → List String
  | .one _ => []
  | f@(.flat _) => f.binderTexts

/-- The binder of the one input that a row quantifies after the model parameters (the input of the model): none for `flat`. -/
def outerBinderTexts : InputForm → List String
  | f@(.one _) => f.binderTexts
  | .flat _ => []

/-- The inputs that are parameters of the model, as arguments of `l3`. -/
def modelArgs : InputForm → List String
  | .one _ => []
  | f@(.flat _) => f.names

/-- The pattern of the input of the model, in `rep`, `returns` and `post`. -/
def pat : InputForm → String
  | .one b => b.name.s
  | .flat _ => "_"

/-- The input of the model as an argument of `rep` and `post`, where the inputs are bound by a row. -/
def arg : InputForm → String
  | .one b => b.name.s
  | .flat _ => "()"

/-- The L3 function `run` applied to the inputs: to the one input, or, for `flat`, to each input by name. -/
def runApp (f : InputForm) (run : String) : String :=
  match f with
  | .one b => s!"{run} {b.name.s}"
  | .flat bs => run ++ String.join (bs.map fun b => s!" ({b.name.s} := {b.name.s})")

end InputForm

/-- The run expression read from the post. Old shapes apply their inputs by the original rule. -/
def StmtShape.runApplication (s : StmtShape) : String :=
  (s.runCall.map (·.s)).getD (s.form.runApp (runName s))

/-- The admitted L3 return premise. Post-based models prove the full post under the contract. -/
def StmtShape.returnsText (s : StmtShape) (y : String) : String :=
  match s.l3Form with
  | .functional => s!"{s.runApplication} = some {y}"
  | .post => s.contract.s

/-- The result binder of a row; a post-based model has one unit result. -/
def StmtShape.resultBinder (s : StmtShape) (y : String) : String :=
  if s.l3Form == .post then s!"({y} : Unit)" else y

/-! ## Writing -/

def ShapeBinder.toJson (b : ShapeBinder) : Json := Json.mkObj [("name", b.name.s), ("type", b.type.s)]

def ArgForm.toJson : ArgForm → Json
  | .nat t => Json.mkObj [("kind", "nat"), ("term", t.s)]
  | .bv => Json.mkObj [("kind", "bv")]

def ArgShape.toJson (a : ArgShape) : Json :=
  Json.mkObj [("bits", a.width.bits), ("term", a.term.s), ("form", a.form.toJson)]

def FnShape.toJson (f : FnShape) : Json :=
  Json.mkObj [("term", f.term.s), ("room", f.room), ("ret", f.ret.bits)]

/-- The JSON object of the shape; `Shape.parse` reads it back. -/
def StmtShape.toJson (s : StmtShape) : Json :=
  Json.mkObj (
    [ ("inputs", Json.arr (s.inputs.map ShapeBinder.toJson).toArray), ("contract", s.contract.s),
      ("binders", Json.arr (s.binders.map ShapeBinder.toJson).toArray),
      ("hyps", Json.arr (s.hyps.map (fun h => Json.str h.s)).toArray), ("call", s.call.name), ("fn", s.fn.toJson),
      ("args", Json.arr (s.args.map ArgShape.toJson).toArray), ("objs", s.objs.s), ("post", s.post.s) ]
      ++ (s.run.map fun r => [("run", Json.str r.s)]).getD []
      ++ (s.runCall.map fun r => [("runCall", Json.str r.s)]).getD []
      ++ (match s.call.stack with
        | [] => []
        | st => [("stack", Json.arr (st.map ArgShape.toJson).toArray)])
      ++ (s.result.map fun r => [("result", Json.str r.s)]).getD []
      ++ (s.resultFn.map fun r => [("resultFn", Json.str r.s)]).getD []
      ++ (s.runResultType.map fun r => [("runResultType", Json.str r.s)]).getD []
      ++ (s.runOutputObjs.map fun r => [("runOutputObjs", Json.str r.s)]).getD []
      ++ (if s.l3Form == .post then [("l3Form", Json.str "post")] else [])
      ++ (if s.l3Text.isEmpty then [] else [("l3", Json.str s.l3Text)]))

/-! ## Reading -/

namespace Shape

/-- The value of the key `k` of the object `j`. `ctx` is the path of `j`, for the error. -/
private def key (ctx : String) (j : Json) (k : String) : Except String Json :=
  match j with
  | .obj _ => (j.getObjVal? k).mapError (fun _ => s!"{ctx}: no key {k}")
  | _ => .error s!"{ctx}: expected an object"

private def str (ctx : String) : Json → Except String String
  | .str s => .ok s
  | _ => .error s!"{ctx}: expected a string"

private def nat (ctx : String) (j : Json) : Except String Nat :=
  (j.getNat?).mapError (fun _ => s!"{ctx}: expected a natural number")

private def arr (ctx : String) : Json → Except String (List Json)
  | .arr a => .ok a.toList
  | _ => .error s!"{ctx}: expected an array"

/-- The elements of the array `j`, each read by `f` with its path. -/
private def elems {α : Type} (ctx : String) (j : Json) (f : String → Json → Except String α) :
    Except String (List α) := do
  let xs ← arr ctx j
  (xs.zipIdx.map (fun (x, i) => (x, s!"{ctx}[{i}]"))).mapM (fun (x, c) => f c x)

private def src (ctx : String) (j : Json) : Except String Src := do
  let s ← str ctx j
  match Src.parse s with
  | some r => pure r
  | none => .error s!"{ctx}: blank text"

private def width (ctx : String) (j : Json) : Except String Width := do
  match ← nat ctx j with
  | 8 => pure .W8
  | 16 => pure .W16
  | 32 => pure .W32
  | 64 => pure .W64
  | n => .error s!"{ctx}: {n} is not a width (8, 16, 32 or 64)"

private def binder (ctx : String) (j : Json) : Except String ShapeBinder := do
  let n ← str s!"{ctx}.name" (← key ctx j "name")
  let some name := Ident.parse n | .error s!"{ctx}.name: {n} is not an identifier"
  pure ⟨name, ← src s!"{ctx}.type" (← key ctx j "type")⟩

private def argForm (ctx : String) (j : Json) : Except String ArgForm := do
  match ← str s!"{ctx}.kind" (← key ctx j "kind") with
  | "nat" => pure (.nat (← src s!"{ctx}.term" (← key ctx j "term")))
  | "bv" => pure .bv
  | k => .error s!"{ctx}.kind: {k} is not a form (nat or bv)"

private def argShape (ctx : String) (j : Json) : Except String ArgShape := do
  let w ← width s!"{ctx}.bits" (← key ctx j "bits")
  let form ← argForm s!"{ctx}.form" (← key ctx j "form")
  match form, w with
  | .nat _, .W64 | .bv, _ => pure ⟨w, ← src s!"{ctx}.term" (← key ctx j "term"), form⟩
  | .nat _, _ => .error s!"{ctx}.form: the form nat needs the width 64"

/-- The call form of the string `j`, with the stack arguments `stack` of the object (`none` when it has no key `stack`). The form
`call8` has the key `stack` with exactly two arguments; the other forms have no stack argument. -/
private def callForm (ctx : String) (j : Json) (stack : Option Json) : Except String CallForm := do
  let st ← match stack with
    | none => pure []
    | some a => elems "stack" a argShape
  match ← str ctx j, st with
  | "call", [] => pure .call
  | "callB", [] => pure .callB
  | "call8", [g, h] =>
    if g.width == .W64 && h.width == .W64 then pure (.call8 g h)
    else .error "stack: the form call8 has two 64-bit stack arguments"
  | "call8B", [g, h] =>
    if g.width == .W64 && h.width == .W64 then pure (.call8B g h)
    else .error "stack: the form call8B has two 64-bit stack arguments"
  | "call8", _ => .error s!"stack: the form call8 has 2 stack arguments, the object has {st.length}"
  | "call8B", _ => .error s!"stack: the form call8B has 2 stack arguments, the object has {st.length}"
  | "call" , _ | "callB", _ => .error s!"stack: the form {← str ctx j} has no stack argument, the object has {st.length}"
  | k, _ => .error s!"{ctx}: {k} is not a call form (call, callB, call8 or call8B)"

private def fnShape (ctx : String) (j : Json) : Except String FnShape := do
  pure ⟨← src s!"{ctx}.term" (← key ctx j "term"), ← nat s!"{ctx}.room" (← key ctx j "room"),
    ← width s!"{ctx}.ret" (← key ctx j "ret")⟩

/-- The shape that the JSON object `j` describes, or the first error: a missing key, a value of the wrong type, a name
that is not an identifier, a blank text, or a width that is not 8, 16, 32 or 64. -/
def parse (j : Json) : Except String StmtShape := do
  pure
    { inputs := ← elems "inputs" (← key "shape" j "inputs") binder
      contract := ← src "contract" (← key "shape" j "contract")
      binders := ← elems "binders" (← key "shape" j "binders") binder
      hyps := ← elems "hyps" (← key "shape" j "hyps") src
      call := ← callForm "call" (← key "shape" j "call") (match key "shape" j "stack" with | .ok v => some v | .error _ => none)
      fn := ← fnShape "fn" (← key "shape" j "fn")
      args := ← elems "args" (← key "shape" j "args") argShape
      objs := ← src "objs" (← key "shape" j "objs")
      post := ← src "post" (← key "shape" j "post")
      run := ← match key "shape" j "run" with
        | .error _ => pure none
        | .ok v => some <$> src "run" v
      runCall := ← match key "shape" j "runCall" with
        | .error _ => pure none
        | .ok v => some <$> src "runCall" v
      result := ← match key "shape" j "result" with
        | .error _ => pure none
        | .ok v => some <$> src "result" v
      resultFn := ← match key "shape" j "resultFn" with
        | .error _ => pure none
        | .ok v => some <$> src "resultFn" v
      runResultType := ← match key "shape" j "runResultType" with
        | .error _ => pure none
        | .ok v => some <$> src "runResultType" v
      runOutputObjs := ← match key "shape" j "runOutputObjs" with
        | .error _ => pure none
        | .ok v => some <$> src "runOutputObjs" v
      l3Form := ← match key "shape" j "l3Form" with
        | .error _ => pure .functional
        | .ok v => match ← str "l3Form" v with
          | "functional" => pure .functional
          | "post" => pure .post
          | k => .error s!"l3Form: {k} is not a form (functional or post)"
      l3Text := ← match key "shape" j "l3" with
        | .error _ => pure ""
        | .ok v => str "l3" v }

end Shape

end Skel.Gen
