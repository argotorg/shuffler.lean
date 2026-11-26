import Lean
import Skel.Gen.Shape
import Lift.Trusted.Call
import Lift.Trusted.Encode
import Lift.Pilot.Call

/-! The command `#stmt_shape <name>` (`docs/one-way-lift-g3-plan-20261118.md`, section 4.1, task G3-03; the forms of the
pilot, task L3-S1). The constant `<name>` is a trusted statement, a definition `∀ inputs, C inputs → … → f.Call args objs
post`, or `f.CallB args objs post`. The command prints one message: the JSON object of `Skel.Gen.StmtShape.toJson` on one
line, which `Skel.Gen.Shape.parse` reads.

The command opens the statement with `forallTelescope`. A variable is a binder if its type is a type and a hypothesis if its
type is a proposition. The variables before the first hypothesis are the inputs (one record `x` of a toy, or several:
`∀ dest i, C dest i → …`); the first hypothesis is the contract `C`; the later variables and hypotheses are as before. A
statement with no variable before the first hypothesis has no input (`C → f.Call …`). A statement with no hypothesis has no
input and the contract `True`, and every variable is a binder. Implicit binders (`∀ {n} …`) are read as inputs or binders.
An instance binder or a strict-implicit binder is an error that names the form. The key `run` is the function of L3 that the body of
`post` names (`runOf`); it is absent when the body names none. The terms are parts of the statement,
printed with full names (`pp.fullNames`) in the context of the variables, with no change. A helper that the statement names
(`objects`, `post`) stays a name: the command does not unfold it, but `runOf` reads the body of `post`.
The list `args` may be a definition (`args a b c`) or an expression (`args x ++ [f]`): the reader reduces its spine with `whnfD`
and prints the elements of the result; a list that does not reduce to `List.cons` and `List.nil` is an error. The body may be
`Call8 f args g h objs post` (L2-SH): a constant named `Call8` whose definition has `Fn.Entry` and `Fn.Return`, with six register
arguments and two stack arguments `g` and `h` of the type `BitVec 64`; the shape has the call form `call8` with `g` and `h`. When
`post` names no `run`, the key `result` is the term `t` of the conjunct `Encode.encode t = [r]` of the body of `post`. A statement that is not of this form is an error that
names the constant. -/

namespace Skel.Shape

open Lean Meta Elab Command Skel.Gen

private def fail {α : Type} (c : Name) (msg : MessageData) : MetaM α :=
  throwError "#stmt_shape {c}: {msg}"

/-- The text of `e`, printed with full names, on one line. -/
private def text (c : Name) (what : String) (e : Expr) : MetaM Src := do
  let f ← withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.structureInstances false) (ppExpr e)
  match Src.parse (f.pretty 1000000) with
  | some s => pure s
  | none => fail c s!"the {what} prints as blank text"

/-- The width that the constructor `e` names. -/
private def widthOf (c : Name) (what : String) (e : Expr) : MetaM Width := do
  match (← whnfR e).constName? with
  | some ``Width.W8 => pure .W8
  | some ``Width.W16 => pure .W16
  | some ``Width.W32 => pure .W32
  | some ``Width.W64 => pure .W64
  | _ => fail c m!"the {what} is not a width constructor: {e}"

/-- The elements of a list that is written out (`List.cons` and `List.nil`), or that unfolds to one: each tail is reduced with
`whnfD` (default transparency and limits), so a definition `args a b c` and `args x ++ [f]` give their elements. A list that does
not reduce to `List.cons` and `List.nil` (a stuck term, such as `List.replicate n f` with a variable `n`) has none. The elements are
the terms of the list as it reduces: a list that is written out is read as it is. -/
private partial def listElems (e : Expr) : MetaM (Option (List Expr)) := do
  let e ← whnfD e
  if e.isAppOfArity ``List.nil 1 then pure (some [])
  else if e.isAppOfArity ``List.cons 3 then
    pure ((← listElems e.appArg!).map (e.appFn!.appArg! :: ·))
  else pure none

/-- A variable of the statement, as a binder. -/
private def binderOf (c : Name) (d : LocalDecl) : MetaM ShapeBinder := do
  let some name := Ident.parse d.userName.toString
    | fail c m!"the variable {d.userName} has a name that is not an identifier"
  pure ⟨name, ← text c s!"type of {d.userName}" d.type⟩

/-- The function `f` of the call: its text, its stack room and its result width, from the term `f` that the program
unfolds to `Fn.mk code entry room ret`. -/
private def fnOf (c : Name) (f : Expr) : MetaM FnShape := do
  let u ← whnfD f
  unless u.isAppOfArity ``Lift.Trusted.Fn.mk 4 do
    fail c m!"the function {f} does not unfold to Fn.mk"
  let some room ← evalNat u.appFn!.appArg!
    | fail c m!"the stack room of {f} is not a number"
  pure ⟨← text c "function" f, room, ← widthOf c "result width" u.appArg!⟩

/-- The form of the value `v` of a field of the width `w`: `nat t` when `v` is the application `BitVec.ofNat 64 t` (a 64-bit
field), else `bv`. `BitVec.ofNat 64 t + 1` is an application of `HAdd.hAdd`, so it is `bv`. -/
private def formOf (c : Name) (w : Width) (v : Expr) : MetaM ArgForm := do
  if w == .W64 && v.isAppOfArity ``BitVec.ofNat 2 then
    match ← evalNat v.appFn!.appArg! with
    | some 64 => pure (.nat (← text c "argument" v.appArg!))
    | _ => pure .bv
  else pure .bv

/-- One argument `Field.mk w v`; a term that is no application of `Field.mk` is reduced with `whnfD` first. -/
private def argOf (c : Name) (a : Expr) : MetaM ArgShape := do
  let a ← if a.isAppOfArity ``Lift.Trusted.Field.mk 2 then pure a else whnfD a
  unless a.isAppOfArity ``Lift.Trusted.Field.mk 2 do
    fail c m!"the argument {a} is not of the form Field.mk w v"
  let w ← widthOf c "argument width" a.appFn!.appArg!
  pure ⟨w, ← text c "argument" a.appArg!, ← formOf c w a.appArg!⟩

/-- The form of the body of the statement, with its stack arguments (the terms `g` and `h` of `Call8`). -/
private inductive Head where
  | call
  | callB
  | call8 (g h : Expr)
  | call8B (g h : Expr)

/-- The last component of the name `n` is `Call8`. -/
private def isCall8 (n : Name) : Bool := match n with | .str _ "Call8" => true | _ => false

/-- The stack argument `g` of `Call8`: a term of the type `BitVec 64` (the word at `rsp + 8` or `rsp + 16`). -/
private def stackArgOf (c : Name) (g : Expr) : MetaM ArgShape := do
  let ty ← whnfR (← inferType g)
  match ty.isAppOfArity ``BitVec 1, ← evalNat ty.appArg! with
  | true, some 64 => pure ⟨.W64, ← text c "stack argument" g, ← formOf c .W64 g⟩
  | _, _ => fail c m!"the stack argument {g} has the type {ty}, not BitVec 64"

/-- The call form and the four terms of the body `f args objs post`. The forms are `Fn.Call`, `Fn.CallB` and `Call8 f args g h
objs post` (a constant named `Call8` whose definition has `Fn.Entry` and `Fn.Return`, with two stack arguments `g` and `h`). Any
other number of stack arguments is an error. -/
private def callOf (c : Name) (body : Expr) : MetaM (Head × Expr × Expr × Expr × Expr) := do
  let args := body.getAppArgs.toList
  if body.isAppOfArity ``Lift.Trusted.Fn.Call 4 then
    let [f, a, o, p] := args | fail c "the body is not Fn.Call f args objs post"
    pure (.call, f, a, o, p)
  else if body.isAppOfArity ``Lift.Trusted.Fn.CallB 4 then
    let [f, a, o, p] := args | fail c "the body is not Fn.CallB f args objs post"
    pure (.callB, f, a, o, p)
  else if body.isAppOfArity ``Lift.Trusted.Fn.Call8B 6 then
    let [f, a, g, h, o, p] := args | fail c "the body is not Fn.Call8B f args g h objs post"
    pure (.call8B g h, f, a, o, p)
  else match body.getAppFn.constName? with
    | some n =>
      if isCall8 n then
        let some v := (← getEnv).find? n >>= (·.value?)
          | fail c m!"{n} has no definition"
        unless (v.find? (·.isConstOf ``Lift.Trusted.Fn.Entry)).isSome && (v.find? (·.isConstOf ``Lift.Trusted.Fn.Return)).isSome do
          fail c m!"{n} is named Call8 but is not the call form: its definition has no Fn.Entry and no Fn.Return"
        match args with
        | f :: a :: rest@(_ :: _ :: _) =>
          let stack := rest.dropLast.dropLast
          let [g, h] := stack
            | fail c m!"the form Call8 has 2 stack arguments, {n} has {stack.length}"
          pure (.call8 g h, f, a, rest.dropLast.getLast!, rest.getLast!)
        | _ => fail c m!"the body is not {n} f args g h objs post"
      else fail c m!"the body is not Fn.Call f args objs post, Fn.CallB f args objs post or Call8 f args g h objs post: {body}"
    | none => fail c m!"the body is not Fn.Call f args objs post, Fn.CallB f args objs post or Call8 f args g h objs post: {body}"

/-- The function `run` of L3 that `post` names: the constant at the head of the left side of the first equation
`f … = some y` in the body of `post` (`∃ y, run x = some y ∧ …`). `post` is a constant applied to some variables: its definition
is opened (a `post` that is no constant, such as `fun _ _ _ => True`, is read as it is). None when the body has no such
equation: the shape has no `run`, and `StmtShape.runConst` takes the module of `C`. -/
private def runOf (post : Expr) : MetaM (Option Src) := do
  let env ← getEnv
  let body := match post.getAppFn.constName?.bind (fun c => (env.find? c).bind (·.value?)) with
    | some v => v
    | none => post
  let eq? := body.find? fun e =>
    e.isAppOfArity ``Eq 3 && (e.getArg! 2).isAppOf ``Option.some && (e.getArg! 1).getAppFn.isConst
  pure (eq?.bind fun e => (e.getArg! 1).getAppFn.constName?.bind fun n => Src.parse n.toString)

/-- The term `t` of the conjunct `Encode.encode t = [r]` of the body of `post`, with `r` the result field (the second parameter of
`post` after the variables that it has applied). `post` is opened with its arguments (`unfoldDefinition?`), as the statement
applies it. None when there is no such conjunct, or `t` is bound in `post` (`∃ y, … Encode.encode y = [r]`). The term is in the
variables of the statement: `(run cells i pos mode).1` for the statements with no contract and no `run`. -/
private def resultOf (c : Name) (post : Expr) : MetaM (Option Src) := do
  let p ← match post.getAppFn with
    | .const .. => pure ((← unfoldDefinition? post).getD post)
    | _ => pure post
  lambdaTelescope p fun ps body => do
    let some r := ps[1]? | pure none
    let isResult (e : Expr) : Bool :=
      e.isAppOfArity ``Eq 3 && (e.getArg! 1).isAppOfArity ``Lift.Trusted.Encode.encode 3
        && (e.getArg! 2).isAppOfArity ``List.cons 3 && (e.getArg! 2).appFn!.appArg! == r
        && (e.getArg! 2).appArg!.isAppOfArity ``List.nil 1
    match body.find? isResult with
    | none => pure none
    | some e =>
      let t := (e.getArg! 1).appArg!
      if t.hasLooseBVars then pure none else some <$> text c "result" t

/-- Open existential witnesses until the variable returned by the run is found. -/
private partial def withRunResultBody {α : Type} (ps witnesses : Array Expr) (body : Expr)
    (f : Array Expr → Array Expr → Expr → Expr → MetaM α) : MetaM (Option α) := do
  let some ex := body.find? (·.isAppOfArity ``Exists 2) | pure none
  lambdaTelescope ex.appArg! fun ys inner => do
    let some y := ys[0]? | pure none
    let hasRun := (inner.find? fun e =>
      e.isAppOfArity ``Eq 3 && (e.getArg! 2).isAppOf ``Option.some && (e.getArg! 2).appArg! == y).isSome
    if hasRun then some <$> f ps witnesses y inner
    else withRunResultBody ps (witnesses.push y) inner f

/-- Open the post parameters, the preceding witnesses, and the existential run result for `f`.
The local expressions are used only within `f`. -/
def withRunResultInfo {α : Type} (post : Expr)
    (f : Array Expr → Array Expr → Expr → Expr → MetaM α) : MetaM (Option α) := do
  let p ← match post.getAppFn with
    | .const .. => pure ((← unfoldDefinition? post).getD post)
    | _ => pure post
  lambdaTelescope p fun ps body => withRunResultBody ps #[] body f

/-- Open the existential run result while keeping the witness expressions inside the callback. -/
def withRunResult {α : Type} (post : Expr) (f : Array Expr → Expr → Expr → MetaM α) : MetaM (Option α) :=
  withRunResultInfo post fun ps _ y inner => f ps y inner

/-- Keep the actual run application in the statement context. Post-local parameters and
existential witnesses cannot escape into a functional return premise. -/
private def runCallOf (c : Name) (post : Expr) : MetaM (Option Src) := do
  return (← withRunResultInfo post fun ps witnesses y inner => do
    let some eq := inner.find? fun e =>
      e.isAppOfArity ``Eq 3 && (e.getArg! 2).isAppOf ``Option.some && (e.getArg! 2).appArg! == y
      | pure none
    let call := eq.getArg! 1
    if call.hasLooseBVars || (ps ++ witnesses.push y).any (fun p => call.containsFVar p.fvarId!) then return none
    some <$> text c "run application" call).bind id

/-- A field equation can use `Encode.encode t = [r]` or state the result field directly, in either order. -/
private def fieldValue? (r e : Expr) : Option Expr := do
  guard (e.isAppOfArity ``Eq 3)
  let lhs := e.getArg! 1
  let rhs := e.getArg! 2
  if lhs.isAppOfArity ``Lift.Trusted.Encode.encode 3 && rhs.isAppOfArity ``List.cons 3 &&
      rhs.appFn!.appArg! == r && rhs.appArg!.isAppOfArity ``List.nil 1 then
    some lhs.appArg!
  else if lhs == r && rhs.isAppOfArity ``Lift.Trusted.Field.mk 2 then some rhs.appArg!
  else if rhs == r && lhs.isAppOfArity ``Lift.Trusted.Field.mk 2 then some lhs.appArg!
  else none

/-- The encoded result term as a function of the existential result of `post`. Identity and first-field
projections use the existing result forms; other terms keep their typed lambda and statement variables. -/
private def resultFnOf (c : Name) (post : Expr) : MetaM (Option Src) := do
  return (← withRunResultInfo post fun ps witnesses y inner => do
      let some r := ps[1]? | pure none
      let some eq := inner.find? (fun e => (fieldValue? r e).isSome) | pure none
      let some t := fieldValue? r eq | pure none
      if t.hasLooseBVars || t == y then return none
      let ty ← inferType y
      if ty.hasLooseBVars || (ps ++ witnesses).any (fun p =>
          t.containsFVar p.fvarId! || ty.containsFVar p.fvarId!) then return none
      let env ← getEnv
      let first : Bool := match t with
        | .proj _ 0 v => v == y
        | _ => match t.getAppFn.constName? with
          | some n => (env.getProjectionFnInfo? n).any fun info => info.i == 0 && t.appArg! == y
          | none => false
      if first then return none
      some <$> text c "result function" (← mkLambdaFVars #[y] t)).bind id

/-- The type of the existential run result, including heap and direct-value posts. -/
private def runResultTypeOf (c : Name) (post : Expr) : MetaM (Option Src) := do
  return (← withRunResultInfo post fun ps witnesses y _ => do
    let ty ← inferType y
    if (ps ++ witnesses).any (fun p => ty.containsFVar p.fvarId!) then return none
    some <$> text c "run result type" ty).bind id

private def l3FormOf (post : Expr) : MetaM L3Form := do
  return (← withRunResultInfo post fun _ witnesses _ _ => pure
    (if witnesses.isEmpty then L3Form.functional else .post)).getD .functional

/-- The direct conjuncts, with nested conjunctions flattened in source order. -/
private partial def conjuncts (e : Expr) : List Expr :=
  if e.isAppOfArity ``And 2 then conjuncts (e.getArg! 0) ++ conjuncts (e.getArg! 1) else [e]

/-- The output objects as a typed function of the run result. Objects can use statement variables and the result;
post-local policy, result-field and memory variables cannot escape their scope. Other forms of `Mem.has` have no mapping. -/
private def runOutputObjsOf (c : Name) (post : Expr) : MetaM (Option Src) := do
  return (← withRunResultInfo post fun ps witnesses y inner => do
    let some policy := ps[0]? | pure none
    let some memory := ps[2]? | pure none
    let parts := conjuncts inner
    let hasMem (e : Expr) := (e.find? (·.isAppOfArity ``Lift.Trusted.Mem.has 3)).isSome
    let direct := parts.filter (·.isAppOfArity ``Lift.Trusted.Mem.has 3)
    if direct.isEmpty || parts.any (fun e => hasMem e && !e.isAppOfArity ``Lift.Trusted.Mem.has 3) then
      return none
    unless direct.all (fun e => e.getArg! 0 == policy && e.getArg! 1 == memory) do return none
    let objs := direct.map (·.getArg! 2)
    let objList ← mkListLit (mkConst ``Lift.Trusted.Object) objs
    let ty ← inferType y
    if (ps ++ witnesses).any (fun p => objList.containsFVar p.fvarId! || ty.containsFVar p.fvarId!) then return none
    let f ← mkLambdaFVars #[y] objList
    withOptions (fun o => o.setBool `pp.funBinderTypes true) do
      some <$> text c "run output objects" f).bind id

/-- The variable `d` is a binder form that the reader knows: an explicit or an implicit binder. -/
private def checkBinder (c : Name) (d : LocalDecl) : MetaM Unit := do
  match d.binderInfo with
  | .default | .implicit => pure ()
  | .instImplicit => fail c m!"the variable {d.userName} is an instance binder, a form that the reader does not know"
  | .strictImplicit =>
    fail c m!"the variable {d.userName} is a strict-implicit binder, a form that the reader does not know"

/-! ## The L3 text (HARNESS-LOOP D4) -/

/-- The most declarations of an L3 text. -/
def l3TextMax : Nat := 40

/-- The package of a module: its first two components (`Lift.Pilot` for `Lift.Pilot.ClosestCopyStatement`). -/
def packageOf (m : Name) : Name :=
  (m.components.take 2).foldl (fun acc c => acc ++ c) .anonymous

/-- The module of the constant `n`, if it is imported. -/
private def moduleOfConst (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- Whether the L3 text has the constant `n`: a definition (no instance, no matcher, no projection, no internal name) or an
inductive type of a module of the package `pkg`. -/
private def l3Kept (env : Environment) (pkg : Name) (n : Name) : Bool :=
  !n.isInternal && !isInstanceCore env n && !isMatcherCore env n && !env.isProjectionFn n &&
    ((moduleOfConst env n).any pkg.isPrefixOf) &&
    match env.find? n with
    | some (.defnInfo _) | some (.inductInfo _) => true
    | _ => false

/-- The constants of the L3 text: the constants that `roots` name and that `l3Kept` keeps, then the constants that their types and
values name, in the order found (a queue), each once, at most `l3TextMax`. `fuel` bounds the visits. -/
def l3Consts (pkg : Name) (roots : List Expr) : MetaM (List Name) := do
  let env ← getEnv
  let rec go : Nat → List Name → List Name → List Name
    | 0, _, found => found
    | _ + 1, [], found => found
    | fuel + 1, n :: queue, found =>
      if found.contains n || !l3Kept env pkg n || found.length ≥ l3TextMax then go fuel queue found
      else
        let used := match env.find? n with
          | some ci => (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]).toList
          | none => []
        go fuel (queue ++ used) (found ++ [n])
  pure (go 10000 (roots.flatMap (·.getUsedConstants.toList)) [])

/-- The source text of the declaration `n`: its lines in the file of its module, a path below the working directory
(`Lift/Pilot/Slot.lean` for `Lift.Pilot.Slot`). None when the module, the range or the file is missing. -/
def declSource (n : Name) : MetaM (Option String) := do
  let some m := moduleOfConst (← getEnv) n | return none
  let some r ← findDeclarationRanges? n | return none
  let file := (System.mkFilePath (m.components.map (·.toString))).addExtension "lean"
  let text ← try IO.FS.readFile file catch _ => return none
  let lines := text.splitOn "\n"
  pure (some ("\n".intercalate ((lines.drop (r.range.pos.line - 1)).take (r.range.endPos.line + 1 - r.range.pos.line))))

/-! ## Full names in the L3 text (HARNESS-LOOP3)

The source text of a declaration names constants as its namespace and its `open` lines let it (`eql`, `none64`, `Slot.word`).
The check and refute files have other namespaces open, so `l3TextOf` writes each name of a constant of the project in the code
of the text with its full name. A comment and a string do not change. -/

/-- The pieces of a Lean text: code identifiers (`true`) and the text between them (`false`), in order. An identifier is not
in a comment or a string and does not follow a `.` or an identifier character (`.ok`, `x.f` stay one piece). Its components
are joined by `.` when the character after the `.` starts a component. -/
partial def identPieces (s : String) : List (Bool × String) :=
  go s.toList ' ' [] []
where
  /-- The rest `cs`, the character before it, the text since the last identifier (reversed) and the pieces so far. -/
  go (cs : List Char) (prev : Char) (other : List Char) (acc : List (Bool × String)) : List (Bool × String) :=
    let flush (acc : List (Bool × String)) := if other.isEmpty then acc else acc ++ [(false, String.ofList other.reverse)]
    match cs with
    | [] => flush acc
    | '-' :: '-' :: rest =>
      let (cmt, after) := rest.span (· != '\n')
      go after '\n' (('-' :: '-' :: cmt).reverse ++ other) acc
    | '/' :: '-' :: rest =>
      let (cmt, after) := block 1 rest []
      go after '/' (('/' :: '-' :: cmt).reverse ++ other) acc
    | '"' :: rest =>
      let (str, after) := string rest []
      go after '"' (('"' :: str).reverse ++ other) acc
    | c :: rest =>
      if isIdFirst c && prev != '.' && !isIdRest prev then
        let (id, after) := ident (c :: rest) []
        go after (id.getLast?.getD c) [] (flush acc ++ [(true, String.ofList id)])
      else go rest c (c :: other) acc
  /-- The text of a block comment up to its end (nested), with the closing marker, and the rest. -/
  block : Nat → List Char → List Char → List Char × List Char
    | _, [], acc => (acc.reverse, [])
    | d, '-' :: '/' :: rest, acc =>
      if d == 1 then (('/' :: '-' :: acc).reverse, rest) else block (d - 1) rest ('/' :: '-' :: acc)
    | d, '/' :: '-' :: rest, acc => block (d + 1) rest ('-' :: '/' :: acc)
    | d, c :: rest, acc => block d rest (c :: acc)
  /-- The text of a string up to its closing quote, with it, and the rest. -/
  string : List Char → List Char → List Char × List Char
    | [], acc => (acc.reverse, [])
    | '\\' :: c :: rest, acc => string rest (c :: '\\' :: acc)
    | '"' :: rest, acc => (('"' :: acc).reverse, rest)
    | c :: rest, acc => string rest (c :: acc)
  /-- An identifier: its characters, and the rest. -/
  ident : List Char → List Char → List Char × List Char
    | c :: rest, acc =>
      if isIdRest c then ident rest (c :: acc)
      else match c, rest with
        | '.', d :: _ => if isIdFirst d then ident rest ('.' :: acc) else (acc.reverse, c :: rest)
        | _, _ => (acc.reverse, c :: rest)
    | [], acc => (acc.reverse, [])

/-- The text `s` with each code identifier given its full name by `full`. `full` gets the components of the identifier and
gives the full name of its longest prefix that names a constant, with the number of components of that prefix; the components
after the prefix stay (`junk.kind` is the constant `junk` and the field `kind`). -/
def qualifyText (full : List String → Option String) (s : String) : String :=
  String.join <| (identPieces s).map fun (isId, t) =>
    if !isId then t else
    let parts := t.splitOn "."
    match (List.range parts.length).reverse.findSome? fun k =>
        (full (parts.take (k + 1))).map fun f => (f, parts.drop (k + 1)) with
    | some (f, rest) => ".".intercalate (f :: rest)
    | none => t

/-- Whether the components `ps` are the last components of the name `n`. -/
def isSuffixName (ps : List String) (n : Name) : Bool :=
  let cs := n.components.map (·.toString)
  ps.length ≤ cs.length && cs.drop (cs.length - ps.length) == ps

/-- The full name that `ps` names among the constants `cs`: the one constant whose last components are `ps`, when it is not
`ps` itself; none when no constant or two constants have them. -/
def fullAmong (cs : List Name) (ps : List String) : Option String :=
  match cs.filter (isSuffixName ps) with
  | [n] => if n.components.length == ps.length then none else some n.toString
  | _ => none

/-- The constants of the project that the declaration `n` names, with `n`: those of its type, its value and the types of its
constructors, from a module whose first component is the first component of the module of `n` (`Lift`). A constant of the
core library (`Option.some`) keeps its name; an internal name is not one. -/
def projectConsts (n : Name) : MetaM (List Name) := do
  let env ← getEnv
  let root := ((moduleOfConst env n).map (·.getRoot)).getD n.getRoot
  let used (ci : ConstantInfo) := ci.type.getUsedConstants.toList ++ ((ci.value?.map (·.getUsedConstants.toList)).getD [])
  let ctors := match env.find? n with
    | some (.inductInfo i) => i.ctors.filterMap env.find?
    | _ => []
  let all := n :: ((env.find? n).map used).getD [] ++ ctors.flatMap used
  pure (all.eraseDups.filter fun c => !c.isInternal && ((moduleOfConst env c).map (·.getRoot)) == some root)

/-- The source text of the declaration `n` with full names (`qualifyText` with `projectConsts`). -/
def fullSource (n : Name) : MetaM (Option String) := do
  let some src ← declSource n | return none
  let cs ← projectConsts n
  pure (some (qualifyText (fullAmong cs) src))

/-- The L3 text of the statement `c` with the terms `roots` (the contract, the objects, `post`): the source text of each
constant of `l3Consts` for the package of the module of `c`, in order, with full names (`fullSource`), a text that an
earlier text holds dropped. -/
def l3TextOf (c : Name) (roots : List Expr) : MetaM String := do
  let some m := moduleOfConst (← getEnv) c | return ""
  let ns ← l3Consts (packageOf m) roots
  let texts ← ns.filterMapM fullSource
  let kept := texts.foldl (fun acc t => if acc.any (fun a => (a.splitOn t).length > 1) then acc else acc ++ [t]) []
  pure ("\n\n".intercalate kept)

/-- The shape of the statement `c`. -/
def readShape (c : Name) : MetaM StmtShape := do
  let some ci := (← getEnv).find? c | fail c "there is no such constant"
  let some v := ci.value? | fail c "it has no value (it is not a definition)"
  unless ci.type.isProp && ci.levelParams.isEmpty do
    fail c "it is not a definition of a proposition with no universe parameter"
  forallTelescope v fun xs body => do
    let decls ← xs.toList.mapM (·.fvarId!.getDecl)
    decls.forM (checkBinder c)
    let tagged ← decls.mapM fun d => do pure (d, ← isProp d.type)
    -- the variables before the first hypothesis are the inputs, that hypothesis is the contract
    let (inputs, contract, contractE, rest) ← match tagged.span (fun (_, p) => !p) with
      | (pre, (hd, _) :: rest) => pure (pre, ← text c "contract" hd.type, hd.type, rest)
      | (pre, []) => pure ([], ⟨"True", by decide⟩, mkConst ``True, pre)
    let (head, f, args, objs, post) ← callOf c body
    let some argList ← listElems args
      | fail c m!"the arguments are not a list that is written out, and do not unfold to one: {args}"
    let argShapes ← argList.mapM (argOf c)
    let call ← match head with
      | .call => pure CallForm.call
      | .callB => pure CallForm.callB
      | .call8 g h =>
        unless argShapes.length == 6 do
          fail c m!"the form Call8 has 6 register arguments, the list has {argShapes.length}"
        pure (CallForm.call8 (← stackArgOf c g) (← stackArgOf c h))
      | .call8B g h =>
        unless argShapes.length == 6 do
          fail c m!"the form Call8B has 6 register arguments, the list has {argShapes.length}"
        pure (CallForm.call8B (← stackArgOf c g) (← stackArgOf c h))
    let run ← runOf post
    let runCall ← runCallOf c post
    let projectedResult ← resultFnOf c post
    pure
      { inputs := ← inputs.mapM fun (d, _) => binderOf c d
        contract
        binders := ← (rest.filter (!·.2)).mapM fun (d, _) => binderOf c d
        hyps := ← (rest.filter (·.2)).mapM fun (d, _) => text c "hypothesis" d.type
        fn := ← fnOf c f
        args := argShapes
        objs := ← text c "objects" objs
        post := ← text c "post" post
        run
        runCall
        result := ← match run with
          | none => resultOf c post
          | some _ => pure none
        call
        resultFn := projectedResult
        runResultType := ← runResultTypeOf c post
        runOutputObjs := ← runOutputObjsOf c post
        l3Form := ← if run.isSome && runCall.isNone then pure .post else l3FormOf post
        l3Text := ← l3TextOf c [contractE, objs, post] }

/-- `#stmt_shape name` prints the JSON of the shape of the statement `name`. -/
syntax (name := stmtShape) "#stmt_shape " ident : command

@[command_elab stmtShape] def elabStmtShape : CommandElab
  | `(#stmt_shape $id) => do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let s ← liftTermElabM (readShape c)
    logInfo (StmtShape.toJson s).compress
  | _ => throwUnsupportedSyntax

end Skel.Shape
