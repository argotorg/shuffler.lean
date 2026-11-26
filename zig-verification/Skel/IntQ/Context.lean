import Lean
import Skel.Discover.Smt.Rung

/-! The type context of a proposed internal statement (task INT-Q2), found by elaboration.

The walk starts at the model function of a target and at the types of the holes of the template (`holeRoots`). It goes from
a constant to the constants of its type and of its value (a definition) or of its constructors (an inductive type), for at
most `depth` steps; a name that is an internal detail (`match_1`, `_proof_2`) does not count as a step. It keeps only the
constants of the modules of the repository (the root `Lift`), and none of a module of the deny list of `leantools.json`.

Of the constants that the walk reaches, the context has the types (inductive types with their fields or constructors, and
definitions of a type), the values (definitions that are not functions), the instances, and the signatures of the functions
that the model calls. It also has each `Encode` instance in the imports of the statement, and the binders and the result type
of the model function, each type with its fully qualified names (`pp.fullNames`). -/

namespace Skel.IntQ

open Lean Meta

/-- A parameter of the model function: the name, the type text (fully qualified names) and whether it is implicit. -/
structure Param where
  names : List String
  type : String
  implicit : Bool
  deriving BEq, Repr

/-- What the context has of a constant. -/
inductive Kind where
  /-- An inductive type or structure, or a definition of a type. -/
  | type
  /-- A definition that is not a function. -/
  | value
  /-- An instance. -/
  | inst
  /-- A function that the model calls (its signature only). -/
  | callee
  deriving BEq, Repr

/-- A constant of the context: the fully qualified name, the module, `name : type`, the fields (a structure) or the
constructors (an inductive type) as `name : type`, the lines of its declaration, and the source text of those lines. -/
structure Entry where
  name : String
  kind : Kind
  module : String
  sig : String
  members : List String
  lines : Option (Nat × Nat)
  text : String := ""
  deriving Repr

/-- The type context of one target. -/
structure TypeCtx where
  model : String
  params : List Param
  ret : String
  entries : List Entry
  encodes : List String
  depth : Nat
  deriving Repr

/-- The types of the holes of the template: the walk starts at them too. -/
def holeRoots : List Name :=
  [`Lift.Trusted.Field, `Lift.Trusted.Object, `Lift.Trusted.Encode, `Lift.Shuffler.Internal.Proposed.Layout.Env]

/-- The module of a source path (`Lift/Shuffler/Fuel.lean` is `Lift.Shuffler.Fuel`). -/
def moduleOfFile (p : String) : String := ((p.splitOn ".lean").headD p).replace "/" "."

/-- The source path of a module. -/
def fileOfModule (m : String) : String := m.replace "." "/" ++ ".lean"

/-- The module of a constant. -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?

/-- A constant of the repository (root `Lift`), not of a denied module. -/
def keepIn (env : Environment) (deny : List String) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => m.getRoot == `Lift && !deny.contains m.toString
  | none => false

/-- The constants that a constant refers to: those of its type, and of its value (a definition) or of its constructors (an
inductive type). An instance and a theorem refer to the constants of their types only. -/
def refs (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let ofType := ci.type.getUsedConstants
    match ci with
    | .defnInfo d => if isInstanceCore env n then ofType else ofType ++ d.value.getUsedConstants
    | .inductInfo i => ofType ++ i.ctors.toArray
    | _ => ofType

/-- The walk: the constants that `keep` accepts and that the roots reach in at most `depth` steps (a name that is an
internal detail is no step). Breadth first, so a constant gets its largest number of steps left. -/
partial def walk (env : Environment) (keep : Name → Bool) (roots : List Name) (depth : Nat) : List Name :=
  go (roots.filter keep |>.map (·, depth)) [] {} []
where
  go (cur next : List (Name × Nat)) (seen : NameSet) (acc : List Name) : List Name :=
    match cur, next with
    | [], [] => acc.reverse
    | [], next => go next.reverse [] seen acc
    | (n, d) :: rest, next =>
      if seen.contains n then go rest next seen acc
      else
        let seen := seen.insert n
        let more := if d == 0 then [] else
          (refs env n).toList.filter (fun m => keep m && !seen.contains m) |>.map fun m =>
            (m, if m.isInternalDetail then d else d - 1)
        go rest (more.reverse ++ next) seen (n :: acc)

/-- The modules that the modules `ms` import, `ms` with them. -/
partial def closure (env : Environment) (ms : List Name) : NameSet :=
  go ms {}
where
  go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | m :: rest =>
      if seen.contains m then go rest seen
      else
        let deps := match env.header.moduleNames.idxOf? m with
          | some i => (env.header.moduleData[i]?.map fun d => d.imports.toList.map (·.module)).getD []
          | none => []
        go (deps ++ rest) (seen.insert m)

/-- The text of `e` with fully qualified names. -/
def ppFull (e : Expr) : MetaM String :=
  withOptions (fun o => o.setBool `pp.fullNames true) do
    return toString (← ppExpr e)

/-- `name : type`, fully qualified. -/
def sigOf (n : Name) : MetaM String := do
  return s!"{n} : {← ppFull (← getConstInfo n).type}"

/-- The fields of a structure as `S.f : T`, or the constructors of an inductive type as `C : T`. -/
def membersOf (n : Name) : MetaM (List String) := do
  let env ← getEnv
  if isStructure env n then
    let ctor := (getStructureCtor env n).name
    forallTelescope (← getConstInfo ctor).type fun xs _ => do
      let params := xs.size - (getStructureFields env n).size
      (xs.toList.drop params).mapM fun x => do
        return s!"{n}.{(← x.fvarId!.getUserName)} : {← ppFull (← inferType x)}"
  else match env.find? n with
    | some (.inductInfo i) => i.ctors.mapM sigOf
    | _ => pure []

/-- The kind of a constant of the walk in the context, or none (a constructor, a field, a recursor, an internal detail, a
theorem, or the model function itself). -/
def kindOf (model n : Name) : MetaM (Option Kind) := do
  let env ← getEnv
  if n == model || n.isInternalDetail then return none
  if isInstanceCore env n then return some .inst
  match env.find? n with
  | some (.inductInfo _) => return some .type
  | some (.defnInfo d) =>
    if (env.getProjectionFnInfo? n).isSome then return none
    forallTelescopeReducing d.type fun xs body => do
      if body.isSort then return some .type
      if ← isProp d.type then return none
      return some (if xs.isEmpty then .value else .callee)
  | some (.opaqueInfo _) => return some .value
  | _ => return none

/-- The entry of a constant of the walk, or none. -/
def entryOf (model n : Name) : MetaM (Option Entry) := do
  let some k ← kindOf model n | return none
  let env ← getEnv
  let lines := (← findDeclarationRanges? n).map fun r => (r.range.pos.line, r.range.endPos.line)
  let members ← if k == .type then membersOf n else pure []
  return some { name := n.toString, kind := k, module := ((moduleOf env n).getD .anonymous).toString, sig := ← sigOf n,
                members, lines }

/-- The `Encode` instances in the modules `mods`: `name : type`. -/
def encodesIn (mods : NameSet) : MetaM (List String) := do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n ci =>
    if isInstanceCore env n && ci.type.getForallBody.getAppFn.constName? == some `Lift.Trusted.Encode &&
        ((moduleOf env n).map mods.contains).getD false then acc.push n else acc
  (names.qsort (·.toString < ·.toString)).toList.mapM sigOf

/-- The binders and the result type of the model function, fully qualified. -/
def paramsOf (model : Name) : MetaM (List Param × String) := do
  forallTelescope (← getConstInfo model).type fun xs body => do
    let ps ← xs.toList.mapM fun x => do
      let d ← x.fvarId!.getDecl
      return ({ names := [d.userName.toString], type := ← ppFull d.type, implicit := !d.binderInfo.isExplicit } : Param)
    return (ps, ← ppFull body)

/-- The type context of the model function `model` for a statement with the imports `imports`. -/
def typeCtxM (deny : List String) (depth : Nat) (model : Name) (imports : List Name) : MetaM TypeCtx := do
  let env ← getEnv
  unless env.contains model do throwError "no constant {model}"
  let names := walk env (keepIn env deny) (model :: holeRoots) depth
  let entries ← names.filterMapM (entryOf model)
  let (params, ret) ← paramsOf model
  return { model := model.toString, params, ret, entries, encodes := ← encodesIn (closure env imports), depth }

/-- The lines `[a, b]` (from 1) of a text. -/
def linesOf (src : String) (a b : Nat) : String := "\n".intercalate (((src.splitOn "\n").drop (a - 1)).take (b + 1 - a))

/-- The entry with the source text of its lines, read from the file of its module. -/
def Entry.withText (e : Entry) : IO Entry := do
  let some (a, b) := e.lines | return e
  let f : System.FilePath := fileOfModule e.module
  if !(← f.pathExists) then return e
  return { e with text := linesOf (← IO.FS.readFile f) a b }

/-- The modules of the deny list of `leantools.json` (the `.lean` paths of `deny`). -/
def denyModules : IO (List String) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "leantools.json"))
  let paths := (j.getObjValAs? (List String) "deny").toOption.getD []
  return (paths.filter (·.endsWith ".lean")).map moduleOfFile

/-- The type contexts of the requests `(model, imports)`, in one environment of all the imports. -/
def typeCtxs (reqs : List (String × List String)) (depth : Nat) : IO (Except String (List TypeCtx)) := do
  let deny ← denyModules
  let imports := (reqs.flatMap (·.2)).eraseDups
  let r ← Skel.Discover.Smt.Rung.inEnv imports do
    try
      return .ok (← reqs.mapM fun (m, is) => typeCtxM deny depth m.toName (is.map (·.toName)))
    catch e => return .error (← e.toMessageData.toString)
  match r with
  | .error e => return .error e
  | .ok tcs => return .ok (← tcs.mapM fun tc => do pure { tc with entries := ← tc.entries.mapM Entry.withText })

/-- The section of the prompt: the types with their fields or constructors and their source, the values, the instances,
the `Encode` instances and the signatures of the callees. A higher `level` gives a shorter text: 1 leaves out the source of
a type with fields or constructors, 2 the source of each type, 3 the callees and the instances (not the `Encode` instances).
The fully qualified fields, constructors and `Encode` instances are in the text at each level. -/
def TypeCtx.render (tc : TypeCtx) (level : Nat := 0) : String :=
  let of (k : Kind) := tc.entries.filter (·.kind == k)
  let src (e : Entry) : List String :=
    if e.text.isEmpty || level ≥ 2 || (level ≥ 1 && !e.members.isEmpty) then [] else ["```lean", e.text, "```"]
  let types := (of .type).flatMap fun e =>
    [s!"### `{e.name}` (`{fileOfModule e.module}`)", s!"`{e.sig}`"] ++
    (if e.members.isEmpty then [] else "Fields or constructors (fully qualified):" :: e.members.map (s!"- `{·}`")) ++ src e ++ [""]
  let line (e : Entry) := s!"- `{e.sig}` (`{fileOfModule e.module}`)"
  let value (e : Entry) := if e.text.isEmpty || (e.text.splitOn "\n").length > 1 then line e else line e ++ s!": `{e.text.trimAscii}`"
  "\n".intercalate (
    [s!"## The types (by elaboration of `{tc.model}` and of the hole types, {tc.depth} steps; fully qualified names)", ""] ++
    types ++
    ["## The values", ""] ++ (of .value).map value ++ [""] ++
    (if level ≥ 3 then [] else
      ["## The functions that the model calls (signatures)", ""] ++ (of .callee).map line ++ [""] ++
      ["## The instances that the model and its types use", ""] ++ (of .inst).map line ++ [""]) ++
    ["## The `Encode` instances in the imports of the statement (no other type has an `Encode` instance)", ""] ++
    tc.encodes.map (s!"- `{·}`") ++ [""])

end Skel.IntQ
