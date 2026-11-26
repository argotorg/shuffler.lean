import Skel.Discover.Features

/-! The plan of a fueled L3 site for the command `skel discover <fn> --module <M>` (task DISC-FUEL): everything that the
production effects of the ladder (`Ladder.Fueled`) need, read from the definitions, with no hand input.

- the site, its call text and the fuel and entry of its call site: `siteInfoOf?` (`Skel/Discover/Site.lean`);
- the pool, with the callees of the step unfolded, and the callees (the unfolds of the tactics): `poolWith`;
- the fuel feature: the fuel expression as a feature (`featureOfFn`); it is added to the features when the pool lacks it;
- the sampler of the state type (`drawText?`), by the type only: `Nat` from `0` to `7`, `Bool`, `Fin n`, the words, `List`
  and `Array` of length `0` to `4`, `Vector`, `Option`, pairs, the structures, and the inductive types whose constructors
  have no argument. The draw of a part `k` of a value uses the stream `k` of the generator;
- the trace draw: the first of 256 draws that satisfies the entry condition, else the first draw. So the runs of the traces
  start at entry states when the sampler finds them;
- the values of the parameters of the site: one draw of the sampler of each parameter type, at the seed 7;
- whether the state type has `FromJson` (the stored states are injected) and `Repr` or `ToJson` (the search prints a state).

`planOf` runs in `MetaM` in an environment with the module of the function. `planFile` is the Lean file that prints the plan
as one JSON line after the word `PLAN`; the command runs it with `lake env lean`. -/

namespace Skel.Discover.L3

open Lean Meta Skel.Discover

/-- The plan of a fueled L3 site. -/
structure Plan where
  site : LoopSite
  call : String
  features : List Feature
  atoms : List Atom
  fuelFeature : Option Feature
  draw : String
  traceDraw : String
  args : List String
  unfolds : List String
  fromJson : Bool
  deriving ToJson, FromJson

/-- The text of `e` with full names, on one line. -/
private def text (e : Expr) : MetaM String := do
  pure ((← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e)).pretty 1000000)

/-- The words, with their `ofNat`. -/
private def words : List Name := [``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize]

/-- The sampler of the type `ty`, a Lean term of the type `Coordinator.Dst.Rng → ty`, or none for a type that the rules do
not cover. `depth` bounds the nesting of the types. -/
partial def drawText? (ty : Expr) (depth : Nat := 4) : MetaM (Option String) := do
  if depth == 0 then return none
  let ty ← whnfR ty
  let nat := "(g.natIn 0 7).1"
  let part (k : Nat) (d : String) : String := s!"(({d}) (g.stream {k}))"
  let tyText ← text ty
  match ty.getAppFn.constName?, ty.getAppArgs with
  | some ``Nat, #[] => return some s!"fun g => {nat}"
  | some ``Bool, #[] => return some "fun g => (g.natIn 0 1).1 == 1"
  | some ``Fin, #[n] =>
    let some k := (← instantiateMVars n).nat? | return none
    if k == 0 then return none
    return some s!"fun g => (⟨(g.natIn 0 {k - 1}).1 % {k}, Nat.mod_lt _ (by decide)⟩ : Fin {k})"
  | some w, #[] =>
    if words.contains w then return some s!"fun g => {w}.ofNat {nat}" else structure? ty tyText
  | some ``List, #[a] =>
    let some d ← drawText? a (depth - 1) | return none
    return some s!"fun g => (List.range (g.natIn 0 4).1).map (fun k => ({d}) (g.stream (k + 1)))"
  | some ``Array, #[a] =>
    let some d ← drawText? a (depth - 1) | return none
    return some s!"fun g => ((List.range (g.natIn 0 4).1).map (fun k => ({d}) (g.stream (k + 1)))).toArray"
  | some ``Vector, #[a, n] =>
    let some d ← drawText? a (depth - 1) | return none
    return some s!"fun g => (Vector.ofFn (n := {← text n}) (fun k => ({d}) (g.stream (k.val + 1))) : {tyText})"
  | some ``Option, #[a] =>
    let some d ← drawText? a (depth - 1) | return none
    return some s!"fun g => (if (g.natIn 0 3).1 == 0 then none else some ({part 1 d}) : {tyText})"
  | some ``Prod, #[a, b] =>
    let some da ← drawText? a (depth - 1) | return none
    let some db ← drawText? b (depth - 1) | return none
    return some s!"fun g => (({part 0 da}, {part 1 db}) : {tyText})"
  | _, _ => structure? ty tyText
where
  /-- A structure (each field by its type, no proof field), or an inductive type of constructors with no argument. -/
  structure? (ty : Expr) (tyText : String) : MetaM (Option String) := do
    let env ← getEnv
    let some c := ty.getAppFn.constName? | return none
    let some (.inductInfo ii) := env.find? c | return none
    if isStructure env c then
      let fields := getStructureFields env c
      let mut parts : List String := []
      for h : k in [0:fields.size] do
        let f := fields[k]
        let some fty ← (do
            let some proj := env.find? (c ++ f) | pure none
            let pty ← instantiateForall (← inferType (mkConst proj.name (ty.getAppFn.constLevels!)))
              (ty.getAppArgs)
            let .forallE _ _ b _ := pty | pure none
            if b.hasLooseBVars then pure none else pure (some b)) | return none
        if ← isProp fty then return none
        let some d ← drawText? fty (depth - 1) | return none
        parts := parts ++ [s!"{f} := (({d}) (g.stream {k}))"]
      return some s!"fun g => (\{ {", ".intercalate parts} } : {tyText})"
    if ii.ctors.isEmpty || ii.numIndices != 0 then return none
    let mut ctors : List String := []
    for ctor in ii.ctors do
      let some (.ctorInfo ci) := env.find? ctor | return none
      if ci.numFields != 0 then return none
      ctors := ctors ++ [ctor.toString]
    let n := ctors.length
    let alts := (ctors.zipIdx).map fun (cn, k) => if k + 1 == n then s!"| _ => {cn}" else s!"| {k} => {cn}"
    return some s!"fun g => (match (g.natIn 0 {n - 1}).1 with {" ".intercalate alts} : {tyText})"

/-- Whether the class `cls` has an instance at the type `ty`. -/
private def hasInstance (cls : Name) (ty : Expr) : MetaM Bool := do
  try
    let u ← getLevel ty
    let inst ← synthInstance? (mkApp (mkConst cls [← decLevel u]) ty)
    pure inst.isSome
  catch _ => pure false

/-- The plan of the fueled function `fn` (see the head of this file), or the reason that it has none. -/
def planOf (fn : Name) : MetaM (Except String Plan) := do
  match ← siteInfoOf? fn with
  | .error e => pure (.error s!"no site: {(repr e).pretty}")
  | .ok info =>
    let s := info.site
    let (pool, callees) ← poolWith (some fn) info.step
    let fuelFeature ← match info.fuel with
      | some f => featureOfFn f
      | none => pure none
    let features := pool.features.map (·.1)
    let features := match fuelFeature with
      | some f => if features.contains f then features else features ++ [f]
      | none => features
    -- the types of the state and of the parameters, from the step function
    lambdaTelescope info.step fun xs _ => do
      let some st := xs.back? | return .error "a step with no state"
      let σ ← inferType st
      let some draw ← drawText? σ | return .error s!"no sampler for the state type {s.stateTy}"
      unless (← hasInstance ``Repr σ) || (← hasInstance ``ToJson σ) do
        return .error s!"the state type {s.stateTy} has no Repr and no ToJson"
      let mut args : List String := []
      for x in xs.pop do
        let some d ← drawText? (← inferType x) | return .error s!"no sampler for the parameter {← text x}"
        args := args ++ [s!"(({d}) (Coordinator.Dst.Rng.ofSeed 7))"]
      let binders := String.join (s.params.map fun (n, t) => s!"fun ({n} : {t}) => ")
      let applied := String.join (args.map (" " ++ ·))
      let traceDraw := if s.entry == "True" then draw else
        s!"(({binders}fun (g : Coordinator.Dst.Rng) => let base : Coordinator.Dst.Rng → {s.stateTy} := {draw}; " ++
        s!"((List.range 256).map (fun k => base (g.stream (k + 100)))).find? (fun (st : {s.stateTy}) => decide ({s.entry})) " ++
        s!"|>.getD (base g)){applied})"
      pure (.ok { site := s, call := info.call, features, atoms := pool.atoms.map (·.1), fuelFeature, draw, traceDraw,
                  args, unfolds := callees.map (·.toString), fromJson := ← hasInstance ``FromJson σ })

/-- The plan of `fn` as one JSON line: `{"ok": plan}` or `{"error": why}`. -/
def planLine (fn : Name) : MetaM String := do
  match ← planOf fn with
  | .ok p => pure (Json.mkObj [("ok", toJson p)]).compress
  | .error e => pure (Json.mkObj [("error", Json.str e)]).compress

/-- The Lean file that prints the plan of `fn`, with the modules `modules`, after the word `PLAN`. -/
def planFile (modules : List String) (fn : String) : String :=
  "\n".intercalate
    ((["Skel.Discover.L3Plan"] ++ modules).map ("import " ++ ·) ++
      [ "open Lean Meta in",
        s!"#eval show MetaM Unit from do IO.println (\"PLAN \" ++ (← Skel.Discover.L3.planLine `{fn}))", "" ])

/-- The plan of a line of the output of `planFile`. -/
def Plan.ofOutput (out : String) : Except String Plan := do
  let some line := (out.splitOn "\n").find? (·.startsWith "PLAN ")
    | throw s!"no plan in the output: {(out.take 300).toString}"
  let j ← Json.parse (String.ofList (line.toList.drop 5))
  match j.getObjVal? "ok" with
  | .ok p => fromJson? p
  | .error _ => throw ((j.getObjValAs? String "error").toOption.getD "no plan")

end Skel.Discover.L3
