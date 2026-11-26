import Lean
import LeanTools.Policy
import LeanTools.Axioms

/-!
# Validation of a submission against its original

The original is the file with the frozen statements (and `sorry`); the submission is the worker's
file. Both are elaborated as the same module, so that private names agree. The submission is valid
when:

- it elaborates with no errors, with the same imports;
- each declaration of the original is in it with the same kind and type, and each definition with
  the same value (declarations that a proof makes, such as matchers, are not compared);
- each theorem of the original depends on no axioms other than `propext`, `Classical.choice`,
  `Quot.sound`, the axioms of `bv_decide` that the validator checks again,
  and the axioms of the original;
- a theorem `t : T` of the original may be replaced by a disproof `t.disproof : ¬ T`, under the
  same rule for axioms;
- it adds no axioms;
- the kernel accepts all of its declarations again, from the imports alone, so that a declaration
  added without a kernel check (`debug.skipKernelTC`, `addDeclWithoutChecking`) is rejected.
-/

open Lean Elab

namespace LeanTools

structure Verdict where
  problems : Array String
  /-- The theorems of the original: the targets. -/
  theorems : Array Name
  /-- The targets that the submission disproves. -/
  disproved : Array Name := #[]
deriving Repr

structure Elaborated where
  env : Environment
  messages : MessageLog

/-- The module mode and import flags of source text. -/
def headerText (text : String) (fileName : String := "<input>") : IO ModuleHeader := do
  let input := Parser.mkInputContext text fileName
  let (header, _, _) ← Parser.parseHeader input
  return Elab.HeaderSyntax.toModuleHeader header

def headerOf (path : System.FilePath) : IO ModuleHeader := do
  headerText (← IO.FS.readFile path) path.toString

/-- The imports of a file, including import-all, public and meta flags. -/
def importsOf (path : System.FilePath) : IO (Array Import) := do
  return (← headerOf path).imports

/-- The environment after `imports`. A process can import only once, so the caller imports once
and elaborates every file from the result. -/
def importEnv (imports : Array Import) (mainModule : Name := `Submission)
    (isModule : Bool := false) : IO Environment := do
  let level := if isModule then OLeanLevel.exported else .private
  let env ← importModules imports {} (loadExts := true) (level := level)
  return env.setMainModule mainModule

def importFileEnv (path : System.FilePath) (mainModule : Name := `Submission) : IO Environment := do
  let header ← headerOf path
  importEnv header.imports mainModule header.isModule

/-- Elaborates the commands of `path` from `imports`, the environment after its header. -/
def elabFrom (imports : Environment) (path : System.FilePath) : IO Elaborated := do
  let inputCtx := Parser.mkInputContext (← IO.FS.readFile path) path.toString
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  -- The CLI and server enable async elaboration. Use the same mode and heartbeat limit here.
  -- `processCommands` waits for the snapshot tree and collects its async diagnostics.
  let opts := Elab.async.set {} true
  let s ← IO.processCommands inputCtx parserState (Command.mkState imports messages opts)
  return { env := s.commandState.env, messages := s.commandState.messages }

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Declarations that a proof or the elaborator makes as a side product. A reserved name is one that Lean realizes on
demand from the declarations before it (the equation lemmas, and the congruence equations `match_N.congr_eq_K` of a
matcher that `split` realizes); a declaration cannot be given a reserved name by hand. -/
def generated (env : Environment) (thms : NameSet) (n : Name) : Bool :=
  n.isInternalDetail || Meta.isMatcherCore env n || isReservedName env n
    || (n.components.length > 1 && thms.contains n.getPrefix)
    || isAuxRecursor env n || isNoConfusion env n

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def axiomsOf (env : Environment) (n : Name) : IO (Array Name) := do
  let (r, _) ← (collectAxioms n : CoreM _).toIO { fileName := "", fileMap := default } { env }
  return r

def binderCount : Expr → Nat
  | .forallE _ _ body _ => 1 + binderCount body
  | .mdata _ body => binderCount body
  | _ => 0

def describeType (env : Environment) (type : Expr) : IO String := do
  let (doc, _) ← (Meta.ppExpr type).run'.toIO
    { fileName := "", fileMap := default, options := ({} : Options).setBool `pp.explicit true }
    { env }
  return doc.pretty

/-- Lean can reuse a compiler matcher or sparse case function from an earlier helper. Compare
their local bodies in each file's environment. Ordinary definitions and imported constants remain fixed. -/
private partial def expandLocalMatchers (env : Environment)
    (visiting : NameSet) (type : Expr) : Expr :=
  type.replace fun e => do
    let .const name levels := e | none
    guard ((env.getModuleIdxFor? name).isNone)
    guard ((Meta.isMatcherCore env name || isSparseCasesOn env name) && !visiting.contains name)
    let .defnInfo info ← env.find? name | none
    let value := info.value.instantiateLevelParams info.levelParams levels
    return expandLocalMatchers env (visiting.insert name) value

private def sameTermData (original submitted : Environment) (a b : Expr) : Bool :=
  expandLocalMatchers original {} a == expandLocalMatchers submitted {} b

/-- Checks declaration data without evaluating submitted commands. Both environments must
come from the same imports. The kernel replay below checks the submitted declarations. -/
def validateEnvironmentsWith
    (kernelReplay : Std.HashMap Name ConstantInfo → Kernel.Environment → IO Kernel.Environment)
    (imports : Environment) (original submitted : Environment) (scaffold : Bool) : IO Verdict := do
  let local_ (env : Environment) : List (Name × ConstantInfo) :=
    env.constants.map₂.toList.filter fun (n, _) => env.getModuleIdxFor? n |>.isNone
  let origConsts := local_ original
  let thms : NameSet := origConsts.foldl (init := {}) fun acc (n, c) =>
    if c matches .thmInfo _ then acc.insert n else acc
  let theorems := (origConsts.filterMap fun (n, c) =>
    if (c matches .thmInfo _) && !generated original {} n then some n else none).toArray.qsort Name.lt
  let mut problems := if theorems.isEmpty then #["the original has no theorems to prove"] else #[]
  let origAxioms := origConsts.filterMap fun (n, c) => if c matches .axiomInfo _ then some n else none
  let mut disproved := #[]
  for (n, c) in origConsts do
    if generated original thms n then continue
    match submitted.find? n with
    | none =>
      match c, submitted.find? (n ++ `disproof) with
      | .thmInfo _, some d =>
        if sameTermData original submitted (mkNot c.type) d.type then disproved := disproved.push n
        else problems := problems.push s!"{n}.disproof: the type is not the negation of {n}'s"
      | _, _ => problems := problems.push s!"{n} is missing"
    | some c' =>
      if kindOf c != kindOf c' then
        problems := problems.push s!"{n}: the kind differs ({kindOf c} in the original, {kindOf c'} here)"
      else if !sameTermData original submitted c.type c'.type then
        problems := problems.push s!"{n}: the type differs from the original's\noriginal type ({binderCount c.type} binders): {← describeType original c.type}\ncurrent type ({binderCount c'.type} binders): {← describeType submitted c'.type}"
      else if !(c matches .thmInfo _) &&
          (c.value? (allowOpaque := true)).map (expandLocalMatchers original {}) !=
            (c'.value? (allowOpaque := true)).map (expandLocalMatchers submitted {}) then
        problems := problems.push s!"{n}: the value differs from the original's"
  for (n, c) in local_ submitted do
    if (c matches .axiomInfo _) && !origAxioms.contains n && !(checkClaim submitted n).isOk then
      problems := problems.push s!"new axiom {n}"
  for n in theorems do
    let proof := if disproved.contains n then n ++ `disproof else n
    if submitted.contains proof then
      let bad := (← axiomsOf submitted proof).filter fun a =>
        !allowedAxiom submitted a && !origAxioms.contains a && !(scaffold && a == ``sorryAx)
      unless bad.isEmpty do
        problems := problems.push s!"{proof} depends on {", ".intercalate ((bad.qsort Name.lt).toList.map toString)}"
  if scaffold then
    for (n, c) in local_ submitted do
      let bad := (← axiomsOf submitted n).filter fun a =>
        !allowedAxiom submitted a && !origAxioms.contains a && a != ``sorryAx
      unless bad.isEmpty do
        problems := problems.push s!"{n}: forbidden axioms in scaffold: {bad}"
      unless c matches .thmInfo _ do
        if (← axiomsOf submitted n).contains ``sorryAx then
          problems := problems.push s!"{n}: a definition depends on sorryAx"
  let newConsts : Std.HashMap Name ConstantInfo := (local_ submitted).foldl (init := {}) fun m (n, c) => m.insert n c
  try
    let _ ← kernelReplay newConsts imports.toKernelEnv
  catch e =>
    problems := problems.push s!"the kernel rejects the submission: {e}"
  return { problems, theorems, disproved }

/-- Legacy validation keeps Lean's replay as its default. Coordinator callers select
its total traversal through validateEnvironmentsWith. -/
def validateEnvironments (imports : Environment) (original submitted : Environment)
    (scaffold : Bool) : IO Verdict :=
  validateEnvironmentsWith (fun constants env => env.replay constants)
    imports original submitted scaffold

/-- Validates `sub` against `orig`; `imports` is the environment after the original's imports. -/
def validateUsing (imports : Environment) (orig sub : System.FilePath)
    (scaffold : Bool) : IO Verdict := do
  if let some reason ← variablePolicy (← IO.FS.readFile sub) then
    return { problems := #[reason], theorems := #[] }
  let originalHeader ← headerOf orig
  let submittedHeader ← headerOf sub
  if originalHeader.isModule != submittedHeader.isModule then
    return { problems := #["the module mode differs from the original's"], theorems := #[] }
  if originalHeader.imports != submittedHeader.imports then
    return { problems := #["the imports differ from the original's"], theorems := #[] }
  if imports.header.isModule != originalHeader.isModule then
    return { problems := #["the import environment has a different module mode"], theorems := #[] }
  let o ← elabFrom imports orig
  let originalErrors ← o.messages.toList.filterM fun m => return m.severity == .error
  unless originalErrors.isEmpty do
    let ps ← originalErrors.toArray.mapM fun m => do
      return s!"error: {m.pos.line}:{m.pos.column + 1}: frozen original elaboration failed: {(← m.data.toString).trimAscii}"
    return { problems := ps, theorems := #[] }
  let s ← elabFrom imports sub
  let errors ← s.messages.toList.filterM fun m => return m.severity == .error
  unless errors.isEmpty do
    let ps ← errors.toArray.mapM fun m => do
      return s!"error: {m.pos.line}:{m.pos.column + 1}: fresh submission elaboration failed: {(← m.data.toString).trimAscii}"
    let theorems := (o.env.constants.map₂.toList.filterMap fun (n, c) =>
      if (o.env.getModuleIdxFor? n).isNone && c.isTheorem && !generated o.env {} n then some n else none).toArray.qsort Name.lt
    return { problems := ps, theorems }
  validateEnvironments imports o.env s.env scaffold

def validateFrom (imports : Environment) (orig sub : System.FilePath) : IO Verdict :=
  validateUsing imports orig sub false

/-- A scaffold permits open theorem proofs. Definitions, contracts and kernel replay retain
the submission rules. The coordinator separately extracts and checks its dependency graph. -/
def validateScaffoldFrom (imports : Environment) (orig sub : System.FilePath) : IO Verdict :=
  validateUsing imports orig sub true

/-- Validates `sub` against `orig` in a process that has not imported yet. -/
def validate (orig sub : System.FilePath) : IO Verdict := do
  validateFrom (← importFileEnv orig) orig sub

end LeanTools
