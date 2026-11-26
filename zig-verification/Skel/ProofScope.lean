import Lean

/-! Model aliases for isolated proof helpers. These aliases add no declarations or axioms. -/

open Lean Elab Command

/-- An isolated helper namespace must resolve nested model names as in the frozen source.
Copy only nested names: direct names already resolve through the surrounding namespace. -/
private def modelAliases (env : Environment) (original current : Name) (excluded : List Name) : Environment :=
  let aliases := env.constants.fold (init := []) fun aliases name _ =>
    let userName := privateToUserName name
    if original.isPrefixOf userName then
      let relative := userName.replacePrefix original .anonymous
      if relative.getPrefix.isAnonymous || excluded.contains relative then aliases else (current ++ relative, name) :: aliases
    else aliases
  let aliases := (getAliasState env).fold (fun aliases name targets =>
    if original.isPrefixOf name then
      let relative := name.replacePrefix original .anonymous
      if relative.getPrefix.isAnonymous || excluded.contains relative then aliases else
        targets.foldl (fun aliases target => (current ++ relative, target) :: aliases) aliases
    else aliases) aliases
  aliases.foldl (fun env (alias, target) => addAlias env alias target) env

private def applyAliases (suffix : Syntax) (excluded : List Name) : CommandElabM Unit := do
  let current ← getCurrNamespace
  let original := suffix.getId.components.foldl (fun n _ => n.getPrefix) current
  unless original ++ suffix.getId == current do
    throwError "proof scope does not match the current namespace"
  modifyEnv fun env => modelAliases env original current excluded

elab "skel_proof_aliases " suffix:ident : command => applyAliases suffix []

elab "skel_proof_aliases " suffix:ident " excluding " "[" excluded:ident,* "]" : command =>
  applyAliases suffix (excluded.getElems.toList.map (·.getId))
