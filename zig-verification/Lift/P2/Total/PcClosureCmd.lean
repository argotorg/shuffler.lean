module

public import Lift.P2.Total.PcClosure
public import Lift.P2.Total.Normalize
public meta import Lean
public meta import Lift.P2.Total.CheckedCmd

public meta section

open Lean Elab Command

namespace Lift.P2.Total

/-- A proposed finite PC graph. Its rank and state invariant are checked. -/
declare_syntax_cat p2PcEdge
syntax num " => " "[" num,* "]" : p2PcEdge

private def pcGraphRank (graphRows : Array (Nat × Array Nat)) (returnSites : Array Nat) :
    Nat → Nat → Except String Nat
  | 0, _ => .error "the PC graph contains a cycle"
  | fuel + 1, pc => do
    let some (_, next) := graphRows.find? (fun row => row.1 == pc)
      | throw s!"missing PC {pc}"
    if returnSites.contains pc then
      if !next.isEmpty then throw s!"return PC {pc} has successors"
      return 1
    let ranks ← next.mapM (pcGraphRank graphRows returnSites fuel)
    return ranks.foldl max 0 + 1

private def pcCommand (source : String) : CommandElabM (TSyntax `command) := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok parsed => return ⟨parsed⟩
  | .error message => throwError "PC closure command parse error: {message}"

/-- Propose a DAG rank and check each source instruction once. The theorem
requires a mapped return slot, but makes no successful heap-read assumption. -/
elab "#p2_pc_closure " step:ident &"entry" entryPC:num
    &"graph" "[" edges:p2PcEdge,* "]"
    &"returns" "[" returnSites:num,* "]" " as " output:ident : command =>
  withScope (fun scope => { scope with opts := scope.opts.insert `maxRecDepth (.ofNat 20000) }) do
    let graphRows ← edges.getElems.mapM fun edge => do
      match edge with
      | `(p2PcEdge| $pc:num => [$next:num,*]) =>
        return (pc.getNat, next.getElems.map (·.getNat))
      | _ => throwError "invalid PC graph row"
    let returnPCs := returnSites.getElems.map (·.getNat)
    let nodes := graphRows.map (·.1)
    if nodes.isEmpty then throwError "the PC graph is empty"
    if nodes.toList.eraseDups.length != nodes.size then throwError "duplicate PC graph row"
    if !nodes.contains entryPC.getNat then throwError "entry PC is absent"
    for pc in nodes do
      if pc >= 2^63 then throwError "PC must be a nonnegative Int64"
    for pc in returnPCs do
      if !nodes.contains pc then throwError "return PC is absent"
    let ranks ← graphRows.mapM fun (pc, _) =>
      match pcGraphRank graphRows returnPCs (nodes.size + 1) pc with
      | .ok rank => pure rank
      | .error message => throwError "{message}"
    let stem := output.getId.toString
    let stepText := step.getId.toString
    let rankName := stem ++ ".rank"
    let nodeName := stem ++ ".nodes"
    let invName := stem ++ ".invariant"
    let ret := "Int64.ofBitVec (BitVec.ofInt 64 word)"
    let rankBody := String.join ((nodes.zip ranks).toList.map fun (pc, rank) =>
      s!"if pc = ({pc} : Int64) then {rank} else ") ++ "0"
    let nodeBody := String.intercalate " ∨ " (nodes.toList.map fun pc => s!"pc = ({pc} : Int64)") ++ " ∨ False"
    let listBody := String.intercalate ", " (nodes.toList.map fun pc => s!"({pc} : Int64)")
    let mut commands : Array (TSyntax `command) := #[]
    let mut audit : Array Name := #[]
    let currentNamespace ← getCurrNamespace
    let add := fun (source : String) => pcCommand source
    commands := commands.push (← add s!"def {rankName} (pc : Int64) : Nat := {rankBody}")
    commands := commands.push (← add s!"def {nodeName} (pc : Int64) : Prop := {nodeBody}")
    commands := commands.push (← add s!"def {invName} (initial : MachineState) (word : Int) (state : MachineState) : Prop :=\n  state.pc = {ret} ∨ (Lift.P2.Total.ReadOnlyFrame initial.data state.data ∧ {nodeName} state.pc)")
    for (pc, _) in graphRows, index in [:graphRows.size] do
      let site := mkIdent (output.getId ++ Name.mkSimple s!"site{index}")
      let pcSyntax : TSyntax `num := ⟨Syntax.mkNumLit (toString pc)⟩
      commands := commands.push (← `(#p2_step_eq $step at $pcSyntax as $site))
      let allName := stem ++ s!".all{index}"
      let siteName := stem ++ s!".site{index}"
      if returnPCs.contains pc then
        commands := commands.push (← add s!"theorem {allName} (data : MachineData) (word : Int)\n    (mapped : Mem.loadInt data.dmem data.regs.rsp.toBitVec 8 = some word) :\n    Lift.P2.Total.AllNext (fun state => state.pc = {ret}) ({stepText} ⟨data, {pc}⟩) := by\n  rw [{siteName}]\n  simp only [Lift.P2.Total.AllNext, MachineData.load, Width.bytes, Width.bits, mapped]")
      else
        commands := commands.push (← add s!"theorem {allName} (data : MachineData) :\n    Lift.P2.Total.AllNext (fun state => Lift.P2.Total.ReadOnlyFrame data state.data ∧\n      {rankName} state.pc < {rankName} {pc} ∧ {nodeName} state.pc)\n      ({stepText} ⟨data, {pc}⟩) := by\n  rw [{siteName}]\n  simp only [Lift.P2.Total.AllNext]\n  repeat' (first | apply Lift.P2.Total.AllNext.load | (intro) | (split))\n  all_goals simp_all [Lift.P2.Total.AllNext, Lift.P2.Total.ReadOnlyFrame, {rankName}, {nodeName}]")
      audit := audit.push (currentNamespace ++ site.getId)
      audit := audit.push (currentNamespace ++ output.getId ++ Name.mkSimple s!"all{index}")
    commands := commands.push (← add "section")
    commands := commands.push (← add "attribute [local irreducible] Lift.P2.Total.AllNext")
    let mut caseProofs := ""
    for (pc, _) in graphRows, index in [:graphRows.size] do
      caseProofs := caseProofs ++ s!"  rcases member with pcEqual | member\n  · change pc = {pc} at pcEqual\n    refine Lift.P2.Total.AllNext.of_pc {stepText}\n      (fun pc next => {invName} initial word next ∧ {rankName} next.pc < {rankName} pc)\n      data pc {pc} pcEqual ?_\n"
      if returnPCs.contains pc then
        caseProofs := caseProofs ++ s!"    have mapped : Mem.loadInt data.dmem data.regs.rsp.toBitVec 8 = some word := by\n      rw [frame.1, frame.2]\n      exact slot\n    refine Lift.P2.Total.AllNext.mono (fun next => next.pc = {ret})\n      (fun next => {invName} initial word next ∧ {rankName} next.pc < {rankName} {pc})\n      ({stepText} ⟨data, {pc}⟩) ?_ ({stem}.all{index} data word mapped)\n    intro next equal\n    refine ⟨Or.inl equal, ?_⟩\n    rw [equal, returnRank]\n    change 0 < {rankName} {pc}\n    decide\n"
      else
        caseProofs := caseProofs ++ s!"    refine Lift.P2.Total.AllNext.mono\n      (fun next => Lift.P2.Total.ReadOnlyFrame data next.data ∧ {rankName} next.pc < {rankName} {pc} ∧ {nodeName} next.pc)\n      (fun next => {invName} initial word next ∧ {rankName} next.pc < {rankName} {pc})\n      ({stepText} ⟨data, {pc}⟩) ?_ ({stem}.all{index} data)\n    rintro next ⟨preserved, lower, member'⟩\n    exact ⟨Or.inr ⟨⟨preserved.1.trans frame.1, preserved.2.trans frame.2⟩, member'⟩, lower⟩\n"
    caseProofs := caseProofs ++ "  exact member.elim\n"
    commands := commands.push (← add s!"theorem {stem}.decreases (V : Type) (returned : MachineState → Option V)\n    (word : Int) (initial : MachineState)\n    (slot : Mem.loadInt initial.data.dmem initial.data.regs.rsp.toBitVec 8 = some word)\n    (outside : {ret} ∉ [{listBody}])\n    (returnBoundary : ∀ state, state.pc = {ret} → returned state ≠ none) :\n    ∀ state, {invName} initial word state → returned state = none →\n      Lift.P2.Total.AllNext (fun next => {invName} initial word next ∧\n        {rankName} next.pc < {rankName} state.pc) ({stepText} state) := by\n  have returnRank : {rankName} ({ret}) = 0 := by\n    simp_all [{rankName}]\n  rintro ⟨data, pc⟩ (atReturn | ⟨frame, member⟩) notReturned\n  · exact (returnBoundary _ atReturn notReturned).elim\n  change _ ∨ _ at member\n{caseProofs}")
    let entryRank := ranks[(nodes.toList.idxOf entryPC.getNat)]!
    commands := commands.push (← add s!"theorem {stem}.closed (V M : Type) (policy : CpuPolicy)\n    (returned : MachineState → Option V) (visible : DataMem → M)\n    (word : Int) (initial : MachineState)\n    (atEntry : initial.pc = {entryPC.getNat})\n    (slot : Mem.loadInt initial.data.dmem initial.data.regs.rsp.toBitVec 8 = some word)\n    (outside : {ret} ∉ [{listBody}])\n    (returnBoundary : ∀ state, state.pc = {ret} → returned state ≠ none)\n    (depth : Nat) (bound : {entryRank} < depth) :\n    ∀ final, ¬ Lift.P2.Total.unroll (Lift.P2.Total.cpuSystem {stepText} policy returned visible) depth initial (.pending final) := by\n  apply Lift.P2.Total.cpuSystem_closed_of_rank {stepText} policy returned visible\n    ({invName} initial word) (fun state => {rankName} state.pc)\n    ({stem}.decreases V returned word initial slot outside returnBoundary) depth initial\n  · exact Or.inr ⟨⟨rfl, rfl⟩, by simp [{nodeName}, atEntry]⟩\n  · simpa [{rankName}, atEntry] using bound")
    commands := commands.push (← add "end")
    for suffix in [`rank, `nodes, `invariant, `decreases, `closed] do
      audit := audit.push (currentNamespace ++ output.getId ++ suffix)
    generateChecked commands audit

end Lift.P2.Total
