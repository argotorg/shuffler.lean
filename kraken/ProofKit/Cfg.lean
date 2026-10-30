import Kraken.StateCfg
import Kraken.KVCGen
import ProofKit.Shape
import ProofKit.SymExec

/-!
Tools for `Program.WP.cfg` proofs. All untrusted: they only build terms that
the kernel checks.

* `cfg_goto`: a jump to a label of the cfg. Three goals: the stack, the
  invariant of the label, the variant.
* `cfg_stk`: the stack goal, when `rsp` is below the entry `rsp`.
* `cfg_blocks`: `cfg_cases`, then each block goal has the tag of its block
  (`entry`, or the label), so `case «.LB.Emission.push.0» t ht => …` selects it.
* `vc_by_shape | kind => tac …`: run `tac` on each goal of that kind.
* `#cfg_skeleton p`: print a `Program.WP.cfg` proof skeleton for `p`.
-/

open Lean Meta Elab Tactic Command

namespace ProofKit

/-- A jump to a label of the cfg: three goals, the stack, the invariant of the
label, the variant. -/
macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

/-- The stack goal of `cfg_goto` when `rsp` is below the entry `rsp`. -/
macro "cfg_stk" : tactic => `(tactic| (
  apply MachineData.stackAtOrBelow_of_toNat_lt
  simp only [Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp]
  bv_omega))

/-- The names of the blocks of a program: `entry`, then the labels. -/
def blockNames (p : Expr) : MetaM (Array String) := do
  return (← blocks (← directives p)).map fun (l?, _) => l?.getD "entry"

/-- `cfg_cases`; then the goal of block `i` has the tag of block `i`.
`cfg_cases` gives the goal of block `i` the tag `right.….right.left` with `i`
times `right` (the last block: `i` times `right`). -/
elab "cfg_blocks" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Program.ForallBlocks p _ := ty
    | throwError "cfg_blocks: expected `Program.ForallBlocks p P`"
  let names ← blockNames p
  g.setTag `cfgBlocks
  evalTactic (← `(tactic| cfg_cases))
  for g in ← getGoals do
    let rights := (← g.getTag).components.filter (· == `right) |>.length
    if let some n := names[rights]? then g.setTag (Name.mkSimple n)

/-! ## Dispatch by shape -/

/-- One arm: a kind (an identifier, so no new keywords), an optional label for
`goto`, and a tactic. -/
syntax vcArm := " | " ident (ppSpace str)? " => " tacticSeq
/-- `vc_by_shape | load => t₁ | goto ".L" => t₂ …`: on each goal, run the
tactic of the first arm whose kind is the kind of the goal (`ProofKit.vcKind`).
A failure of the tactic is an error. The goals that no arm matches stay. -/
syntax (name := vcByShape) "vc_by_shape" (ppLine vcArm)+ : tactic

/-- Does the arm `(kind, label?)` match `k`? -/
def armMatches (kind : Name) (l? : Option String) (k : VcKind) : Bool :=
  match k, l? with
  | .goto l, some l' => kind == `goto && l == l'
  | .goto _, none => kind == `goto
  | k, none => kind.toString == k.name
  | _, some _ => false

@[tactic vcByShape] def evalVcByShape : Tactic := fun stx => do
  let arms := stx[1].getArgs.map fun a => (a[1].getId, a[2].getOptional?.map (·.isStrLit?.get!), a[4])
  for (kind, _, _) in arms do
    unless [`load, `retAddr, `goto, `ret, `jumpOut, `fall, `closed, `other].contains kind do
      throwError "vc_by_shape: unknown kind {kind}"
  let mut out := #[]
  for g in ← getGoals do
    if ← g.isAssigned then continue
    let k ← vcKind g
    match arms.find? fun (kind, l?, _) => armMatches kind l? k with
    | none => out := out.push g
    | some (_, _, tac) =>
      setGoals [g]
      let tag := (← g.getTag)
      -- not backtracking: an abort (`.internal`) keeps the error that the tactic logged
      Tactic.tryCatch (evalTactic tac) fun e => do
        if e matches .internal .. then throw e
        throwError "vc_by_shape: the tactic for the {k.name} goal {tag} fails:\n{e.toMessageData}"
      out := out ++ (← getUnsolvedGoals)
  setGoals out.toList

/-! ## The skeleton -/

/-- The string literals in `e`. -/
partial def strLits (e : Expr) (acc : Array String := #[]) : Array String :=
  match e with
  | .lit (.strVal s) => acc.push s
  | .app f a => strLits a (strLits f acc)
  | .mdata _ b | .proj _ _ b => strLits b acc
  | _ => acc

/-- `#cfg_skeleton p`: print a `Program.WP.cfg` proof for `p` with a hole
(`sorry`) for the invariant of each block, a hole for the proof of the entry
invariant, a hole for the variant of each label that is on a cycle of the block
graph (jumps and fall-throughs), that a block at or after it jumps to, or that
reaches such a label, and one `case` per block. The other labels get the
variant `0`: on each edge into them the block index increases. -/
syntax (name := cfgSkeleton) "#cfg_skeleton " ident : command

@[command_elab cfgSkeleton] def elabCfgSkeleton : CommandElab := fun stx => do
  let `(#cfg_skeleton $p) := stx | throwUnsupportedSyntax
  liftTermElabM do
    let pn ← realizeGlobalConstNoOverloadWithInfo p
    let bs ← blocks (← directives (mkConst pn))
    let labels := bs.filterMap (·.1)
    -- the labels that each block jumps to
    let targets := bs.map fun (_, body) =>
      body.foldl (fun (acc : Array String) d => (strLits d).foldl (fun (acc : Array String) s =>
        if labels.contains s && !acc.contains s then acc.push s else acc) acc) #[]
    -- the edges of the block graph: the jumps, and the fall-through unless the
    -- block ends with `jmp` or `ret`
    let idx (l : String) := (bs.findIdx? (·.1 == some l)).getD 0
    let ends (body : Array Expr) := body.back?.any fun d =>
      (d.find? fun e => e.isConstOf ``Operation.jmp || e.isConstOf ``Operation.ret).isSome
    let succ := (bs.zip targets).zipIdx.map fun (((_, body), ts), i) =>
      ts.map idx ++ (if ends body || i + 1 ≥ bs.size then #[] else #[i + 1])
    -- the blocks that block `i` reaches
    let reach (i : Nat) : Array Nat := Id.run do
      let mut seen : Array Nat := #[]
      let mut todo := succ[i]!.toList
      for _ in [0:bs.size * bs.size + 1] do
        match todo with
        | [] => break
        | j :: rest =>
          todo := rest
          if seen.contains j then continue
          seen := seen.push j
          todo := todo ++ succ[j]!.toList
      return seen
    -- a label needs a variant if it is on a cycle (it reaches itself), if a
    -- block at or after it jumps to it, or if it reaches such a label
    let backTarget (l : String) := (targets.zipIdx.any fun (ts, j) => j ≥ idx l && ts.contains l)
    let back0 := labels.filter fun l => (reach (idx l)).contains (idx l) || backTarget l
    let back := labels.filter fun l =>
      back0.contains l || (reach (idx l)).any fun j => back0.any (idx · == j)
    let q (s : String) := s!"\"{s}\""
    let mut out := "refine Program.WP.cfg (fun\n    | .entry, t => sorry\n"
    for l in labels do
      out := out ++ s!"    | .label {q l}, t => sorry\n"
    out := out ++ "    | _, _ => False)\n"
    let var := back.foldl (fun acc l => acc ++ s!"    | {q l}, _ => sorry\n") "  (fun\n"
    out := out ++ s!"{var}    | _, _ => 0) ?_ sorry\ncfg_blocks\n"
    for ((l?, body), ts) in bs.zip targets do
      let n := l?.getD "entry"
      let ts := ts.toList.map q
      out := out ++ s!"case «{n}» t ht => sorry -- {body.size} directives, jumps to {ts}\n"
    logInfo m!"Try this:\n{out}"

end ProofKit
