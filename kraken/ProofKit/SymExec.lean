import Kraken.StateCfg
import Kraken.KVCGen
import ProofKit.Shape

/-!
`#symexec p from "L"`: run one block of the parsed program `p` on a symbolic
state and print a def for the state at each exit of the block.

The tool runs `kvcgen64` on `WP.wp body (fun _ => Q) E s` with `s`, `Q` and
`E` free. Each goal whose target is `Q t` is the fall-through exit; each goal
whose target is `E a t` is a jump to `a` (a label, or `t.retAddr.get!` for
`ret`). The hypotheses that `vcgen` adds on the way are the path condition.
The other goals are side conditions (loads, flags); the tool counts them.
An exit that the normalization tactic closes is dead: it gets no defs.

The state is the state of the VC that the proof will see, after the same
normalization tactic, so the printed def matches that goal up to `rfl`.
Untrusted: the output is a def; the kernel checks each use of it.
-/

open Lean Meta Elab Term Command Tactic

namespace ProofKit

/-- The default normal form of a state: the `kvcgen64` rewrite set, literal
`Int64`/`BitVec` evaluation, and `ofInt (toInt x) = x`, `at *` or at the given location. -/
macro "symexec_norm" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic => do
  let loc ← match loc with
    | some l => pure l
    | none => `(Lean.Parser.Tactic.location| at *)
  `(tactic| simp only [
  Reg64s.get64_rax, Reg64s.get64_rbx, Reg64s.get64_rcx, Reg64s.get64_rdx, Reg64s.get64_rsi,
  Reg64s.get64_rdi, Reg64s.get64_rsp, Reg64s.get64_rbp, Reg64s.get64_r8, Reg64s.get64_r9,
  Reg64s.get64_r10, Reg64s.get64_r11, Reg64s.get64_r12, Reg64s.get64_r13, Reg64s.get64_r14,
  Reg64s.get64_r15,
  Reg64s.rax_mk, Reg64s.rbx_mk, Reg64s.rcx_mk, Reg64s.rdx_mk, Reg64s.rsi_mk, Reg64s.rdi_mk,
  Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r8_mk, Reg64s.r9_mk, Reg64s.r10_mk, Reg64s.r11_mk,
  Reg64s.r12_mk, Reg64s.r13_mk, Reg64s.r14_mk, Reg64s.r15_mk,
  MachineData.regs_mk, MachineData.dmem_mk, MachineData.status_mk, MachineData.zmms_mk,
  Int64.reduceToInt, Int64.toBitVec_ofNat, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat,
  BitVec.add_zero, BitVec.ofInt_toInt, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
  Nat.reduceAnd, BitVec.take, BitVec.reduceExtractLsb', BitVec.reduceSetWidth,
  CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc,
  CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result,
  StatusFlags.from_result.Remaining.cf_mk, UInt64.ofBitVec_toBitVec,
  BitVec.reduceToNat] $loc)

/-- The directive cells of a program literal. -/
partial def directives (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let e ← whnfD e
  match_expr e with
  | List.nil _ => return acc
  | List.cons _ hd tl => directives tl (acc.push (← whnfD hd))
  | _ => throwError "symexec: cannot compute the directives of the program"

/-- The blocks of a program: `none` for the entry segment, then one per label. -/
def blocks (dirs : Array Expr) : MetaM (Array (Option String × Array Expr)) := do
  let mut bs : Array (Option String × Array Expr) := #[(none, #[])]
  for d in dirs do
    match_expr d with
    | Directive.label l =>
      let some s ← strLit? l | throwError "symexec: a label that is not a literal"
      bs := bs.push (some s, #[])
    | _ =>
      let (l, b) := bs.back!
      bs := bs.pop.push (l, b.push d)
  return bs

/-- One exit of a block. -/
structure Exit where
  /-- `fall`, `goto L`, `ret`, `out`. -/
  kind : String
  /-- Free Bool variables (the `af` values of `∀ af`) the state reads. -/
  bools : Array Expr
  /-- The path condition, one entry per hypothesis. -/
  conds : Array Expr
  /-- The state at the exit. -/
  state : Expr

/-! ## Sharing: repeated subterms become `let`s -/

/-- The size of a term (number of nodes, with repetition). -/
partial def termSize : Expr → Nat
  | .app f a => termSize f + termSize a + 1
  | .lam _ t b _ | .forallE _ t b _ => termSize t + termSize b + 1
  | .letE _ t v b _ => termSize t + termSize v + termSize b + 1
  | .mdata _ b | .proj _ _ b => termSize b + 1
  | _ => 1

/-- Count each closed-under-binders subterm of `e` whose type is in `tys`. -/
def countSubterms (e : Expr) (keep : Expr → MetaM Bool) : MetaM (Std.HashMap Expr Nat) := do
  let r ← IO.mkRef ({} : Std.HashMap Expr Nat)
  let rec go (e : Expr) : MetaM Unit := do
    if e.hasLooseBVars then
      match e with
      | .app f a => go f; go a
      | _ => pure ()
      return
    let m ← r.get
    if let some n := m[e]? then
      r.set (m.insert e (n + 1))
      return  -- children already counted once
    if ← keep e then r.set (m.insert e 1)
    match e with
    | .app f a => go f; go a
    | .proj _ _ b | .mdata _ b => go b
    | _ => pure ()
  go e
  r.get
/-- A subterm worth a name: a memory, or a word that reads memory. -/
def worthName (e : Expr) : MetaM Bool := do
  if !e.hasFVar || termSize e < 8 then return false
  let ty ← inferType e
  if ty.isAppOf ``Mem then return true
  let ty ← whnfR ty
  if ty.isAppOf ``BitVec then
    return (e.find? (·.isAppOf ``Mem.loadInt)).isSome
  return false

/-- Replace repeated subterms of `e` by `let`s, smallest first, at most `n` of them.
The names are `M1, M2, …` for memories and `v1, v2, …` for words. -/
partial def shareLets (e : Expr) (n : Nat := 64) : MetaM Expr := do
  let cache ← IO.mkRef ({} : Std.HashMap Expr Bool)
  let keep (t : Expr) : MetaM Bool := do
    if let some b := (← cache.get)[t]? then return b
    let b ← worthName t
    cache.modify (·.insert t b)
    return b
  let rec loop (e : Expr) (k : Nat) (lets : Array (Name × Expr × Expr)) : MetaM Expr := do
    let counts ← countSubterms e keep
    let cands := counts.toArray.filter (·.2 ≥ 2) |>.qsort (fun a b => termSize a.1 < termSize b.1)
    match cands[0]?, k with
    | some (t, _), k + 1 =>
      let ty ← inferType t
      let isMem := ty.isAppOf ``Mem
      let nm := Name.mkSimple (if isMem then s!"M{lets.size + 1}" else s!"v{lets.size + 1}")
      withLocalDeclD nm ty fun x => do
        let e' := e.replace fun s => if s == t then some x else none
        let lets' := lets.map fun (nm, ty, v) => (nm, ty, v)
        let body ← loop e' k (lets'.push (nm, ty, t))
        -- `body` is closed over the later lets; bind `x`
        let body := body.abstract #[x]
        return .letE nm ty t body false
    | _, _ => return e
  loop e n #[]

/-! ## The command -/

/-- The options for printing: the text must elaborate back to the same term. -/
def ppOpts (o : Options) : Options :=
  ((((o.set `format.width (100 : Nat)).set `pp.proofs true).set `pp.structureInstanceTypes true)
    |>.set `pp.coercions.types true)

/-- The pairs of subterms where `a` and `b` differ (a walk over the same shape). -/
partial def diffs (a b : Expr) (acc : Array (Expr × Expr) := #[]) : Array (Expr × Expr) :=
  if a == b then acc else
  match a, b with
  | .app f x, .app g y => diffs x y (diffs f g acc)
  | .letE _ t v e _, .letE _ t' v' e' _ => diffs e e' (diffs v v' (diffs t t' acc))
  | .mdata _ x, _ => diffs x b acc
  | _, .mdata _ y => diffs a y acc
  | _, _ => acc.push (a, b)
/-- Pretty-print a def, and check that the text of the body elaborates back to
the body: `exact` (the same term), `defeq`, or `FAIL`. -/
def ppDef (name : String) (val : Expr) : TermElabM (String × String) := do
  lambdaTelescope val fun xs body => do
    let mut bs := ""
    for x in xs do
      let d ← x.fvarId!.getDecl
      bs := bs ++ s!" ({d.userName} : {← ppExpr d.type})"
    let rty ← inferType body
    let b := toString (← withOptions ppOpts (ppExpr body))
    let check : TermElabM String := do
      let stx ← match Parser.runParserCategory (← getEnv) `term b with
        | .ok stx => pure stx
        | .error e => return s!"FAIL (parse: {e})"
      let e ← Term.withSynthesize (elabTermEnsuringType stx rty)
      let e ← instantiateMVars e
      if e == body then return "exact"
      if ← isDefEq e body then return "defeq"
      let ds := diffs e body
      let show1 (p : Expr × Expr) : String := s!"{p.1.getAppFn} vs {p.2.getAppFn}"
      return s!"FAIL: {ds.size} differences: {(ds.extract 0 4).toList.map show1}"
    let ok ← try check catch ex => pure s!"FAIL ({← ex.toMessageData.toString})"
    return (s!"def {name}{bs} : {← ppExpr rty} :=\n  {b.replace "\n" "\n  "}", ok)

/-- Run `kvcgen64` and then `norm` on the block body; give the exits and the number of
side goals. -/
def runBlock (body : Expr) (norm : TSyntax `Lean.Parser.Tactic.tacticSeq) :
    TermElabM (Array Exit × Array (String × Nat)) := do
  let bodyStx ← exprToSyntax body
  let tyStx ← `(open scoped Program.WP in ∀ [Host] [FunDecls] (s : MachineData)
      (Q : MachineData → Prop) (E : Int64 → MachineData → Prop), Std.WP.wp $bodyStx (fun _ => Q) E s)
  let ty ← elabType tyStx
  synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let g ← mkFreshExprMVar ty
  let (fvs, g) ← g.mvarId!.introN 5 [`inst1, `inst2, `s, `Q, `E]
  let qv := mkFVar fvs[3]!
  let ev := mkFVar fvs[4]!
  let s := mkFVar fvs[2]!
  let base ← g.withContext do return (← getLCtx).getFVarIds
  let gs ← Tactic.run g (evalTactic (← `(tactic| kvcgen64)))
  let mut exits := #[]
  let mut side : Std.HashMap String Nat := {}
  for g in gs do
    let t ← g.withContext do whnfR (← instantiateMVars (← g.getType))
    let isExit := t.getAppFn == qv || t.getAppFn == ev
    unless isExit do
      let k ← vcKind g
      side := side.insert k.name (side.getD k.name 0 + 1)
      continue
    -- revert the path condition, normalize, re-introduce
    let newHyps ← g.withContext do
      let lctx ← getLCtx
      let mut hs := #[]
      for d in lctx do
        if d.isImplementationDetail || base.contains d.fvarId then continue
        if ← isProp d.type then hs := hs.push d.fvarId
      return hs
    let (_, g1) ← g.revert newHyps
    let gs' ← Tactic.run g1 (evalTactic (← `(tactic| try ($norm))))
    let some g2 := gs'.head? | exits := exits.push ⟨"dead", #[], #[], s⟩; continue
    let (hs, g3) ← g2.intros
    let ex ← g3.withContext do
      let t ← instantiateMVars (← g3.getType)
      let conds ← hs.mapM fun h => do instantiateMVars (← h.getType)
      let args := t.getAppArgs
      let (kind, st) ←
        if t.getAppFn == qv then pure ("fall", args[0]!)
        else
          let a := args[0]!
          let kind ← match_expr a with
            | Labels.label _ l => pure s!"goto {(← strLit? l).getD "?"}"
            | Option.get! _ _ x => pure (if x.isAppOf ``MachineData.retAddr then "ret" else "out")
            | _ => pure "out"
          pure (kind, args[1]!)
      let fvs := (conds.push st).foldl (fun acc e => collectFVars acc e) {}
      let lctx ← getLCtx
      let mut bools := #[]
      for x in fvs.fvarIds do
        if x == s.fvarId! then continue
        match lctx.find? x with
        | some d => bools := bools.push d.toExpr
        | none => logInfo m!"symexec: free variable {mkFVar x} is not in the context"
      -- close over the start state and the Bool variables
      let close (e : Expr) : TermElabM Expr := do
        mkLambdaFVars (#[s] ++ bools) e
      return { kind, bools, conds := ← conds.mapM close, state := ← close st : Exit }
    exits := exits.push ex
  return (exits, side.toArray)

syntax (name := symexecCmd) "#symexec " ident " from " str (" using " tacticSeq)? : command

@[command_elab symexecCmd] def elabSymexec : CommandElab := fun stx => do
  let `(#symexec $p from $l $[using $norm?]?) := stx | throwUnsupportedSyntax
  liftTermElabM do
    let pn ← realizeGlobalConstNoOverloadWithInfo p
    let dirs ← directives (mkConst pn)
    let bs ← blocks dirs
    let lbl := l.getString
    let some (_, body) := bs.find? fun (n, _) => n == some lbl || (lbl == "entry" && n.isNone)
      | throwError "symexec: no block {lbl}"
    let bodyE ← mkListLit (mkConst ``Directive) body.toList
    let norm ← match norm? with
      | some n => pure n
      | none => `(Lean.Parser.Tactic.tacticSeq| symexec_norm)
    -- `vcgen` needs the scoped instances of these namespaces; open them for this block only
    Lean.pushScope
    let (exits, side) ← try
        for ns in [`Std.WP, `Lean.Order, `Program.WP] do Lean.activateScoped ns
        runBlock bodyE norm
      finally Lean.popScope
    let base := s!"{pn}.{lbl.replace "." ""}"
    let mut out := s!"-- #symexec {pn} from \"{lbl}\": {body.size} instructions, " ++
      s!"{exits.size} exits, side goals {side.toList}\n"
    let mut i := 0
    let mut checks : Array String := #[]
    for ex in exits do
      i := i + 1
      let nm := s!"{base}.x{i}"
      out := out ++ s!"\n-- exit {i}: {ex.kind}\n"
      if ex.kind == "dead" then continue
      let mut j := 0
      for c in ex.conds do
        j := j + 1
        let cn := if ex.conds.size == 1 then s!"{nm}.cond" else s!"{nm}.cond{j}"
        let v ← shareLets' c
        define cn v
        let (t, ok) ← ppDef cn v
        out := out ++ t ++ "\n"
        checks := checks.push s!"{cn}: {ok}"
      let v ← shareLets' ex.state
      define s!"{nm}.st" v
      let (t, ok) ← ppDef s!"{nm}.st" v
      out := out ++ t ++ "\n"
      checks := checks.push s!"{nm}.st: {ok}"
    logInfo m!"Try this:\n{out}"
    logInfo m!"symexec: the command defines these terms. The printed text elaborates back to: {checks.toList}"
where
  /-- Add `name := v` to the environment. -/
  define (name : String) (v : Expr) : TermElabM Unit := do
    let v ← instantiateMVars v
    let ty ← inferType v
    let dv : DefinitionVal :=
      { name := name.toName, levelParams := [], type := ty, value := v, hints := .regular 1,
        safety := .safe }
    addDecl (.defnDecl dv)
    enableRealizationsForConst name.toName
  shareLets' (e : Expr) : MetaM Expr :=
    lambdaTelescope e fun xs b => do mkLambdaFVars xs (← shareLets b)

end ProofKit
