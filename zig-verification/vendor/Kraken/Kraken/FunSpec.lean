module

public import Kraken.StateCfg
public meta import Lean.Elab.Command

open Std.WP
open Lean.Order
open scoped Program.WP

public structure CallingConvention where
  calleeSaved : List Reg64
  paramArea : Nat → Nat

@[expose] public def CallingConvention.SysV : CallingConvention :=
  ⟨[.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], fun k => 8 * k⟩

@[expose] public def CallingConvention.Win64 : CallingConvention :=
  ⟨[.rbx, .rbp, .rdi, .rsi, .r12, .r13, .r14, .r15, .rsp], fun k => 32 + 8 * k⟩

namespace FunSpec

variable [Host] [FunDecls]


public theorem autoframes {f : Label} {g : Fragment} (h : FunDecls.at (label f) = some g)
    (s : MachineData) (ra : Int64)
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    {X : MachineData → Int64 → MachineData → Prop} {Fr : MachineData → MachineData → Prop}
    {Hv : MachineData → MachineData → MachineData}
    (hH : ∀ s s', Fr s s' → s'.regs.rsp = s.regs.rsp → Hv s s' = s')
    (hp : ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s ⦄ g.prog
      ⦃ fun _ _ => False; fun a s' =>
        (a = ra → Q s s' ∧ s'.regs.rsp = s.regs.rsp ∧ Fr s s')
        ∧ (a ≠ ra → X s a s') ⦄)
    (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop) :
    ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s
        ∧ (∀ r, (fun t => Q s t → E' ra t) (Hv s r))
        ∧ (∀ a s', a ≠ ra → X s a s' → E' a s') ⦄
      FunDecls.body f
    ⦃ Q'; E' ⦄ := by
  refine Triple.intro fun s₀ ⟨h₀, hpre, hok, hexit⟩ => ?_
  rw [FunDecls.body_eq h]
  refine Program.wp_mono (fun _ h => False.elim h) (fun u hu => ?_) (hp.1 s₀ ⟨h₀, hpre⟩)
  by_cases ha : u.pc = ra
  · obtain ⟨hQ, hrsp, hF⟩ := hu.1 ha
    have hk := hok u.data
    rw [hH s u.data hF hrsp] at hk
    exact ha ▸ hk hQ
  · exact hexit u.pc u.data ha (hu.2 ha)

public theorem autoframes_of_ret {f : Label} {g : Fragment} (h : FunDecls.at (label f) = some g)
    (s : MachineData) (ra : Int64)
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    {Fr : MachineData → MachineData → Prop} {Hv : MachineData → MachineData → MachineData}
    (hH : ∀ s s', Fr s s' → s'.regs.rsp = s.regs.rsp → Hv s s' = s')
    (hp : ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s ⦄ g.prog
      ⦃ fun _ _ => False; fun a s' => a = ra ∧ Q s s' ∧ s'.regs.rsp = s.regs.rsp
        ∧ Fr s s' ⦄)
    (Q' : Unit → MachineData → Prop) (E' : Int64 → MachineData → Prop) :
    ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s
        ∧ (∀ r, (fun t => Q s t → E' ra t) (Hv s r)) ⦄
      FunDecls.body f
    ⦃ Q'; E' ⦄ := by
  refine Triple.intro fun s₀ ⟨h₀, hpre, hok⟩ => ?_
  rw [FunDecls.body_eq h]
  refine Program.wp_mono (fun _ h => False.elim h) (fun u hu => ?_) (hp.1 s₀ ⟨h₀, hpre⟩)
  obtain ⟨ha, hQ, hrsp, hF⟩ := hu
  have hk := hok u.data
  rw [hH s u.data hF hrsp] at hk
  exact ha ▸ hk hQ

public theorem plain {f : Label} {g : Fragment} (h : FunDecls.at (label f) = some g)
    (s : MachineData) (ra : Int64)
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    {X : MachineData → Int64 → MachineData → Prop}
    (hp : ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s ⦄ g.prog
      ⦃ fun _ _ => False; fun a s' => (a = ra → Q s s') ∧ (a ≠ ra → X s a s') ⦄) :
    ⦃ fun s₀ => s₀ = s.push64 ra ∧ P s ⦄ FunDecls.body f
      ⦃ fun _ _ => False; fun a s' => (a = ra → Q s s') ∧ (a ≠ ra → X s a s') ⦄ :=
  FunDecls.body_eq h ▸ hp

public theorem guarded {prog : Program} {pre : MachineData → Prop} {p : Prop}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
    (h : p → ⦃ pre ⦄ prog ⦃ Q; E ⦄) : ⦃ fun s₀ => pre s₀ ∧ p ⦄ prog ⦃ Q; E ⦄ :=
  Triple.intro fun s₀ ⟨hp, hlt⟩ => (h hlt).1 s₀ hp

end FunSpec

namespace FunSpec

open Lean Elab Command Term Meta

declare_syntax_cat funspecClause

syntax "calling_conv " term : funspecClause
syntax "paramSlots " term : funspecClause
syntax "reserve " term : funspecClause
syntax "preserves" (ppSpace ident)+ : funspecClause
syntax "writes " term,+ : funspecClause

declare_syntax_cat funspecSig

syntax ident ppSpace str (ppSpace bracketedBinder)* " at " ident
  (" requires " term)? " ensures " ident " => " term
  (" exits " ident ident " => " term)? (" halts " term)?
  (" autoframes" (ppSpace funspecClause)*)? " := " term Lean.Parser.Termination.suffix
  (Lean.Parser.Term.whereDecls)? : funspecSig

syntax (name := funspecCmd) (Lean.Parser.Command.visibility)? "funspec " funspecSig : command

syntax (name := funspecPrelude) "funspec_prelude " (Lean.Parser.Command.visibility)? funspecSig : command

meta def regOrder : List Name :=
  [`rax, `rbx, `rcx, `rdx, `rsi, `rdi, `rsp, `rbp, `r8, `r9, `r10, `r11, `r12, `r13, `r14, `r15]

meta def regField (x : Ident) (field : Name) : Ident :=
  mkIdent (x.getId ++ `regs ++ field)

meta def ccTerm (cc : Term) : CommandElabM Term :=
  `((open CallingConvention in ($cc : CallingConvention)))

meta def reduceInTerm (stx : Term) : CommandElabM Expr := liftTermElabM do
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  Meta.reduce (← instantiateMVars e)

meta def calleeSaved (cc : Term) : CommandElabM (List Name) := do
  let e ← reduceInTerm (← `(CallingConvention.calleeSaved $(← ccTerm cc)))
  let some (_, rs) := e.listLit?
    | throwErrorAt cc "calleeSaved of {cc} does not reduce to a list literal"
  rs.mapM fun r => match r with
    | .const n _ => if n.getPrefix == ``Reg64 then pure (Name.mkSimple n.getString!)
        else throwErrorAt cc "unexpected register {r}"
    | _ => throwErrorAt cc "unexpected register {r}"

meta def paramArea (cc k : Term) : CommandElabM Nat := do
  let e ← reduceInTerm (← `(CallingConvention.paramArea $(← ccTerm cc) $k))
  let some n ← liftTermElabM (Meta.evalNat e).run
    | throwErrorAt k "paramArea of {k} does not reduce to a numeral"
  pure n

meta def block (stx : Term) : CommandElabM Term :=
  match stx with
  | `($b[*...<$n]) => `(($b, $n))
  | `($b[$a...<$e]) => `(($b + BitVec.ofNat 64 $a, $e - $a))
  | _ => throwErrorAt stx "expected a block `b[*...<n]` or `b[a...<e]`"

meta def conj (ts : Array Term) (last : Term) : CommandElabM Term :=
  ts.foldrM (fun t acc => `($t ∧ $acc)) last

meta def elabWhere (name : Ident) (ds : Array Syntax) : CommandElabM Unit := do
  if ds.isEmpty then return
  elabCommand (← `(command| namespace $name:ident))
  for d in ds do
    match d with
    | `(Lean.Parser.Term.letRecDecl| $[@[$attrs?,*]]? $x:ident $bs* : $ty := $val) =>
      let bs : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := bs.map (⟨·.raw⟩)
      elabCommand <| ← match attrs? with
        | some attrs => `(command| @[$attrs,*] private abbrev $x:ident $bs* : $ty := $val)
        | none => `(command| private abbrev $x:ident $bs* : $ty := $val)
    | _ => throwErrorAt d "funspec expects `where` declarations `x binders* : type := value`"
  elabCommand (← `(command| end $name:ident))

meta def measure? (sfx : Syntax) : Option Term :=
  let t := sfx[0][0]
  if t.isOfKind ``Lean.Parser.Termination.terminationBy && t[1].isNone && t[2].isNone then
    some ⟨t[3]⟩
  else none

meta def forwardArgs (binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder) :
    MacroM (Array Syntax) := do
  let mut args : Array Syntax := #[]
  for b in binders do
    match b with
    | `(bracketedBinder| ($xs:ident* : $_)) => args := args ++ xs.map (·.raw)
    | `(bracketedBinder| {$xs:ident* : $_}) | `(bracketedBinder| ⦃$xs:ident* : $_⦄) =>
      for x in xs do
        args := args.push (← `(Lean.Parser.Term.namedArgument| ($x:ident := $x)))
    | _ => pure ()
  return args

meta def mkApp' (f : Term) (args : Array Syntax) : Term :=
  if args.isEmpty then f else ⟨mkNode ``Lean.Parser.Term.app #[f, mkNullNode args]⟩

structure Parts where
  name : Ident
  f : TSyntax `str
  binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder
  c : Ident
  h : Ident
  p : Term
  P : Term
  tQ : Ident
  Q : Term
  aX : Ident
  X? : Option Term
  hasHalts : Bool
  auto : Bool
  proof : Term
  sfx : TSyntax ``Lean.Parser.Termination.suffix
  hasWhere : Bool

meta def parts (sig : TSyntax `funspecSig) : MacroM Parts := do
  let `(funspecSig| $name:ident $f:str $binders* at $c $[requires $P?]? ensures $tQ => $Q
      $[exits $aX? $tX? => $X?]? $[halts $H?]? $[autoframes $clauses?*]? := $proof $sfx:suffix
      $[$wds?]?) := sig
    | Macro.throwUnsupported
  let some (h, p) ← binders.findSomeM? fun b => do
      match b with
      | `(bracketedBinder| ($h:ident : FunDecls.at (label $l:str) = some ⟨$p⟩)) =>
        pure (if l.getString == f.getString then some (h, p) else none)
      | _ => pure none
    | Macro.throwErrorAt sig s!"funspec expects a binder `(h : FunDecls.at (label {f}) = some ⟨p⟩)`"
  if let some tX := tX? then
    unless tX.getId == tQ.getId do
      Macro.throwErrorAt tX s!"exits must bind the state as {tQ.getId}, the binder of ensures"
  let P ← P?.getDM `(True)
  let aX : Ident := aX?.getD (mkIdent `a)
  -- `halts H`: the return address is not a halt address, and each exit is at one.
  let (P, X?) ← match H? with
    | some H => do
      pure (← `($P ∧ ra ∉ List.map label $H),
        some (← `($aX ∈ List.map label $H ∧ $(← X?.getDM `(True)))))
    | none => pure (P, X?)
  return ⟨name, f, binders, c, h, p, P, tQ, Q, aX, X?, H?.isSome, clauses?.isSome, proof, sfx,
    wds?.isSome⟩

syntax (name := funspecAux) "funspec_aux% " ident ident : term

@[term_elab funspecAux] public meta def elabFunspecAux : TermElab := fun stx expectedType? => do
  let n ← resolveGlobalConstNoOverload (mkIdentFrom stx[1] (stx[1].getId ++ stx[2].getId.eraseMacroScopes))
  elabTerm (mkCIdentFrom stx[1] n) expectedType?

meta def frameOf (name : Ident) : MacroM Term := `((funspec_aux% $name Frame))

meta def havocOf (name : Ident) : MacroM Term := `((funspec_aux% $name Frame.havoc))

meta def havocEqOf (name : Ident) : MacroM Term := `((funspec_aux% $name Frame.havoc_eq))

/-- The exit condition under `autoframes`: `X` and the frame, or only `X` for a halt exit, which
leaves the function before it restores the frame. -/
meta def exitOf (x : Parts) (X frame : Term) : MacroM Term :=
  if x.hasHalts then pure X else `($X ∧ $frame $x.c $x.tQ)

meta def autoPre (x : Parts) (s₀ : Ident) : MacroM Term := do
  let (c, tQ, aX, P, Q) := (x.c, x.tQ, x.aX, x.P, x.Q)
  let frame ← frameOf x.name
  let ok ← `(∀ (r : MachineData), (fun $tQ:ident => $Q → E' ra $tQ) ($(← havocOf x.name) $c r))
  match x.X? with
  | some X => `($s₀ = MachineData.push64 $c ra ∧ $P ∧ $ok
      ∧ (∀ ($aX : Int64) ($tQ : MachineData), $aX ≠ ra → $(← exitOf x X frame) → E' $aX $tQ))
  | none => `($s₀ = MachineData.push64 $c ra ∧ $P ∧ $ok)

meta def plainPost (x : Parts) : MacroM Term := do
  `(fun $x.aX $x.tQ => ($x.aX = ra → $x.Q) ∧ ($x.aX ≠ ra → $(← x.X?.getDM `(False))))

meta def specStmt (x : Parts) (guard? : Option Term) :
    MacroM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder) × Term) := do
  let s₀ : Ident := ⟨(← `(s)).raw⟩
  let addGuard (pre : Term) : MacroM Term := match guard? with
    | some g => `($pre ∧ $g)
    | none => pure pre
  if x.auto then
    let pre ← addGuard (← autoPre x s₀)
    return (#[← `(bracketedBinder| (Q' : Unit → MachineData → Prop)),
        ← `(bracketedBinder| (E' : Int64 → MachineData → Prop))],
      ← `(Std.WP.Triple (FunDecls.body $x.f) (fun $s₀ => $pre) Q' E'))
  let pre ← addGuard (← `($s₀ = MachineData.push64 $x.c ra ∧ $x.P))
  return (#[], ← `(Std.WP.Triple (FunDecls.body $x.f) (fun $s₀ => $pre) (fun _ _ => False)
    $(← plainPost x)))

meta def renameState (old : Name) (new : Name) (t : Term) : Term :=
  ⟨Id.run <| t.raw.replaceM fun
    | stx@(.ident _ _ id _) =>
      pure <| if old.isPrefixOf id then
        some (mkIdentFrom stx (new ++ id.replacePrefix old .anonymous))
      else none
    | _ => pure none⟩

meta def guardOf (μc : Term) (g : Parts) : MacroM (Option (Ident × Term × Term)) := do
  let some μ := measure? g.sfx | return none
  let c ← withFreshMacroScope (MonadQuotation.addMacroScope g.c.getId)
  let r := renameState g.c.getId c
  let g' := { g with c := mkIdentFrom g.c c, P := r g.P, Q := r g.Q, X? := g.X?.map r }
  let (bs, t) ← specStmt g' (some (← `($(r μ) < $μc)))
  let t ← bs.foldrM (fun b acc => `(∀ $b, $acc)) t
  let ty ← `(∀ ($g'.c : MachineData) (ra : Int64), $t)
  let args := bs.filterMap fun b => match b with
    | `(bracketedBinder| ($x:ident : $_)) => some x.raw
    | _ => none
  let app := mkApp' g.name ((← forwardArgs g.binders) ++ #[g.c.raw, (← `(ra)).raw] ++ args)
  let lam ← args.foldrM (fun a acc => `(fun $(⟨a⟩):ident => $acc))
    (← `(FunSpec.guarded fun _ => $app))
  let pf ← `(fun $g.c:ident (ra : Int64) => $lam)
  return some (g.name, ty, pf)

meta def funspecTheorem (vis? : Option (TSyntax ``Lean.Parser.Command.visibility))
    (sig : TSyntax `funspecSig) (group : Array (TSyntax `funspecSig)) :
    MacroM (TSyntax `command × TSyntax `command) := do
  let x ← parts sig
  let (name, binders, c, h, p, P, tQ, Q, aX, sfx) :=
    (x.name, x.binders, x.c, x.h, x.p, x.P, x.tQ, x.Q, x.aX, x.sfx)
  let X ← x.X?.getDM `(False)
  let frame ← frameOf name
  let rsp := regField c `rsp
  let tRsp := regField tQ `rsp
  let post ← if !x.auto then plainPost x
    else if x.X?.isSome then
      `(fun $aX $tQ => ($aX = ra → $Q ∧ $tRsp = $rsp ∧ $frame $c $tQ)
        ∧ ($aX ≠ ra → $(← exitOf x X frame)))
    else `(fun a $tQ => a = ra ∧ $Q ∧ $tRsp = $rsp ∧ $frame $c $tQ)
  let guards ← match measure? sfx with
    | some μ => (← group.mapM parts).filterMapM (guardOf μ)
    | none => pure #[]
  let guardBinders ← guards.mapM fun (g, ty, _) => `(bracketedBinder| ($g:ident : $ty))
  let go := mkIdent (name.getId ++ `go)
  let goThm ← `(command|
    theorem $go:ident $binders* ($c : MachineData) (ra : Int64) $guardBinders* :
        Std.WP.Triple $p (fun s₀ => s₀ = MachineData.push64 $c ra ∧ $P) (fun _ _ => False) $post :=
      $x.proof)
  let goCmd ← if x.auto || x.hasWhere then `(command| open $name:ident in $goThm) else pure goThm
  let goApp := mkApp' go
    ((← forwardArgs binders) ++ #[c.raw, (← `(ra)).raw] ++ guards.map (·.2.2.raw))
  let pf ← if !x.auto then
      `(FunSpec.plain $h $c ra (P := fun $c => $P) (Q := fun $c $tQ => $Q)
          (X := fun $c $aX $tQ => $X) $goApp)
    else if x.X?.isSome then
      `(FunSpec.autoframes $h $c ra (P := fun $c => $P) (Q := fun $c $tQ => $Q)
          (X := fun $c $aX $tQ => $(← exitOf x X frame)) (Fr := $frame) (Hv := $(← havocOf name)) $(← havocEqOf name) $goApp Q' E')
    else
      `(FunSpec.autoframes_of_ret $h $c ra (P := fun $c => $P) (Q := fun $c $tQ => $Q)
          (Fr := $frame) (Hv := $(← havocOf name)) $(← havocEqOf name) $goApp Q' E')
  let (bs, t) ← specStmt x none
  return (goCmd, ← `(command|
    @[spec] $[$vis?:visibility]? theorem $name:ident $binders* ($c : MachineData) (ra : Int64) $bs* :
        $t := $pf
    $sfx:suffix))

@[command_elab funspecPrelude] public meta def elabFunspecPrelude : CommandElab := fun stx => do
  let `(funspec_prelude $[$vis?:visibility]? $sig:funspecSig) := stx | throwUnsupportedSyntax
  let `(funspecSig| $name:ident $_f:str $_binders* at $c $[requires $_P?]? ensures $tQ => $_Q
      $[exits $_aX? $_tX? => $_X?]? $[halts $_H?]? $[autoframes $clauses?*]? := $_proof
      $_sfx:suffix $[$wds?]?) := sig
    | throwUnsupportedSyntax
  let wdecls := match wds? with
    | some wd => wd.raw[1].getSepArgs
    | none => #[]
  let some clauses := clauses? | elabWhere name wdecls
  let mut cc? : Option Term := none
  let mut slots : Term ← `(0)
  let mut rsv : Term ← `(0)
  let mut kept₀ : Array Ident := #[]
  let mut written : Array Term := #[]
  for cl in clauses do
    match cl with
    | `(funspecClause| calling_conv $cc) => cc? := some cc
    | `(funspecClause| paramSlots $k) => slots := k
    | `(funspecClause| reserve $k) => rsv := k
    | `(funspecClause| preserves $rs*) => kept₀ := kept₀ ++ rs
    | `(funspecClause| writes $bs,*) => written := written ++ (← bs.getElems.mapM block)
    | _ => throwErrorAt cl "unexpected autoframes clause"
  for r in kept₀ do
    unless regOrder.contains r.getId do throwErrorAt r "{r} is not a 64-bit register"
  let saved ← match cc? with
    | some cc => calleeSaved cc
    | none => pure []
  let kept := regOrder.filter fun r => r != `rsp && (saved.contains r || kept₀.any (·.getId == r))
  let eqs ← kept.toArray.mapM fun r => `($(regField tQ r) = $(regField c r))
  let rsp := regField c `rsp
  let mut blocks : Array Term := #[← `(Mem.Block.ofStackSlots $rsp $rsv)]
  if let some cc := cc? then
    let n ← paramArea cc slots
    if n > 0 then
      let base := mkIdent (rsp.getId ++ `toBitVec)
      blocks := blocks.push (← `(($base, $(Syntax.mkNumLit (toString n)))))
  blocks := blocks ++ written
  let regs := mkIdent (name.getId ++ `Frame.Regs)
  let blks := mkIdent (name.getId ++ `Frame.blocks)
  let frame := mkIdent (name.getId ++ `Frame)
  let havoc := mkIdent (name.getId ++ `Frame.havoc)
  let havocEq := mkIdent (name.getId ++ `Frame.havoc_eq)
  let cDmem := mkIdent (c.getId ++ `dmem)
  let tDmem := mkIdent (tQ.getId ++ `dmem)
  let regsBody ← match eqs.back? with
    | some e => conj eqs.pop e
    | none => `(True)
  elabCommand (← `(command|
    $[$vis?:visibility]? abbrev $regs:ident ($c:ident $tQ:ident : MachineData) : Prop := $regsBody))
  elabCommand (← `(command|
    $[$vis?:visibility]? abbrev $blks:ident ($c:ident : MachineData) : List (BitVec 64 × Nat) := [$blocks,*]))
  elabCommand (← `(command|
    $[$vis?:visibility]? abbrev $frame:ident ($c:ident $tQ:ident : MachineData) : Prop :=
      $regs $c $tQ ∧ Mem.WritesOnly ($blks $c) $cDmem $tDmem))
  let fields ← (kept.toArray.push `rsp).mapM fun f =>
    `(Lean.Parser.Term.structInstField| $(mkIdent f):ident := $(regField c f))
  let regsVal ← `({ $(mkIdent (tQ.getId ++ `regs)):ident with $fields,* })
  let stateVal ← `({ $tQ:ident with regs := $regsVal, dmem := Mem.havoc $cDmem ($blks $c) $tDmem })
  elabCommand (← `(command|
    $[$vis?:visibility]? abbrev $havoc:ident ($c:ident $tQ:ident : MachineData) : MachineData := $stateVal))
  elabCommand (← `(command|
    $[$vis?:visibility]? theorem $havocEq:ident ($c $tQ : MachineData) (h : $frame $c $tQ)
        (hr : $(regField tQ `rsp) = $(regField c `rsp)) : $havoc $c $tQ = $tQ := by
      obtain ⟨hR, hW⟩ := h
      simp only [$havoc:ident]
      rw [← Mem.WritesOnly.eq_havoc hW]
      obtain ⟨⟨⟩, _, _, _⟩ := $tQ:ident
      simp_all [$regs:ident]))
  elabWhere name wdecls

macro_rules
  | `($[$vis?:visibility]? funspec $sig:funspecSig) => do
    let (go, thm) ← funspecTheorem vis? sig #[sig]
    return mkNullNode #[← `(funspec_prelude $[$vis?:visibility]? $sig:funspecSig), go, thm]

macro_rules
  | `(mutual $elems* end) => do
    unless elems.any (·.raw.isOfKind ``funspecCmd) do Macro.throwUnsupported
    let group : Array (TSyntax `funspecSig) :=
      elems.filterMap fun e => if e.raw.isOfKind ``funspecCmd then some ⟨e.raw[2]⟩ else none
    let mut pre : Array Syntax := #[]
    let mut inner : Array Syntax := #[]
    let mut auxs : Array Syntax := #[]
    for e in elems do
      if e.raw.isOfKind ``funspecCmd then
        let sig : TSyntax `funspecSig := ⟨e.raw[2]⟩
        let vis? : Option (TSyntax ``Lean.Parser.Command.visibility) := e.raw[0].getOptional?.map (⟨·⟩)
        pre := pre.push (← `(funspec_prelude $[$vis?:visibility]? $sig:funspecSig))
        let (go, thm) ← funspecTheorem vis? sig group
        auxs := auxs.push go
        inner := inner.push thm
      else
        inner := inner.push e
    let stx ← getRef
    return mkNullNode ((pre ++ auxs).push (stx.setArg 1 (mkNullNode inner)))

end FunSpec
