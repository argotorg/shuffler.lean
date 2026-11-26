import Lean
import Skel.Gen.Derive.Site
import Lift.Tactic.Block
import Lift.Tactic.RunN
import Lift.Tactic.Cond

/-! The split block proof (task N12 of `docs/research/symexec-pilot-20261118.md`, section 5; decisions D41, D43): one
lemma for each instruction (parts of k = 1 of section 3), and a tactic that proves a block statement by chaining them.

**Site lemmas.** For the site at `a`, `#lift_site_lemmas` adds two theorems, each checked by the kernel alone:
* `<step>.compose.field<a>`: `∀ x₁ … x₂₄, step ⟨D x, a⟩ = T x`, with `D x` the state of the 24 field variables (16
  registers, `zmms`, 6 flags, `dmem`). It is the site equation of N1 (`Skel.Gen.Derive.siteEq`) at `D x`, with each exit
  state a literal of its 24 simplified fields (the exact flags, so that the next site reads a flag by a projection);
* `<step>.compose.reach<a>`: `∀ {policy} (hx : ExecRange policy lo hi) x₁ … x₂₄ <each access: its value, its
  hypothesis> {Q} (hnext : ∀ <undefined values>, Reaches step policy Q ⟨D', pc'⟩), Reaches step policy Q ⟨D x, a⟩`.

**The block proof.** `lift_block_split` proves the goal `Reaches step policy Q ⟨d, pc⟩` of a block statement in the form
of `Skel/Gen/Stmt.lean` (`by intros; lift_block_split`). From the state `⟨D, pc⟩` it applies the site lemma of `pc` to the
24 fields of `D` (not to `D`: with the state as one argument the kernel check of a composition times out, E2 section 3),
the next access hypotheses of the statement, and the rest of the proof as `hnext`. After at least one site, at a PC of an
exit hypothesis it closes the goal with that exit. A PC `if c then a else b` is split.

After each site, each field that the site changed, and the PC, is put in the normal form of the site bodies
(`normTerm`: `simp` with the default set, `lift_site`, `lift_flag` and the default simprocs, an explicit proof for each
`rfl` theorem, then `canonInst`), with the proof `reaches_congr`. The composed terms then stay small and in the form of
the whole-block `simp` (route E of E1), which is the form of the statements of E2.

The statement has its own terms (the L2 form); the site lemmas give the composed terms. Each place where they meet is
one equation, proved alone: the memory, address and value of an access (`read_congr`, `write_congr`), the PC and each
field of an exit state (`exit_eq`), each condition of an exit. An equation is closed syntactically, by reducible
definitional equality, or by the normal forms of both sides: where these differ, at the first explicit argument that
differs (`firstDiff`), that pair is proved alone and rewritten (`bridge`); a pair with different heads by
`lift_compose_eq`. When that pair has no proof, the two sides of the equation are given to `lift_compose_eq` as they are
(the address `rsp - 8 - 8` of the second push of a block against `rsp - 16`: the pair `rsp - 8`, `rsp` is not equal, the
sums are; N15). A condition is closed by `lift_compose_cond`. A part that no closer proves is an error that names it
(for example "the address of access 1"): the tactic leaves no goal. Each access hypothesis of the statement is used by
one access of the sites, in order.

`set_option trace.lift_block_split true` traces the sites and the equations; `set_option lift_block_split.checkParts
true` checks each equation proof by the kernel alone and traces its time. -/

open Lean Meta Elab Term Tactic Lift.P2.Total Lift.Sem

namespace Lift.Tactic.Compose

initialize registerTraceClass `lift_block_split

register_option lift_block_split.checkParts : Bool := {
  defValue := false
  descr := "lift_block_split: check each proof of a meeting equation by the kernel alone, and trace the time"
}

/-! ## Lemmas -/

/-- `Handled.load_ok_iff` with the memory of the hypothesis as a side condition `d.dmem = mem` (so that `simp` uses it for
a state whose memory is a variable after a store). -/
theorem load_ok_iff' {M : Type} {policy : CpuPolicy} {mem : DataMem} {a : BitVec 64} {w : Width} {v : w.type}
    (hread : readRam policy mem a w = .ok v) (visible : DataMem → M) (p : DataMem) (d : MachineData)
    (k : w.type → MachineData → Effects) (result : StepResult M) (hd : d.dmem = mem) :
    Handled policy visible p (d.load a w k) result ↔ Handled policy visible p (k v d) result := by
  subst hd
  exact Handled.load_ok_iff visible p d a w k result hread

/-- `Handled.store_ok_iff` with the memory of the hypothesis as a side condition. -/
theorem store_ok_iff' {M : Type} {policy : CpuPolicy} {mem : DataMem} {a : BitVec 64} {w : Width} {v : w.type}
    {m : DataMem} (hwrite : writeRam policy mem a w v = .ok m) (visible : DataMem → M) (p : DataMem)
    (d : MachineData) (k : MachineData → Effects) (result : StepResult M) (hd : d.dmem = mem) :
    Handled policy visible p (d.store a v k) result ↔ Handled policy visible p (k { d with dmem := m }) result := by
  subst hd
  exact Handled.store_ok_iff visible p d a w v k result hwrite

/-- The start of a block: the state `d` as the literal of its 24 fields. -/
theorem reaches_fields {step : MachineState → Effects} {policy : CpuPolicy} {Q : MachineState → Prop}
    (d : MachineData) (p : Int64)
    (h : Reaches step policy Q ⟨⟨⟨d.regs.rax, d.regs.rbx, d.regs.rcx, d.regs.rdx, d.regs.rsi, d.regs.rdi, d.regs.rsp,
      d.regs.rbp, d.regs.r8, d.regs.r9, d.regs.r10, d.regs.r11, d.regs.r12, d.regs.r13, d.regs.r14, d.regs.r15⟩,
      d.zmms, ⟨d.status.cf, d.status.pf, d.status.af, d.status.zf, d.status.sf, d.status.of⟩, d.dmem⟩, p⟩) :
    Reaches step policy Q ⟨d, p⟩ := h

/-- A PC in another form (the generated text writes `entry + offset`; a site lemma has the numeral). -/
theorem reaches_pc {step : MachineState → Effects} {policy : CpuPolicy} {Q : MachineState → Prop} {D : MachineData}
    {p q : Int64} (hp : p = q) (h : Reaches step policy Q ⟨D, q⟩) : Reaches step policy Q ⟨D, p⟩ := hp ▸ h

/-- The state and the PC in another form (the normal form of the fields after a site). -/
theorem reaches_congr {step : MachineState → Effects} {policy : CpuPolicy} {Q : MachineState → Prop}
    {D D' : MachineData} {p p' : Int64} (hD : D = D') (hp : p = p') (h : Reaches step policy Q ⟨D', p'⟩) :
    Reaches step policy Q ⟨D, p⟩ := hD ▸ hp ▸ h

/-- A branch: the PC `if c then a else b`. -/
theorem reaches_ite {step : MachineState → Effects} {policy : CpuPolicy} {Q : MachineState → Prop} {D : MachineData}
    {c : Prop} [Decidable c] {a b : Int64} (h1 : c → Reaches step policy Q ⟨D, a⟩)
    (h2 : ¬c → Reaches step policy Q ⟨D, b⟩) : Reaches step policy Q ⟨D, if c then a else b⟩ := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h1 hc
  · simp only [hc, ite_false]; exact h2 hc

/-- An exit: `Q` at the state of the hypothesis, which is the state of the goal. -/
theorem exit_eq {step : MachineState → Effects} {policy : CpuPolicy} {Q : MachineState → Prop} {D D' : MachineData}
    {p p' : Int64} (hQ : Q ⟨D', p'⟩) (hD : D' = D) (hp : p' = p) : Reaches step policy Q ⟨D, p⟩ := by
  subst hD hp
  exact .done hQ

/-- A load of the site lemma from the load hypothesis of the statement: the memory and the address are equal. -/
theorem read_congr {policy : CpuPolicy} {M M' : DataMem} {A A' : BitVec 64} {w : Width} {v : w.type}
    (h : readRam policy M A w = .ok v) (hM : M' = M) (hA : A' = A) : readRam policy M' A' w = .ok v := by
  subst hM hA
  exact h

/-- A store of the site lemma from the store hypothesis of the statement: memory, address and value are equal. -/
theorem write_congr {policy : CpuPolicy} {M M' : DataMem} {A A' : BitVec 64} {w : Width} {X X' : w.type}
    {m : DataMem} (h : writeRam policy M A w X = .ok m) (hM : M' = M) (hA : A' = A) (hX : X' = X) :
    writeRam policy M' A' w X' = .ok m := by
  subst hM hA hX
  exact h

/-! ## Closers of the meeting equations -/

open Lean.Parser.Tactic

/-- Normalize flag encodings in a scalar goal or an explicitly selected hypothesis.
The borrow rule requires equal modulus forms and a positive modulus. -/

syntax "lift_compose_flag_norm" (location)? : tactic
macro_rules
  | `(tactic| lift_compose_flag_norm $[$loc:location]?) =>
    `(tactic| simp -failIfUnchanged (disch := first | assumption | rfl | decide)
      [↓Lift.Tactic.Cond.borrow_mod_eq_lt, ↓Lift.Tactic.Cond.nocarry_mod_iff_le,
       Bool.beq_eq_decide_eq, Lift.Tactic.Cond.sub_zero_iff,
       Lift.Tactic.Cond.ofNat_decide, Lift.Tactic.Cond.ofNat_bool_eq_zero,
       Lift.Tactic.Cond.extract_replaceLow,
       UInt64.or_eq_zero_iff, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
       UInt64.toNat_mod, UInt8.toNat_toUInt64, UInt16.toNat_toUInt64,
       UInt32.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_toUInt16,
       UInt64.toNat_toUInt32] $[$loc]?)

/-- Reduce flag choices before the word solver. Equal conditions in words of
separate widths must take the same branch. -/
syntax "lift_compose_flag_eq" : tactic
macro_rules
  | `(tactic| lift_compose_flag_eq) =>
    `(tactic|
      (lift_compose_flag_norm
       simp -failIfUnchanged only [BitVec.replaceLow, BitVec.drop]
       repeat' first | split
       all_goals (simp_all -failIfUnchanged only [ite_true, ite_false]; bv_decide (config := { timeout := 10 }))))

/-- Prove a condition from one branch premise after the shared flag reduction. -/
syntax "lift_compose_flag_cond" ident : tactic
macro_rules
  | `(tactic| lift_compose_flag_cond $h:ident) =>
    `(tactic|
      (lift_compose_flag_norm at $h:ident ⊢
       simp -failIfUnchanged only [← UInt64.toNat_inj, UInt64.toNat_ofNat] at $h:ident ⊢
       first | assumption | omega))


/-- An equation of a composed term and a statement term (a field, an address, a stored value, a PC). The `bv_decide`
closers are for words. With `BitVec.replaceLow` unfolded, `bv_decide` comes before `ac_rfl`: the low byte of `rax` written
by `setne`, or the 16 bits written by `movw`, is `replaceLow` in the composed term and a mask and an `|||` in the
statement (N14), and on such a term `ac_rfl` takes 28 seconds (the instance `Std.LawfulIdentity`) and uses the heartbeats
of the proof (the `xorb` after two `setne` of `closestCopy` o114, N15). -/
syntax "lift_compose_eq" : tactic
macro_rules
  | `(tactic| lift_compose_eq) =>
    `(tactic| first
      | with_reducible rfl
      | (simp -implicitDefEqProofs only [lift_site, lift_addr]; done)
      | (simp -implicitDefEqProofs [lift_site, lift_flag, lift_addr]; done)
      | (simp only [BitVec.replaceLow, BitVec.drop]; bv_decide)
      | lift_compose_flag_eq
      | ac_rfl
      | grind
      | bv_decide)

/-- A condition of an exit from the branch hypothesis `h` of the composed PC. The last closer is `bv_decide`: the composed
condition `(v2 ^^^ rsi) <<< 16 = 0` of a `cmp` of 48 bits and the condition `v2 &&& m = rsi &&& m` of the statement are two
forms of one fact about words (N14). The composed condition of a `setne`, a `sete` and an 8-bit `xor` has
`BitVec.replaceLow`: it is unfolded as in `lift_compose_eq` (N15). -/
syntax "lift_compose_cond" ident : tactic
macro_rules
  | `(tactic| lift_compose_cond $h:ident) =>
    `(tactic| first
      | exact $h:ident
      | (simp -implicitDefEqProofs only [lift_flag] at $h:ident ⊢; exact $h:ident)
      | (simpa -implicitDefEqProofs [lift_site, lift_flag] using $h:ident)
      | grind
      | ((try simp only [BitVec.replaceLow, BitVec.drop] at $h:ident ⊢); bv_decide)
      | lift_compose_flag_cond $h:ident)

/-! ## Field form of a state -/

/-- The simp set of the site bodies (`Skel.Gen.Derive.siteContext`: the default set, `lift_site`, `lift_flag`), with an
explicit proof for each `rfl` theorem. With the implicit proof (the default), the kernel checks the step by definitional
equality, and on a `BitVec` sum with a large literal (`(x + 18446744073709551615#64).toNat` by `BitVec.toNat_add`) it
unfolds `Nat.add` on the literal: a kernel time-out (the `lea; addl` time-out of E1 and E2). -/
def normContext : MetaM Simp.Context := do
  let site ← (← getSimpExtension? `lift_site).get!.getTheorems
  let flag ← (← getSimpExtension? `lift_flag).get!.getTheorems
  Simp.mkContext (config := { implicitDefEqProofs := false }) (simpTheorems := #[← getSimpTheorems, site, flag])

/-- The fields of `Reg64s` and of `StatusFlags`, in constructor order (`reaches_fields` checks the order). -/
def regFields : Array Name :=
  #[`rax, `rbx, `rcx, `rdx, `rsi, `rdi, `rsp, `rbp, `r8, `r9, `r10, `r11, `r12, `r13, `r14, `r15]

def flagFields : Array Name := #[`cf, `pf, `af, `zf, `sf, `of]

/-- Projections of constructor applications reduced, also inside instance arguments (which `dsimp` does not visit). -/
def projInst (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if let .const n _ := x.getAppFn then
      if let some info ← getProjectionFnInfo? n then
        if let some s := x.getAppArgs[info.numParams]? then
          if s.isApp && (← isConstructorApp s) then
            return .visit (← whnfR x)
    return .continue)

/-- Projections of literals, `beta`, `eta` and `zeta` reduced. The result is definitionally equal. -/
def proj (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext (config := { proj := true, beta := true, eta := true, zeta := true })
  projInst (← dsimp e ctx).1

/-- The 24 fields of a state: the arguments of a literal, else projections (reduced). -/
def fieldsOf (D : Expr) : MetaM (Array Expr) := do
  let regs ← if D.isAppOfArity ``MachineData.mk 4 then pure (D.getArg! 0) else mkAppM ``MachineData.regs #[D]
  let zmms ← if D.isAppOfArity ``MachineData.mk 4 then pure (D.getArg! 1) else mkAppM ``MachineData.zmms #[D]
  let st ← if D.isAppOfArity ``MachineData.mk 4 then pure (D.getArg! 2) else mkAppM ``MachineData.status #[D]
  let dmem ← if D.isAppOfArity ``MachineData.mk 4 then pure (D.getArg! 3) else mkAppM ``MachineData.dmem #[D]
  let rs ← if regs.isAppOfArity ``Reg64s.mk 16 then pure regs.getAppArgs
    else regFields.mapM fun n => do proj (← mkAppM (``Reg64s ++ n) #[regs])
  let fs ← if st.isAppOfArity ``StatusFlags.mk 6 then pure st.getAppArgs
    else flagFields.mapM fun n => do proj (← mkAppM (``StatusFlags ++ n) #[st])
  return rs ++ #[← proj zmms] ++ fs ++ #[← proj dmem]

/-- The state literal of 24 fields. -/
def ofFields (xs : Array Expr) : Expr :=
  mkAppN (mkConst ``MachineData.mk)
    #[mkAppN (mkConst ``Reg64s.mk) (xs.extract 0 16), xs[16]!, mkAppN (mkConst ``StatusFlags.mk) (xs.extract 17 23),
      xs[23]!]

/-- Is `D` the literal of 24 fields? -/
def isFieldLit (D : Expr) : Bool :=
  D.isAppOfArity ``MachineData.mk 4 && (D.getArg! 0).isAppOfArity ``Reg64s.mk 16 &&
    (D.getArg! 2).isAppOfArity ``StatusFlags.mk 6

/-- Run `k` with 24 local field variables and their state literal. -/
def withFieldVars {α : Type} [Inhabited α] (k : Array Expr → Expr → TermElabM α) : TermElabM α := do
  let ty (c : Name) : Array Expr → TermElabM Expr := fun _ => pure (mkConst c)
  let decls : Array (Name × (Array Expr → TermElabM Expr)) :=
    (regFields.map fun n => (Name.mkSimple s!"x_{n}", ty ``UInt64)) ++ #[(`x_zmms, ty ``RegZmms)] ++
      (flagFields.map fun n => (Name.mkSimple s!"x_{n}", ty ``Bool)) ++ #[(`x_dmem, ty ``DataMem)]
  withLocalDeclsD decls fun xs => k xs (ofFields xs)

/-! ## Site lemmas -/

/-- The names of the theorems of a site. -/
def sitePrefix (step : Name) : Name := step ++ `compose
def fieldEqName (step : Name) (addr : Nat) : Name := sitePrefix step ++ Name.mkSimple s!"field{addr}"
def reachName (step : Name) (addr : Nat) : Name := sitePrefix step ++ Name.mkSimple s!"reach{addr}"

/-- Each exit state `done ⟨D, pc⟩` of a tree as `done ⟨literal of the 24 fields of D, pc⟩` (structure eta: the same term
up to definitional equality). -/
def etaExits (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if x.isAppOfArity ``Effects.done 1 then
      let s := x.appArg!
      let D ← mkAppM ``MachineState.data #[s]
      let pc ← mkAppM ``MachineState.pc #[s]
      return .done (← mkAppM ``Effects.done #[← mkAppM ``MachineState.mk #[ofFields (← fieldsOf D), pc]])
    return .continue)

/-- An access of a site, in program order: the value (or new memory) variable and the hypothesis type. -/
structure Access where
  isLoad : Bool
  fv : Expr
  hyp : Expr

/-- The walk of the tree of one site from the exec check to its `done`: the accesses, the undefined values, the exit
state and PC. A condition in the effects (not in the PC) or another node is an error. -/
partial def walk {α : Type} [Inhabited α] (policy : Expr) (e : Expr) (accs : Array Access) (undefs : Array Expr)
    (k : Array Access → Array Expr → Expr → Expr → TermElabM α) : TermElabM α := do
  let e := e.headBeta
  if e.isAppOfArity ``Effects.require_exec_access 2 then
    walk policy (mkApp (e.getArg! 1) (mkConst ``Unit.unit)) accs undefs k
  else if e.isAppOfArity ``MachineData.load 4 then
    let D := e.getArg! 0
    let r := e.getArg! 3
    let vty := (← whnfR (← inferType r)).bindingDomain!
    let n := (accs.filter (·.isLoad)).size
    withLocalDeclD (Name.mkSimple s!"v{n + 1}") vty fun v => do
      let lhs ← mkAppM ``readRam #[policy, ← proj (← mkAppM ``MachineData.dmem #[D]), ← proj (e.getArg! 1), e.getArg! 2]
      let hyp ← mkEq lhs (← okOf lhs v)
      walk policy (mkApp2 r v D) (accs.push ⟨true, v, hyp⟩) undefs k
  else if e.isAppOfArity ``MachineData.store 5 then
    let D := e.getArg! 0
    let n := (accs.filter (!·.isLoad)).size
    withLocalDeclD (Name.mkSimple s!"m{n + 1}") (mkConst ``DataMem) fun m => do
      let lhs ← mkAppM ``writeRam #[policy, ← proj (← mkAppM ``MachineData.dmem #[D]), ← proj (e.getArg! 1),
        e.getArg! 2, ← proj (e.getArg! 3)]
      let hyp ← mkEq lhs (← okOf lhs m)
      let D' ← mkAppM ``MachineData.mk #[← mkAppM ``MachineData.regs #[D], ← mkAppM ``MachineData.zmms #[D],
        ← mkAppM ``MachineData.status #[D], m]
      walk policy (mkApp (e.getArg! 4) D') (accs.push ⟨false, m, hyp⟩) undefs k
  else if e.isAppOfArity ``Effects.undefined 3 then
    withLocalDeclD (Name.mkSimple s!"u{undefs.size + 1}") (e.getArg! 0) fun u =>
      walk policy (mkApp (e.getArg! 2) u) accs (undefs.push u) k
  else if e.isAppOfArity ``ite 5 then
    throwError "site lemma: a condition in the effects{indentExpr (e.getArg! 1)}"
  else if e.isAppOfArity ``Effects.done 1 then
    let s := e.getArg! 0
    k accs undefs (← proj (← mkAppM ``MachineState.data #[s])) (← proj (← mkAppM ``MachineState.pc #[s]))
  else throwError "site lemma: a node that is not an access, a choice or an exit{indentExpr e}"
where
  okOf (lhs v : Expr) : MetaM Expr := do
    let_expr Except ε β := ← whnfR (← inferType lhs) | throwError "not an Except: {lhs}"
    mkAppOptM ``Except.ok #[ε, β, v]

/-- The number of `∃` in front of a proposition. -/
partial def countEx (e : Expr) : Nat :=
  if e.isAppOfArity ``Exists 2 then
    match e.getArg! 1 with
    | .lam _ _ b _ => 1 + countEx b
    | _ => 1
  else 0

/-- The proof of a site lemma from its field equation, on the goal after the intro of all binders. -/
def siteTac (eq : Name) (nl ns : Nat) : TacticM Unit := do
  let hx := mkIdent `hx
  let hr := mkIdent `hr
  let hnext := mkIdent `hnext
  let mut lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| Lift.Tactic.exec_iff $hx))
  for i in [0:nl] do
    let h := mkIdent (Name.mkSimple s!"hread{i + 1}")
    lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| Lift.Tactic.Compose.load_ok_iff' $h))
  for i in [0:ns] do
    let h := mkIdent (Name.mkSimple s!"hwrite{i + 1}")
    lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| Lift.Tactic.Compose.store_ok_iff' $h))
  lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| Lift.P2.Total.Handled.done_iff))
  lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| Lift.P2.Total.Handled.choice_iff))
  let c := mkIdent eq
  evalTactic (← `(tactic| refine Lift.Sem.Reaches.of_step fun r $hr:ident => ?_))
  evalTactic (← `(tactic| rw [$c:ident] at $hr:ident))
  -- no simprocs: the terms of `hr` stay the terms of the statement
  evalTactic (← `(tactic| set_option simprocs false in try dsimp only at $hr:ident))
  evalTactic (← `(tactic| set_option simprocs false in
    simp (disch := first | decide | rfl) only [$lemmas,*] at $hr:ident))
  let k ← withMainContext do
    pure (countEx (← instantiateMVars (← getLocalDeclFromUserName `hr).type))
  for _ in [0:k] do
    evalTactic (← `(tactic| obtain ⟨_, $hr:ident⟩ := $hr:ident))
  evalTactic (← `(tactic| subst $hr:ident))
  evalTactic (← `(tactic| exact ⟨_, rfl, $hnext:ident ..⟩))

/-- Add a theorem; the kernel checks it now. -/
def addThm (name : Name) (ty v : Expr) : TermElabM Unit := do
  let ty ← instantiateMVars ty
  let v ← instantiateMVars v
  if v.hasSorry || v.hasMVar then throwError "{name}: the proof has `sorry` or a metavariable"
  withOptions (fun o => Elab.async.set o false) do
    addDecl (.thmDecl { name, levelParams := [], type := ty, value := v })

/-- The field equation and the site lemma of the site equation `e` (N1) of `step`, for the code range `lo`, `hi`
(constants). -/
def addSiteLemma (step lo hi : Name) (e : Skel.Gen.Derive.SiteEq) : TermElabM Unit := do
  withFieldVars fun xs D0 => do
    let a ← mkNumeral (mkConst ``Int64) e.addr
    let s0 ← mkAppM ``MachineState.mk #[D0, a]
    let lhs ← mkAppM step #[s0]
    let B := e.body.beta #[D0]
    let e1 ← proj (← etaExits (← proj B))
    let (r, _) ← simp e1 (← normContext) #[← Simp.getSimprocs]
    let T := r.expr
    let h1 ← mkExpectedTypeHint (← mkEqRefl B) (← mkEq B e1)
    let prf ← mkEqTrans (mkApp (mkConst e.name) D0) (← mkEqTrans h1 (← r.getProof))
    let eqName := fieldEqName step e.addr
    addThm eqName (← mkForallFVars xs (← mkEq lhs T)) (← mkLambdaFVars xs prf)
    withLocalDecl `policy .implicit (mkConst ``CpuPolicy) fun policy => do
    withLocalDeclD `hx (← mkAppM ``SysV.ExecRange #[policy, mkConst lo, mkConst hi]) fun hx => do
    walk policy T #[] #[] fun accs undefs D' pc' => do
      let D' := ofFields (← fieldsOf D')
      let uses (x : Expr) := undefs.any fun u => x.containsFVar u.fvarId!
      if accs.any (uses ·.hyp) then throwError "site {e.addr}: an undefined value in an access"
      -- the hypothesis of access `j`: `hread<k>` for the `k`-th load, `hwrite<k>` for the `k`-th store
      let hypName (j : Nat) (acc : Access) : Name :=
        let k := ((accs.extract 0 (j + 1)).filter (·.isLoad == acc.isLoad)).size
        Name.mkSimple (if acc.isLoad then s!"hread{k}" else s!"hwrite{k}")
      let binders := accs.mapIdx fun j acc => (hypName j acc, acc.hyp)
      let nl := (accs.filter (·.isLoad)).size
      let ns := accs.size - nl
      withLocalDeclsDND binders fun hs => do
      withLocalDecl `Q .implicit (← mkArrow (mkConst ``MachineState) (mkSort 0)) fun Q => do
        let reach (s : Expr) : MetaM Expr := mkAppM ``Reaches #[mkConst step, policy, Q, s]
        let next ← reach (← mkAppM ``MachineState.mk #[D', pc'])
        let us := undefs.filter fun u => next.containsFVar u.fvarId!
        withLocalDeclD `hnext (← mkForallFVars us next) fun hnext => do
          let vs := (accs.zip hs).flatMap fun (acc, h) => #[acc.fv, h]
          let ty ← instantiateMVars (← mkForallFVars (#[policy, hx] ++ xs ++ vs ++ #[Q, hnext]) (← reach s0))
          let mv ← mkFreshExprMVar ty
          let (_, g) ← mv.mvarId!.introNP (2 + xs.size + vs.size + 2)
          let gs ← Term.withoutErrToSorry <| Tactic.run g (siteTac eqName nl ns)
          unless gs.isEmpty do throwError "site {e.addr}: the site lemma proof leaves goals"
          addThm (reachName step e.addr) ty mv

/-- The site lemmas of `step` for the code range `lo`, `hi`, at each address of the table of `step` in `[from, to)`. The
sites that have no lemma, each with the reason. -/
def addSiteLemmas (step lo hi : Name) (lo' hi' : Nat) : TermElabM (List (Nat × String)) := do
  let table ← Skel.Gen.Derive.tableSites step
  -- an address is in the table once for each label at it and once for its instruction; `dispatch` takes the first
  let addrs := ((table.map (·.1)).filter fun a => lo' ≤ a && a < hi').eraseDups
  let eqs ← Skel.Gen.Derive.siteEqs step (sitePrefix step ++ `site) addrs
  eqs.filterMapM fun r => do
    match r with
    | .error err => pure (some (errAddr err, s!"site equation: {repr err}"))
    | .ok e =>
      tryCatchRuntimeEx (do withCurrHeartbeats (addSiteLemma step lo hi e); pure none) fun ex => do
        pure (some (e.addr, (← ex.toMessageData.toString)))
where
  errAddr : Skel.Gen.Derive.SiteError → Nat
    | .notASite a | .limit a _ | .failed a _ => a

/-- `#lift_site_lemmas step lo hi from to`: the site lemmas of `step` for the code range `lo`, `hi` (constants), at the
sites of the table in `[from, to)`. A site with no lemma is a warning that names it. -/
syntax (name := liftSiteLemmas) "#lift_site_lemmas " ident ident ident num num : command

open Command in
@[command_elab liftSiteLemmas] def elabLiftSiteLemmas : CommandElab
  | `(#lift_site_lemmas $step $lo $hi $a $b) => liftTermElabM do
    let step ← realizeGlobalConstNoOverloadWithInfo step
    let lo ← realizeGlobalConstNoOverloadWithInfo lo
    let hi ← realizeGlobalConstNoOverloadWithInfo hi
    let fails ← addSiteLemmas step lo hi a.getNat b.getNat
    for (addr, msg) in fails do logWarning m!"#lift_site_lemmas: no site lemma at {addr}: {msg}"
  | _ => throwUnsupportedSyntax

/-! ## The block tactic -/

/-- The value of a PC, if it evaluates to a numeral. -/
def evalPC (p : Expr) : MetaM (Option Nat) := do
  if p.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (p.getArg! 1).rawNatLit? then return some n
  try
    let r ← whnf (← mkAppM ``BitVec.toNat #[← mkAppM ``Int64.toBitVec #[p]])
    return r.rawNatLit?
  catch _ => return none

/-- The context of a block proof: the step, policy, postcondition, the code range hypothesis, the access hypotheses in
order, and the exit hypotheses. -/
structure Ctx where
  step : Name
  policy : Expr
  Q : Expr
  hx : Expr
  accs : Array Expr
  exits : Array Expr

/-- Where two terms differ. -/
inductive Diff where
  /-- The same term. -/
  | same
  /-- The same explicit arguments everywhere: they differ only in implicit or instance arguments. -/
  | implicitOnly
  /-- The first pair of subterms that differ in an explicit position. -/
  | at (x y : Expr)

/-- The first pair of subterms where `a` and `b` differ, in any argument (a diagnostic). -/
partial def firstDiffAll (a b : Expr) : Expr × Expr :=
  if a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
    match (a.getAppArgs.zip b.getAppArgs).find? (fun (x, y) => x != y) with
    | some (x, y) => firstDiffAll x y
    | none => (a, b)
  else (a, b)

/-- The smallest pairs of subterms where `a` and `b` differ, in any argument, at most `n` of them. -/
partial def diffPairs (a b : Expr) (n : Nat) (acc : Array (Expr × Expr)) : Array (Expr × Expr) :=
  if a == b || acc.size ≥ n then acc
  else if a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
    (a.getAppArgs.zip b.getAppArgs).foldl (fun acc (x, y) => diffPairs x y n acc) acc
  else acc.push (a, b)

/-- The first pair of subterms where `a` and `b` differ, descending through the explicit arguments of the same head. A
difference in an implicit or instance argument (a type index, the instance of a numeral) is not followed: a rewrite there
would change an index without its term. -/
partial def firstDiff (a b : Expr) : MetaM Diff := do
  if a == b then return .same
  let n := a.getAppNumArgs
  if a.getAppFn == b.getAppFn && n == b.getAppNumArgs && n > 0 then
    let info ← getFunInfoNArgs a.getAppFn n
    let mut implicit := false
    for i in [0:n] do
      let x := a.getArg! i
      let y := b.getArg! i
      if x == y then continue
      let explicit := match info.paramInfo[i]? with
        | some p => p.binderInfo.isExplicit
        | none => true
      if !explicit then implicit := true; continue
      match ← firstDiff x y with
      | .same => pure ()
      | .implicitOnly => implicit := true
      | d@(.at _ _) => return d
    return if implicit then .implicitOnly else .same
  return .at a b

/-- With `lift_block_split.checkParts`: the kernel check of `prf` alone (over the local context), its time traced. A
diagnostic: the environment does not change. -/
def checkPart (what : String) (prf : Expr) : MetaM Unit := do
  unless lift_block_split.checkParts.get (← getOptions) do return
  let prf ← instantiateMVars prf
  let ty ← instantiateMVars (← inferType prf)
  let xs := (← getLCtx).getFVars
  let ty ← mkForallFVars xs ty
  let v ← mkLambdaFVars xs prf
  let t0 ← IO.monoMsNow
  let r ← tryCatchRuntimeEx
    (withoutModifyingEnv do
      withOptions (fun o => Elab.async.set o false) do
        addDecl (.thmDecl { name := `_lift_block_split_part, levelParams := [], type := ty, value := v })
      pure m!"ok")
    fun ex => pure ex.toMessageData
  trace[lift_block_split] "checkParts: {what}: {r}, {(← IO.monoMsNow) - t0} ms"

/-- Each numeral `@OfNat.ofNat α n inst` whose instance is for another index `n'` (`dsimp` rewrites `n` and not the
instance, for example `(from_result v f).cf` to `f.cf` in the numeral of a `Bool.toNat`) with the instance of `OfNat α n`.
The result is definitionally equal. Without it two normal forms can differ only in the index of an instance, and the
check of that index by `isDefEq` passes `maxRecDepth`. -/
def canonInst (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if x.isAppOfArity ``OfNat.ofNat 3 then
      let n := x.getArg! 1
      if n.isRawNatLit then return .done x
      let instTy ← whnfR (← inferType (x.getArg! 2))
      if instTy.isAppOfArity ``OfNat 2 && instTy.getArg! 1 != n then
        let some inst ← synthInstance? (← mkAppM ``OfNat #[x.getArg! 0, n]) | return .done x
        return .done (mkApp3 x.getAppFn (x.getArg! 0) n inst)
    return .continue)

/-- A term in the normal form of the site bodies (`simp` with `normContext` and the default simprocs, then
`canonInst`): the term and a proof of `e = term` (`none` when it is `e`). -/
def normTerm (e : Expr) : MetaM (Expr × Option Expr) := do
  if e.isFVar then return (e, none)
  let r? ← tryCatchRuntimeEx (some <$> simp e (← normContext) #[← Simp.getSimprocs]) fun ex => do
    trace[lift_block_split] "normTerm: {ex.toMessageData} at{indentExpr e}"
    pure none
  let (e1, h1) := match r? with
    | some (r, _) => (r.expr, r.proof?)
    | none => (e, none)
  let e2 ← canonInst e1
  if e2 == e then return (e, none)
  let h1 ← match h1 with
    | some h => pure h
    | none => mkExpectedTypeHint (← mkEqRefl e) (← mkEq e e1)
  if e2 == e1 then return (e1, some h1)
  return (e2, some (← mkEqTrans h1 (← mkExpectedTypeHint (← mkEqRefl e1) (← mkEq e1 e2))))

/-- Reducible definitional equality; a runtime error (as `maxRecDepth`) is `false`. -/
def redDefEq (a b : Expr) : MetaM Bool :=
  tryCatchRuntimeEx (withNewMCtxDepth (withReducible (isDefEq a b))) fun ex => do
    trace[lift_block_split] "redDefEq: {ex.toMessageData}"
    pure false

/-- A proof of `a = b` by `lift_compose_eq` (its runtime errors, as `maxRecDepth`, caught), or why there is none. -/
def closeEq (a b : Expr) : TacticM (Except MessageData Expr) := do
  let mv ← mkFreshExprSyntheticOpaqueMVar (← mkEq a b)
  let saved ← saveState
  let why ← tryCatchRuntimeEx
    (do
      let gs ← Term.withoutErrToSorry <| Tactic.run mv.mvarId! (evalTactic (← `(tactic| lift_compose_eq)))
      pure (if gs.isEmpty then none else some m!"goals left"))
    fun ex => pure (some ex.toMessageData)
  match why with
  | none => return .ok (← instantiateMVars mv)
  | some m => saved.restore; return .error m

/-- A numeral: a raw literal, `OfNat.ofNat _ n _` or `BitVec.ofNat w n` of a raw literal `n`. -/
def isNumeral (e : Expr) : Bool :=
  e.isRawNatLit || (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).isRawNatLit) ||
    (e.isAppOfArity ``BitVec.ofNat 2 && (e.getArg! 1).isRawNatLit)

mutual
/-- A proof of `a = b`: syntactic, reducible definitional equality, or the normal forms (`normTerm`) of both sides
joined by `bridge`; else an error naming `what`. Two numerals that differ are an error at once. -/
partial def proveEq (what : String) (a b : Expr) : TacticM Expr := do
  if a == b then return ← mkEqRefl a
  trace[lift_block_split] "{what}: {a} = {b}"
  if ← redDefEq a b then return ← mkEqRefl a
  if isNumeral a && isNumeral b then
    throwError "lift_block_split: {what}: no proof of{indentExpr (← mkEq a b)}\nthe numerals differ"
  let (na, ha) ← normTerm a
  let (nb, hb) ← normTerm b
  let hm ← bridge what na nb 64
  let ha ← match ha with | some h => pure h | none => mkEqRefl a
  let hb ← match hb with | some h => pure h | none => mkEqRefl b
  let prf ← mkEqTrans ha (← mkEqTrans hm (← mkEqSymm hb))
  checkPart what prf
  return prf

/-- A proof of `a = b` for two terms in normal form. At the first pair of subterms `x`, `y` where they differ
(`firstDiff`), a proof of `x = y` rewrites each `x` in `a` to `y` (`congrArg`), and so on, at most `fuel` times. The
normal forms can differ in a place that `simp` does not visit (the numeral of an `OfNat.ofNat`, an instance). Where
the heads differ, `lift_compose_eq` proves the equation. -/
partial def bridge (what : String) (a b : Expr) (fuel : Nat) : TacticM Expr := do
  if a == b then return ← mkEqRefl a
  if ← redDefEq a b then return ← mkEqRefl a
  let d ← firstDiff a b
  let fail (why : MessageData) : TacticM Expr := do
    let (x, y) := match d with
      | .at x y => (x, y)
      | _ => firstDiffAll a b
    trace[lift_block_split] "{what}: {why}"
    throwError "lift_block_split: {what}: no proof of{indentExpr (← mkEq a b)}\nthe normal forms differ first at{indentExpr x}\nand{indentExpr y}"
  match d with
  | .same => mkEqRefl a
  | .implicitOnly =>
    -- the explicit arguments are equal: each smallest difference by definitional equality (not the whole terms: on
    -- these terms `isDefEq` passes `maxRecDepth`); then the terms are definitionally equal argument by argument
    let pairs := diffPairs a b 16 #[]
    let ok ← pairs.allM fun (x, y) =>
      tryCatchRuntimeEx (withNewMCtxDepth (withTransparency .default (isDefEq x y))) fun _ => pure false
    if ok && pairs.size < 16 then
      mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)
    else match ← closeEq a b with
      | .ok h => pure h
      | .error m => fail m
  | .at x y =>
    if fuel == 0 || (x == a && y == b) || (isNumeral x && isNumeral y) then
      return ← match ← closeEq a b with
        | .ok h => pure h
        | .error m => fail m
    -- The pair `x`, `y` can have no proof while the whole terms are equal: `rsp - 8 - 8` and `rsp - 16` first differ at
    -- `rsp - 8` and `rsp` (the second push of a block, a call after a push). Then the closers prove `a = b` as it is,
    -- and when they fail, the error is the one of the pair.
    let saved ← saveState
    let r : Except Exception Expr ← try pure (.ok (← proveEq what x y)) catch ex => pure (.error ex)
    let hxy ← match r with
      | .ok h => pure h
      | .error ex =>
        saved.restore
        match ← closeEq a b with
        | .ok h => return h
        | .error _ => throw ex
    let ty ← inferType x
    -- each occurrence of `x` in `a`, syntactically (`kabstract` tests candidates by `isDefEq`, which passes
    -- `maxRecDepth` on these terms)
    let motive ← withLocalDeclD `z ty fun z => do
      mkLambdaFVars #[z] (a.replace fun e => if e == x then some z else none)
    let a' := motive.beta #[y]
    let h1 ← mkCongrArg motive hxy
    let h1 ← mkExpectedTypeHint h1 (← mkEq a a')
    mkEqTrans h1 (← bridge what a' b (fuel - 1))
end

/-- A proof of the equation of two constructor terms of the same constructor, by congruence of the arguments; other
terms by `proveEq`. -/
partial def proveEqTree (what : String) (a b : Expr) : TacticM Expr := do
  if a == b then return ← mkEqRefl a
  let ctorOf (x : Expr) : MetaM (Option Name) := do
    let .const c _ := x.getAppFn | return none
    if (← getEnv).isConstructor c then return some c else return none
  match ← ctorOf a, ← ctorOf b with
  | some c, some c' =>
    if c == c' && a.getAppNumArgs == b.getAppNumArgs then
      let mut prf ← mkEqRefl a.getAppFn
      for (x, y) in a.getAppArgs.zip b.getAppArgs do
        let h ← proveEqTree what x y
        prf ← mkCongr prf h
      return prf
    else proveEq what a b
  | _, _ => proveEq what a b

/-- A proof of the condition `c` of an exit from one of the branch hypotheses `bs` by `lift_compose_cond`. -/
def proveCond (bs : Array Expr) (c : Expr) : TacticM (Option Expr) := do
  for b in bs do
    let mv ← mkFreshExprSyntheticOpaqueMVar c
    let saved ← saveState
    let name ← b.fvarId!.getUserName
    let ok ← tryCatchRuntimeEx
      (do
        let gs ← Term.withoutErrToSorry <| Tactic.run mv.mvarId! do
          evalTactic (← `(tactic| lift_compose_cond $(mkIdent name)))
        pure gs.isEmpty)
      fun _ => pure false
    if ok then return some (← instantiateMVars mv)
    saved.restore
  return none

/-- A proof of the fact `f.g = v` of a kept flag of an exit (L2-FLAGS), with `f` the flags of the exit state (a literal
`StatusFlags.mk`): the field of the literal and the value `v` of the statement are one equation of `proveEq`. `none` when the
fact is not of this form or has no proof. -/
def proveKeptFlag (ty : Expr) : TacticM (Option Expr) := do
  let some (bty, lhs, rhs) := ty.eq? | return none
  unless bty.isConstOf ``Bool do return none
  let some n := lhs.getAppFn.constName? | return none
  unless flagFields.any (``StatusFlags ++ · == n) && lhs.getAppNumArgs == 1 do return none
  let saved ← saveState
  try
    let lhs' ← whnfR lhs
    let prf ← proveEq "a kept flag of an exit" lhs' rhs
    return some (← mkExpectedTypeHint prf ty)
  catch _ =>
    saved.restore
    return none

/-- Close the goal `Reaches step policy Q ⟨D, p⟩` (with `D` a field literal) by an exit hypothesis at its PC. -/
def closeExit (c : Ctx) (bs : Array Expr) (g : MVarId) (D p : Expr) (pn : Option Nat) (i : Nat) :
    TacticM Bool := g.withContext do
  trace[lift_block_split] "closeExit at {p}, {c.exits.size} exits"
  for h in c.exits do
    let hty ← instantiateMVars (← inferType h)
    let saved ← saveState
    let (ms, _, body) ← forallMetaTelescopeReducing hty
    let body ← instantiateMVars body
    let isTrap := body.isConstOf ``False
    -- the PC of the exit
    let pe? : Option Expr := if isTrap then none else
      if body.isApp && body.appFn! == c.Q then some (body.appArg!) else none
    if !isTrap && pe?.isNone then trace[lift_block_split] "exit {h}: not an exit of Q{indentExpr body}"; saved.restore; continue
    let mut ok := true
    let mut hp : Option Expr := none
    if let some st := pe? then
      let st ← whnfR st
      let pe := st.appArg!
      match pn, ← evalPC pe with
      | some n, some m =>
        if n != m then ok := false
        else if pe == p then hp := some (← mkEqRefl pe)
        else hp := some (← mkDecideProof (← mkEq pe p))
      | _, _ =>
        if pn.isSome then ok := false
        else
          try hp := some (← proveEq "the PC of an exit" pe p) catch _ => ok := false
    if !ok then trace[lift_block_split] "exit {h}: the PC differs"; saved.restore; continue
    -- the conditions and the flags
    let mut condsOk := true
    for m in ms do
      if ← m.mvarId!.isAssigned then continue
      let ty ← instantiateMVars (← inferType m)
      if ty.isConstOf ``StatusFlags then
        m.mvarId!.assign (D.getArg! 2)
      else if ← isProp ty then
        match ← proveCond bs ty with
        | some prf => m.mvarId!.assign prf
        | none =>
          -- a kept flag of the exit (L2-FLAGS): `f.cf = v`, with `f` the flags of the exit state
          match ← proveKeptFlag ty with
          | some prf => m.mvarId!.assign prf
          | none =>
            let bts ← bs.mapM fun b => do instantiateMVars (← inferType b)
            trace[lift_block_split] "no proof of the condition{indentExpr ty}\nfrom the branches{bts.toList}"
            condsOk := false
      else condsOk := false
    if !condsOk then trace[lift_block_split] "exit {h}: a condition has no proof"; saved.restore; continue
    if i < c.accs.size then
      throwError "lift_block_split: an exit with the access hypothesis {c.accs[i]!} not used: the block has fewer accesses"
    let hq ← instantiateMVars (mkAppN h ms)
    if isTrap then
      g.assign (← mkFalseElim (← g.getType) hq)
      return true
    let some st := pe? | unreachable!
    let st ← instantiateMVars (← whnfR st)
    let D' ← zetaReduce (← instantiateMVars st.appFn!.appArg!)
    let hD ← proveEqTree "a field of an exit state" D' D
    let some hpc := hp | unreachable!
    let pe := st.appArg!
    let prf ← mkAppOptM ``exit_eq #[mkConst c.step, c.policy, c.Q, D, D', p, pe, hq, hD, hpc]
    g.assign prf
    return true
  return false

/-- The goal `Reaches step policy Q ⟨D', p'⟩` after a site, with each field of `D'` that is not a field `prev` of the
state before the site, and the PC, in normal form (`normTerm`). The composed terms then stay in the form of the
whole-block terms, and the terms do not grow by projections of literals. -/
def normalize (c : Ctx) (g : MVarId) (prev : Array Expr) : TacticM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr Reaches _ _ _ s := ty | throwError "lift_block_split: the goal is not `Reaches`{indentExpr ty}"
  let s ← whnfR s
  let D := s.appFn!.appArg!
  let p := s.appArg!
  let fs ← fieldsOf D
  let rs ← fs.mapM fun f => if prev.contains f then pure (f, none) else normTerm f
  let (p', hp?) ← normTerm p
  if rs.all (·.2.isNone) && hp?.isNone then return g
  let D' := ofFields (rs.map (·.1))
  -- `D = D'` by congruence of the fields
  let fe ← (fs.zip rs).mapM fun (f, r) => match r.2 with
    | some h => pure h
    | none => mkEqRefl f
  let cong (fn : Expr) (hs : Array Expr) : MetaM Expr := do
    hs.foldlM (fun acc h => mkCongr acc h) (← mkEqRefl fn)
  let hRegs ← cong (mkConst ``Reg64s.mk) (fe.extract 0 16)
  let hSt ← cong (mkConst ``StatusFlags.mk) (fe.extract 17 23)
  let hD ← cong (mkConst ``MachineData.mk) #[hRegs, fe[16]!, hSt, fe[23]!]
  let hp ← match hp? with
    | some h => pure h
    | none => mkEqRefl p
  let g' ← mkFreshExprSyntheticOpaqueMVar
    (← mkAppM ``Reaches #[mkConst c.step, c.policy, c.Q, ← mkAppM ``MachineState.mk #[D', p']])
  checkPart "the normal form after a site" hD
  checkPart "the normal form of the PC after a site" hp
  g.assign (← mkAppOptM ``reaches_congr #[mkConst c.step, c.policy, c.Q, D, D', p, p', hD, hp, g'])
  return g'.mvarId!

/-- The proof of the goal `g` from the access hypothesis `i` on; `n` sites so far. -/
partial def run (c : Ctx) (bs : Array Expr) (g : MVarId) (i n : Nat) : TacticM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  trace[lift_block_split] "site {n}, access {i}: {ty.appArg!.appArg!}"
  let_expr Reaches _ _ _ s := ty | throwError "lift_block_split: the goal is not `Reaches`{indentExpr ty}"
  let s ← whnfR s
  let D := s.appFn!.appArg!
  let p := s.appArg!
  -- a branch
  if p.isAppOfArity ``ite 5 then
    let cnd := p.getArg! 1
    let mk (hyp : Expr) (pc : Expr) : MetaM Expr := do
      let t ← mkAppM ``Reaches #[mkConst c.step, c.policy, c.Q, ← mkAppM ``MachineState.mk #[D, pc]]
      mkFreshExprSyntheticOpaqueMVar (← mkArrow hyp t)
    let h1 ← mk cnd (p.getArg! 3)
    let h2 ← mk (mkNot cnd) (p.getArg! 4)
    g.assign (← mkAppOptM ``reaches_ite
      #[mkConst c.step, c.policy, c.Q, D, cnd, p.getArg! 2, p.getArg! 3, p.getArg! 4, h1, h2])
    for h in [h1, h2] do
      let (hc, g') ← h.mvarId!.intro `hc
      run c (bs.push (mkFVar hc)) g' i n
    return
  -- the start: the state as the literal of its fields
  unless isFieldLit D do
    let D' := ofFields (← fieldsOf D)
    let h ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``Reaches #[mkConst c.step, c.policy, c.Q, ← mkAppM ``MachineState.mk #[D', p]])
    g.assign (← mkAppOptM ``reaches_fields #[mkConst c.step, c.policy, c.Q, D, p, h])
    return ← run c bs h.mvarId! i n
  let pn ← evalPC p
  if n > 0 then
    if ← closeExit c bs g D p pn i then return
  let some a := pn | throwError "lift_block_split: no exit and no site at the PC{indentExpr p}"
  let L := reachName c.step a
  unless (← getEnv).contains L do
    throwError "lift_block_split: no site lemma {L} (`#lift_site_lemmas`), and no exit at this PC"
  -- the PC as the numeral of the site lemma
  let an ← mkNumeral (mkConst ``Int64) a
  let g ← if p == an then pure g else do
    let h ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``Reaches #[mkConst c.step, c.policy, c.Q, ← mkAppM ``MachineState.mk #[D, an]])
    g.assign (← mkAppOptM ``reaches_pc
      #[mkConst c.step, c.policy, c.Q, D, p, an, ← mkDecideProof (← mkEq p an), h])
    pure h.mvarId!
  -- the site lemma at the fields of `D`
  let mut args : Array Expr := #[c.policy, c.hx] ++ (← fieldsOf D)
  let mut lt ← instantiateForall (← inferType (mkConst L)) args
  let mut i := i
  while true do
    let .forallE _ dom _ bi := lt | throwError "lift_block_split: {L}: unexpected type{indentExpr lt}"
    if bi.isImplicit then break  -- `{Q}`
    -- an access: its value, then its hypothesis
    let some h := c.accs[i]? | throwError "lift_block_split: {L}: no access hypothesis left for an access{indentExpr dom}
if the PC is an exit of the statement, no exit hypothesis proves it (`set_option trace.lift_block_split true` shows why)"
    let hty ← instantiateMVars (← inferType h)
    let some (_, lhs, rhs) := hty.eq? | throwError "lift_block_split: not an access hypothesis{indentExpr hty}"
    let val := rhs.appArg!
    lt := lt.bindingBody!.instantiate1 val
    args := args.push val
    let .forallE _ hdom _ _ := lt | throwError "lift_block_split: {L}: no access hypothesis binder"
    let some (_, blhs, _) := hdom.eq? | throwError "lift_block_split: {L}: not an access binder{indentExpr hdom}"
    unless blhs.getAppFn == lhs.getAppFn && blhs.getAppNumArgs == lhs.getAppNumArgs do
      throwError "lift_block_split: {L}: the access hypothesis {h} is of another kind{indentExpr hty}"
    let ba := blhs.getAppArgs
    let ha := lhs.getAppArgs
    unless ← isDefEq ba[3]! ha[3]! do
      throwError "lift_block_split: {L}: the access hypothesis {h} has another width{indentExpr hty}"
    let hM ← proveEq s!"the memory of access {i + 1}" ba[1]! ha[1]!
    let hA ← proveEq s!"the address of access {i + 1}" ba[2]! ha[2]!
    let prf ← if blhs.isAppOf ``readRam then
        mkAppOptM ``read_congr #[none, none, none, none, none, none, none, h, hM, hA]
      else
        let hX ← proveEq s!"the stored value of access {i + 1}" ba[4]! ha[4]!
        mkAppOptM ``write_congr #[none, none, none, none, none, none, none, none, none, h, hM, hA, hX]
    let prf ← mkExpectedTypeHint prf hdom
    lt := lt.bindingBody!.instantiate1 prf
    args := args.push prf
    i := i + 1
  args := args.push c.Q
  lt := lt.bindingBody!.instantiate1 c.Q
  let .forallE _ nextTy _ _ := lt | throwError "lift_block_split: {L}: no `hnext` binder"
  let hnext ← mkFreshExprSyntheticOpaqueMVar nextTy
  let prf := mkAppN (mkConst L) (args.push hnext)
  unless ← isDefEq (← inferType prf) (← g.getType) do
    throwError "lift_block_split: {L}: the site lemma does not fit the goal{indentExpr (← g.getType)}"
  g.assign prf
  let (_, g') ← hnext.mvarId!.intros
  let g' ← normalize c g' (← fieldsOf D)
  run c bs g' i (n + 1)

/-- The context of the goal: the step, policy, `Q`, the code range hypothesis, and the hypotheses of the accesses and
exits in the order of the local context. -/
def ctxOf (g : MVarId) : TacticM Ctx := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr Reaches step policy Q _ := ty | throwError "lift_block_split: the goal is not `Reaches`{indentExpr ty}"
  let some step := step.constName? | throwError "lift_block_split: the step is not a constant{indentExpr step}"
  let mut hx? := none
  let mut accs := #[]
  let mut exits := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let t ← instantiateMVars ldecl.type
    if t.isAppOf ``SysV.ExecRange then hx? := some ldecl.toExpr
    else if let some (_, lhs, rhs) := t.eq? then
      if (lhs.isAppOf ``readRam || lhs.isAppOf ``writeRam) && rhs.isAppOf ``Except.ok then
        accs := accs.push ldecl.toExpr
    else
      let body := t.getForallBody
      if body.isConstOf ``False || (body.isApp && body.appFn! == Q) then
        if t.isForall then exits := exits.push ldecl.toExpr
  let some hx := hx? | throwError "lift_block_split: no `SysV.ExecRange` hypothesis"
  return { step, policy, Q, hx, accs, exits }

/-- `lift_block_split`: the split proof of a block statement (see the module comment). It closes the goal or fails. -/
syntax "lift_block_split" : tactic
elab_rules : tactic
  | `(tactic| lift_block_split) => do
    let g ← getMainGoal
    let c ← ctxOf g
    run c #[] g 0 0
    replaceMainGoal []

end Lift.Tactic.Compose
