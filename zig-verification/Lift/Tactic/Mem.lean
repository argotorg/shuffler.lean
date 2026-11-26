module

public import Lift.Tactic.MemLemmas
public meta import Lean.Elab.Tactic
public meta import VerifiedNix.MemSimp

@[expose] public section

/-! `room_mem`: the memory side goals of a block lemma about a stack room.

The goals that it closes, with a fact `room : SysV.StackRoom policy s n` (any number of such
facts) in the context:

1. `readRam policy M a .W64 = .ok v`;
2. `writeRam policy M a .W64 v = .ok M'` (`M'` may be a metavariable);
3. `Mem.loadInt M a 8 ≠ none`;
4. `SysV.Outside s n M`.

`M` is the start memory `s.data.dmem`, a chain of `Mem.storeInt` of one word each on it, or a
memory with a fact about it (see below). `a` is a slot `rsp - k` of the room (`8 ≤ k ≤ n`, `8 ∣ k`;
a read of the word at `rsp` goes through a fact about the start memory and `Outside`).

The steps:

* `prep`: the equations `x.regs.rsp = e` of the context rewrite the goal, and `UInt64.toBitVec` of a
  sum or a difference is pushed to the bits, so that all addresses are linear in the atoms of the
  start state (`d.regs.rsp.toBitVec - 8` with `hsp : d.regs.rsp = s₀.data.regs.rsp - 24` becomes
  `s₀.data.regs.rsp.toBitVec - 24#64 - 8`).
* The goal is cut into side goals by a lemma of `Lift/Tactic/MemLemmas.lean`. An address equation
  is proved from the linear forms of the two sides (`MemSimp.reify`), never by a search: the
  coefficients of the atoms must be equal, and the constants must be equal modulo `2 ^ 64`.
  `k` of a slot is the constant difference of the address and `rsp`.
* A load through a chain of stores is `mem_simp` (`MemSimp.memSimpGoal`).
* A load that stays, `Mem.loadInt M₀ a 8`, is closed by the room (`M₀` is the start memory), by a
  fact `Mem.loadInt M₀ a' 8 ≠ none`, or by `Outside` (the word at `rsp`).
* A read whose word is not stored in the chain is closed by a fact
  `readRam policy M₀ a' .W64 = .ok v` of the context, when the chain does not touch the word.

Each step is bounded: the tactic goes down the chain once, and tries each fact of the context at
most once. When it fails, `room_mem` gives an error with the side goals that stay (normalized by
`prep` and `mem_simp`); `room_mem_side` leaves these goals instead. -/

namespace Lift.Tactic.Room

open Lean Meta Elab Tactic
open Lift.P2.Total Lift.Sem

/-- A fact `StackRoom policy s n` of the context: the fact, the policy, `s.data.dmem`,
`s.data.regs.rsp` (a `UInt64`), `s.data.regs.rsp.toBitVec`, and `n`. -/
meta structure Room where
  pf : Expr
  policy : Expr
  dmem : Expr
  rspU : Expr
  rsp : Expr
  n : Nat

/-- The rooms and the other facts of the context (a fact and its type). -/
meta structure Env where
  rooms : Array Room
  hyps : Array (Expr × Expr)

meta def ty64 : Expr := mkApp (mkConst ``BitVec) (mkNatLit 64)

meta def mkRoom? (pf ty : Expr) : MetaM (Option Room) := do
  unless ty.isAppOfArity ``SysV.StackRoom 3 do return none
  let some n ← (evalNat ty.appArg!).run | return none
  let s := ty.appFn!.appArg!
  let data ← mkAppM ``MachineState.data #[s]
  let dmem ← mkAppM ``MachineData.dmem #[data]
  let rspU ← mkAppM ``Reg64s.rsp #[← mkAppM ``MachineData.regs #[data]]
  let rsp ← mkAppM ``UInt64.toBitVec #[rspU]
  return some { pf, policy := ty.appFn!.appFn!.appArg!, dmem, rspU, rsp, n }

meta def mkEnv : MetaM Env := do
  let mut rooms := #[]
  let mut hyps := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    hyps := hyps.push (d.toExpr, ty)
    if let some r ← mkRoom? d.toExpr ty then rooms := rooms.push r
  return { rooms, hyps }

/-! ## Addresses -/

/-- `k` with `a = r - k` modulo `2 ^ 64`, when `a` and `r` have the same atoms. -/
meta def offset (r a : Expr) : MetaM (Option Nat) := do
  let (((_, la), (_, lr)), atoms) ← (do
    let x ← MemSimp.reify true 64 ty64 a
    let y ← MemSimp.reify true 64 ty64 r
    return (x, y)).run #[]
  unless (List.range atoms.size).all fun i => la.coeff i == lr.coeff i do return none
  return some ((lr.const - la.const) % (2 ^ 64 : Nat)).toNat

/-- A proof of `a = b` when the two have the same atoms with the same coefficients, and the
constants agree modulo `2 ^ 64`. -/
meta def addrEq (a b : Expr) : MetaM (Option Expr) := do
  let ((((ea, la), (eb, lb))), atoms) ← (do
    let x ← MemSimp.reify true 64 ty64 a
    let y ← MemSimp.reify true 64 ty64 b
    return (x, y)).run #[]
  unless (List.range atoms.size).all fun i => la.coeff i == lb.coeff i do return none
  unless ((la.const - lb.const) % (2 ^ 64 : Nat)) == 0 do return none
  let ρ ← mkListLit ty64 atoms.toList
  let p := mkAppN (mkConst ``addr_eq) #[mkNatLit 64, ρ, ea, eb, MemSimp.eqTrue, MemSimp.eqTrue]
  let expected ← mkEq a b
  unless ← isDefEq (← inferType p) expected do return none
  return some (← mkExpectedTypeHint p expected)

/-! ## The preparation -/

/-- Rewrites the goal with the equations `x.regs.rsp = e` of the context, and moves
`UInt64.toBitVec` to the bits of a sum or a difference. An equation whose left side is the `rsp` of
a room is not used. -/
meta def prep (env : Env) (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let mut thms : SimpTheorems := {}
  for n in [``UInt64.toBitVec_sub, ``UInt64.toBitVec_add, ``UInt64.toBitVec_ofNat] do
    thms ← thms.addConst n
  for (pf, ty) in env.hyps do
    let some (_, lhs, rhs) := ty.eq? | continue
    unless lhs.isAppOf ``Reg64s.rsp && (rhs.find? (· == lhs)).isNone do continue
    if ← env.rooms.anyM fun r => withReducible (isDefEq lhs r.rspU) then continue
    thms ← thms.add (.fvar pf.fvarId!) #[] pf
  let ctx ← Simp.mkContext (config := { failIfUnchanged := false }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← simpGoal g ctx).1.map (·.2)

/-! ## The goals -/

/-- `true = true` for a `decide` fact about literals. -/
meta def closeDecide (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  if ← isDefEq (← inferType pf) (← instantiateMVars (← g.getType)) then
    g.assign pf
    return #[]
  return #[g]

/-- An equation of two addresses. -/
meta def closeAddr (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let some (_, a, b) := (← instantiateMVars (← g.getType)).eq? | return #[g]
  match ← addrEq a b with
  | some p => g.assign p; return #[]
  | none => return #[g]

/-- Equal up to reducible unfolding (and `let` values). -/
meta def closeRfl (g : MVarId) : MetaM Bool := g.withContext do
  let some (_, a, b) := (← instantiateMVars (← g.getType)).eq? | return false
  if ← withReducible (isDefEq a b) then
    g.assign (← mkEqRefl a)
    return true
  return false

/-- The value of a `let` variable. -/
meta partial def unlet (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  if let .fvar fv := e then
    if let some v ← fv.getValue? then return ← unlet v
  return e

meta def isW64 (e : Expr) : MetaM Bool := withReducible (isDefEq e (mkConst ``Width.W64))

/-- The lemma `name` applied to the explicit arguments `args` (the implicit ones are unified, the
rest of the binders stay as the premises of the result, which has metavariables). -/
meta partial def lemApp (name : Name) (args : Array Expr) : MetaM Expr := do
  let rec go (f ty : Expr) (i : Nat) : MetaM Expr := do
    if i == args.size then return f
    match ← whnf ty with
    | .forallE _ d b bi =>
      if bi.isExplicit then
        unless ← isDefEq d (← inferType args[i]!) do throwError "lemApp: {name}: argument {i}"
        go (mkApp f args[i]!) (b.instantiate1 args[i]!) (i + 1)
      else
        let m ← mkFreshExprMVar d
        go (mkApp f m) (b.instantiate1 m) i
    | _ => throwError "lemApp: {name}: too many arguments"
  let c ← mkConstWithFreshMVarLevels name
  go c (← inferType c) 0

mutual

/-- Applies `f` to the goal, then proves each new goal. A failure of the application leaves the
goal as it is. -/
meta partial def applyAll (env : Env) (g : MVarId) (f : Expr) : MetaM (Array MVarId) := do
  let gs ← try g.apply f catch _ => return #[g]
  let mut stuck := #[]
  for g' in gs do stuck := stuck ++ (← prove env g')
  return stuck

/-- `applyAll` with the lemma `name` and its explicit arguments `args`. -/
meta partial def applyLem (env : Env) (g : MVarId) (name : Name) (args : Array Expr) :
    MetaM (Array MVarId) := do
  let some f ← (try some <$> lemApp name args catch _ => pure none) | return #[g]
  applyAll env g f

meta partial def prove (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  if let some (α, l, _) := t.eq? then
    let l := (← instantiateMVars l).consumeMData
    if l.isAppOfArity ``readRam 4 then return ← proveRead env g
    if l.isAppOfArity ``writeRam 5 then return ← proveWrite env g
    if l.isAppOfArity ``Mem.loadInt 4 then return ← proveLoadEq env g
    if l.isAppOfArity ``CpuPolicy.permits 2 then return ← provePermit env g
    if l.isAppOfArity ``Decidable.decide 2 then return ← closeDecide g
    if ← closeRfl g then return #[]
    if (← unlet l).isAppOfArity ``Mem.storeInt 5 then return ← proveStore env g
    if α.consumeMData.isAppOf ``BitVec then return ← closeAddr g
    return #[g]
  if t.isAppOfArity ``Ne 3 then return ← proveMapped env g
  if t.isAppOfArity ``SysV.Outside 3 then return ← proveOutside env g
  return #[g]

/-- A read: the stored word of the chain, or a fact about a memory that the chain keeps. -/
meta partial def proveRead (env : Env) (g : MVarId) : MetaM (Array MVarId) := do
  let s ← saveState
  let stored := applyAll env g (mkConst ``readRam_of_stored)
  let r ← try stored catch _ => pure #[g]
  if r.isEmpty then return #[]
  s.restore
  for (pf, ty) in env.hyps do
    let some (_, l, _) := ty.eq? | continue
    unless l.isAppOfArity ``readRam 4 do continue
    let s' ← saveState
    let r ← applyLem env g ``readRam_of_hyp #[pf]
    if r.isEmpty then return #[]
    s'.restore
  s.restore
  try stored catch _ => pure #[g]

/-- A write: the permit, the mapped word, and the new memory. -/
meta partial def proveWrite (env : Env) (g : MVarId) : MetaM (Array MVarId) :=
  applyAll env g (mkConst ``writeRam_of_store)

/-- The memory `M'` of a write is the store: the same chain, with the addresses equal. -/
meta partial def proveStore (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  if ← closeRfl g then return #[]
  let some (_, l, r) := (← instantiateMVars (← g.getType)).eq? | return #[g]
  let l ← unlet l
  let r ← unlet r
  unless l.isAppOfArity ``Mem.storeInt 5 && r.isAppOfArity ``Mem.storeInt 5 do return #[g]
  applyAll env g (mkConst ``storeInt_congr)

/-- A load equation `M.loadInt a 8 = M₀.loadInt a 8`: `mem_simp`, then `Outside` for the word at
`rsp`. -/
meta partial def proveLoadEq (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let some g' ← MemSimp.memSimpGoal none g | return #[]
  g'.withContext do
    if ← closeRfl g' then return #[]
    let some (_, l, _) := (← instantiateMVars (← g'.getType)).eq? | return #[g']
    let_expr Mem.loadInt _ m _ _ := l | return #[g']
    for (pf, ty) in env.hyps do
      unless ty.isAppOfArity ``SysV.Outside 3 do continue
      unless ← withReducible (isDefEq ty.appArg! m) do continue
      let s ← saveState
      let r ← applyLem env g' ``loadInt_of_outside #[pf]
      if r.isEmpty then return #[]
      s.restore
    return #[g']

/-- A permit of the room. -/
meta partial def provePermit (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let some (_, l, _) := (← instantiateMVars (← g.getType)).eq? | return #[g]
  let policy := l.appFn!.appArg!
  let acc := l.appArg!
  let lem ← if acc.isAppOf ``Access.read then pure ``permits_read
    else if acc.isAppOf ``Access.write then pure ``permits_write
    else return #[g]
  unless acc.getAppNumArgs == 2 do return #[g]
  unless ← isW64 acc.appArg! do return #[g]
  for r in env.rooms do
    unless ← withReducible (isDefEq policy r.policy) do continue
    let some k ← offset r.rsp acc.appFn!.appArg! | continue
    let s ← saveState
    let res ← applyLem env g lem #[r.pf, mkNatLit k]
    if res.isEmpty then return #[]
    s.restore
  return #[g]

/-- A mapped word: `mem_simp` through the stores, then the room or a fact. -/
meta partial def proveMapped (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let some g' ← MemSimp.memSimpGoal none g | return #[]
  g'.withContext do
    let t := (← instantiateMVars (← g'.getType)).consumeMData
    let_expr Ne _ l _ := t | return #[g']
    if l.isAppOf ``Option.some then
      g'.assign (← mkAppM ``Option.some_ne_none #[l.appArg!])
      return #[]
    let_expr Mem.loadInt _ m a _ := l | return #[g']
    for r in env.rooms do
      unless ← withReducible (isDefEq m r.dmem) do continue
      let some k ← offset r.rsp a | continue
      let s ← saveState
      let res ← applyLem env g' ``mapped_slot #[r.pf, mkNatLit k]
      if res.isEmpty then return #[]
      s.restore
    for (pf, ty) in env.hyps do
      let_expr Ne _ l' _ := ty | continue
      let_expr Mem.loadInt _ m' _ _ := l' | continue
      unless ← withReducible (isDefEq m m') do continue
      let s ← saveState
      let res ← applyLem env g' ``mapped_of_hyp #[pf]
      if res.isEmpty then return #[]
      s.restore
    return #[g']

/-- The bytes outside the room: one `outside_store` for each store of the chain, then the start
memory or a fact. -/
meta partial def proveOutside (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let s := t.appFn!.appFn!.appArg!
  let m ← unlet t.appArg!
  if m.isAppOfArity ``Mem.storeInt 5 then
    unless (← (evalNat (m.getArg! 3)).run) == some 8 do return #[g]
    let rsp ← mkAppM ``UInt64.toBitVec #[← mkAppM ``Reg64s.rsp #[← mkAppM ``MachineData.regs
      #[← mkAppM ``MachineState.data #[s]]]]
    let some k ← offset rsp (m.getArg! 2) | return #[g]
    return ← applyLem env g ``outside_store #[mkNatLit k]
  let rfl := mkApp2 (mkConst ``SysV.Outside.rfl) s t.appFn!.appArg!
  if ← withReducible (isDefEq (← inferType rfl) t) then
    g.assign rfl
    return #[]
  for (pf, ty) in env.hyps do
    unless ty.isAppOfArity ``SysV.Outside 3 do continue
    if ← withReducible (isDefEq ty t) then
      g.assign pf
      return #[]
  return #[g]

end

/-- A fact that a side goal can need: a room, `Outside`, a read, a mapped word, an equation of
`rsp`. -/
meta def relevant (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  ty.isAppOfArity ``SysV.StackRoom 3 || ty.isAppOfArity ``SysV.Outside 3 ||
    (match ty.eq? with
      | some (_, l, _) => l.isAppOfArity ``readRam 4 || l.isAppOf ``Reg64s.rsp ||
          l.isAppOfArity ``Mem.loadInt 4
      | none => false) ||
    (ty.isAppOfArity ``Ne 3 && ty.appFn!.appArg!.isAppOfArity ``Mem.loadInt 4)

/-- The goal without the facts of the context that are not `relevant` (those that other hypotheses
depend on stay). -/
meta def tidy (g : MVarId) : MetaM MVarId := g.withContext do
  let mut drop := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail || d.isLet then continue
    if (← isProp d.type) && !relevant (← instantiateMVars d.type) then drop := drop.push d.fvarId
  g.tryClearMany drop

/-- The side goals that stay (none: the goal is closed). -/
meta def roomMemCore (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let env ← mkEnv
  let some g ← prep env g | return #[]
  prove env g

end Lift.Tactic.Room

open Lean Elab Tactic Lift.Tactic.Room in
/-- `room_mem`: closes a memory side goal of a stack room, or fails with the side goals that it
cannot close (see `Lift/Tactic/Mem.lean`). -/
syntax (name := roomMem) "room_mem" : tactic

/-- `room_mem_side`: as `room_mem`, but the side goals that stay are the new goals. -/
syntax (name := roomMemSide) "room_mem_side" : tactic

open Lean Elab Tactic Lift.Tactic.Room in
@[tactic roomMem] meta def evalRoomMem : Tactic := fun _ => withMainContext do
  let rest ← roomMemCore (← getMainGoal)
  unless rest.isEmpty do
    let shown ← rest.mapM (fun g => (tidy g : MetaM MVarId))
    throwError "room_mem: stuck at{indentD (MessageData.joinSep (shown.toList.map MessageData.ofGoal) "\n\n")}"
  replaceMainGoal []

open Lean Elab Tactic Lift.Tactic.Room in
@[tactic roomMemSide] meta def evalRoomMemSide : Tactic := fun _ => withMainContext do
  replaceMainGoal (← roomMemCore (← getMainGoal)).toList
