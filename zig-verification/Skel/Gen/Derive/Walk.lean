import Lean
import Skel.Gen.Derive.Run
import Skel.Gen.Types

/-! The walk of a derived block term and its exit diff (tasks N3 and N4 of `docs/research/symexec-pilot-20261118.md`,
section 5; decisions D41 and D43 of the plan; the walk of `scratch/symreuse/E1.lean` and `projInst` of
`scratch/symreuse/E2Block.lean`).

The input is the term of `blockTerm`: `fun d : MachineData => effects`. The effects of a block are one path: a chain of
`require_exec_access` (one for each instruction), `MachineData.load`, `MachineData.store` and `Effects.undefined`, then
`Effects.done`. A branch is the exit (an `ite` in the PC), not a path. An `ite` of effects is the error `twoPaths`; any
other node is `stuck`.

The walk gives each load value, each memory after a store and each undefined value a free variable (`Var`), and
continues with the state before a load (`s := D`) and with `{ D with dmem := m }` after a store. The expressions of the
result are in terms of the start `d`, these variables and the registers of `d`; projections of state literals are reduced
(`dsimp`, and `projInst` also inside instance arguments, which `dsimp` does not visit). The variables are free
variables of no local context that stays: the result is data. Do not infer a type of an expression of it without
declaring its variables again.

N3 gives `Walk`: the code ranges, the accesses in order, the undefined values, the exit, and (for N4) the registers, the
memory and the flags that the block changes. N4 gives `Walk.diff`: the diff for the flags that a later block reads
(`live`). A flag that no later block reads is dropped, with the undefined values that only it uses. A flag that a later
block reads is kept, and its value is a flag input of that block (decision D43). `Walk.diff` also gives the flags of the
block start that the kept parts read. -/

open Lean Meta

namespace Skel.Gen.Derive

/-! ## Names -/

/-- The status flags (`Flag` of `Skel/Gen/Types.lean`). -/
def _root_.Skel.Gen.Flag.all : List Flag := [.cf, .pf, .af, .zf, .sf, .of]

/-- The projection `StatusFlags.f` of the flag. -/
def _root_.Skel.Gen.Flag.proj : Flag → Name
  | .cf => ``StatusFlags.cf | .pf => ``StatusFlags.pf | .af => ``StatusFlags.af
  | .zf => ``StatusFlags.zf | .sf => ``StatusFlags.sf | .of => ``StatusFlags.of

/-- The 16 registers. -/
def allRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The projection `Reg64s.r` of the register. -/
def regProj : Reg64 → Name
  | .rax => ``Reg64s.rax | .rbx => ``Reg64s.rbx | .rcx => ``Reg64s.rcx | .rdx => ``Reg64s.rdx
  | .rsi => ``Reg64s.rsi | .rdi => ``Reg64s.rdi | .rsp => ``Reg64s.rsp | .rbp => ``Reg64s.rbp
  | .r8 => ``Reg64s.r8 | .r9 => ``Reg64s.r9 | .r10 => ``Reg64s.r10 | .r11 => ``Reg64s.r11
  | .r12 => ``Reg64s.r12 | .r13 => ``Reg64s.r13 | .r14 => ``Reg64s.r14 | .r15 => ``Reg64s.r15

/-! ## The result -/

/-- A variable of the walk: a free variable and its type. -/
structure Var where
  id : FVarId
  type : Expr

/-- A memory access, in program order. `addr` is a `BitVec 64`. `mem` is the memory before the access. A load gives the
variable `value` (a `BitVec` of the width). A store of `val` gives the variable `mem'` (a `DataMem`): the memory after
it. -/
inductive MemAccess where
  | load (addr : Expr) (width : Width) (mem : Expr) (value : FVarId)
  | store (addr : Expr) (width : Width) (val : Expr) (mem : Expr) (mem' : FVarId)

/-- The exit of a block, from its PC. `goto` and `branch` have literal targets. A `branch` goes to `yes` when `cond`
(a `Prop` over the start and the variables, with its `Decidable` instance `inst`) holds, else to `no`. A `call` is a `goto` whose last access is a store of
the address after the last instruction (the return address) with the width 64. A `ret` is a PC that is the value of
the last access, a load. Another PC that is not a literal is `indirect`. `trap` is a fault: the block has no exit
state. -/
inductive BlockExit where
  | goto (pc : Nat)
  | branch (cond : Expr) (inst : Expr) (yes no : Nat)
  | call (callee cont : Nat)
  | ret
  | indirect (target : Expr)
  | trap

/-- The walk of a block. `checks` are the code ranges `[lo, hi)` of the instructions, in order. `regs` are the registers
that the block changes with their values (`UInt64`), `flags` the flags that it changes with their values (`Bool`), and
`dmem` the memory after the last store, when there is a store. A `trap` has no registers and no flags. `undefs` are all
undefined values, in order: `Walk.diff` drops the ones that no kept part uses. -/
structure Walk where
  start : FVarId
  checks : Array (Nat × Nat)
  accesses : Array MemAccess
  undefs : Array Var
  exit : BlockExit
  regs : Array (Reg64 × Expr)
  dmem : Option FVarId
  flags : Array (Flag × Expr)

/-- Why a term is not a walk. -/
inductive WalkError where
  /-- The term is not `fun d => …`. -/
  | notBlock
  /-- An `ite` of effects: the block has more than one path. -/
  | twoPaths
  /-- An effect node that is not a step of a block: its head constant. -/
  | stuck (head : Name)
  /-- A width that is not `W8`, `W16`, `W32` or `W64`. -/
  | width (e : Expr)
  /-- A code range or a PC that must be a literal and is not. -/
  | notLiteral (what : String) (e : Expr)
  /-- The memory at the exit is not the memory of the last store. -/
  | memory (e : Expr)
  deriving Inhabited, Repr

/-! ## Projections -/

/-- Projections of constructor applications reduced, also inside instance arguments (which `dsimp` does not visit): a
`Decidable` instance that `simp` left keeps the term of its condition before the rewrite. -/
def projInst (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if let .const n _ := x.getAppFn then
      if let some info ← getProjectionFnInfo? n then
        if let some s := x.getAppArgs[info.numParams]? then
          if s.isApp && (← isConstructorApp s) then
            return .visit (← whnfR x)
    return .continue)

/-- Projections of structure literals, beta and eta, in the whole term. With `inst`, also in instance arguments
(`projInst`). -/
def projWith (inst : Bool) (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext (config := { proj := true, beta := true, eta := true, zeta := true })
  let r := (← dsimp e ctx).1
  if inst then projInst r else pure r

/-! ## The walk -/

private def widthOf? (e : Expr) : Option Width :=
  if e.isConstOf ``Width.W8 then some .W8
  else if e.isConstOf ``Width.W16 then some .W16
  else if e.isConstOf ``Width.W32 then some .W32
  else if e.isConstOf ``Width.W64 then some .W64
  else none

/-- The value of a numeral of `Int64` (`OfNat.ofNat`) or of `BitVec` (`OfNat.ofNat` or `BitVec.ofNat w n`). -/
private def numeral? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``BitVec.ofNat 2 then (e.getArg! 1).nat? else e.nat?

/-- The bounds of a code range `lo...hi` of literals. -/
private def rangeOf? (e : Expr) : Option (Nat × Nat) :=
  if e.isAppOfArity ``Std.Rco.mk 3 then do
    let lo ← (e.getArg! 1).nat?
    let hi ← (e.getArg! 2).nat?
    pure (lo, hi)
  else none

/-- The fields of a state, projections reduced. -/
private def fields (inst : Bool) (d : Expr) : MetaM (Array Expr) := do
  let proj := projWith inst
  #[``MachineData.regs, ``MachineData.zmms, ``MachineData.status, ``MachineData.dmem].mapM fun f =>
    do proj (← mkAppM f #[d])

/-- The state `D` with its memory replaced by `m`. -/
private def withMem (inst : Bool) (d m : Expr) : MetaM Expr := do
  let fs ← fields inst d
  mkAppM ``MachineData.mk #[fs[0]!, fs[1]!, fs[2]!, m]

/-- The width of an access. -/
def MemAccess.width : MemAccess → Width
  | .load _ w _ _ => w
  | .store _ w _ _ _ => w

/-- The exit of the PC `pc` (reduced), after the accesses and the code ranges of the block. -/
private def exitOf (pc : Expr) (accesses : Array MemAccess) (checks : Array (Nat × Nat)) :
    Except WalkError BlockExit :=
  match pc.nat? with
  | some t =>
    match accesses.back?, checks.back? with
    | some (.store _ .W64 v _ _), some (_, cont) =>
      if numeral? v == some cont then .ok (.call t cont) else .ok (.goto t)
    | _, _ => .ok (.goto t)
  | none =>
    if pc.isAppOfArity ``ite 5 then
      match (pc.getArg! 3).nat?, (pc.getArg! 4).nat? with
      | some y, some n => .ok (.branch (pc.getArg! 1) (pc.getArg! 2) y n)
      | none, _ => .error (.notLiteral "branch target" (pc.getArg! 3))
      | _, none => .error (.notLiteral "branch target" (pc.getArg! 4))
    else match accesses.back?, pc with
      | some (.load _ .W64 _ v), .app (.const ``Int64.ofBitVec _) (.fvar x) =>
        if x == v then .ok .ret else .ok (.indirect pc)
      | _, _ => .ok (.indirect pc)

/-- The variables so far, for the names. -/
private structure Acc where
  checks : Array (Nat × Nat) := #[]
  accesses : Array MemAccess := #[]
  undefs : Array Var := #[]

/-- The value of the flag `f` of the status `st`: `StatusFlags.f st`, simplified with `ctx` (the `from_result` lemmas). -/
private def flagValue (inst : Bool) (ctx : Simp.Context) (st : Expr) (f : Flag) : MetaM Expr := do
  let e ← mkAppM f.proj #[st]
  let (r, _) ← simp e ctx #[← Simp.getSimprocs]
  projWith inst r.expr

/-- The end of the path: the exit, and the registers, the memory and the flags that differ from the start `d`. -/
private def finish (inst : Bool) (ctx : Simp.Context) (d : FVarId) (acc : Acc) (st : Expr) :
    ExceptT WalkError MetaM Walk := do
  let proj := projWith inst
  let d0 := mkFVar d
  let data ← proj (← mkAppM ``MachineState.data #[st])
  let pc ← proj (← mkAppM ``MachineState.pc #[st])
  let exit ← liftExcept (exitOf pc acc.accesses acc.checks)
  let regs ← proj (← mkAppM ``MachineData.regs #[data])
  let regs0 ← mkAppM ``MachineData.regs #[d0]
  let mut changed := #[]
  for r in allRegs do
    let v ← proj (← mkAppM (regProj r) #[regs])
    if v != (← mkAppM (regProj r) #[regs0]) then changed := changed.push (r, v)
  let dmem ← proj (← mkAppM ``MachineData.dmem #[data])
  let dmem' ← match ← proj (← mkAppM ``MachineData.dmem #[d0]) with
    | m0 => if dmem == m0 then pure none else
      match dmem.fvarId? with
      | some m => pure (some m)
      | none => throwThe WalkError (.memory dmem)
  let status ← proj (← mkAppM ``MachineData.status #[data])
  let status0 ← proj (← mkAppM ``MachineData.status #[d0])
  let mut flags := #[]
  for f in Flag.all do
    let v ← flagValue inst ctx status f
    if v != (← flagValue inst ctx status0 f) then flags := flags.push (f, v)
  pure { start := d, checks := acc.checks, accesses := acc.accesses, undefs := acc.undefs, exit,
         regs := changed, dmem := dmem', flags }
where
  liftExcept {α : Type} : Except WalkError α → ExceptT WalkError MetaM α := fun
    | .ok a => pure a
    | .error e => throwThe WalkError e

/-- The walk of the effects `e`. -/
private partial def go (inst : Bool) (ctx : Simp.Context) (d : FVarId) (acc : Acc) (e : Expr) :
    ExceptT WalkError MetaM Walk := do
  let proj := projWith inst
  let e := e.headBeta
  if e.isAppOfArity ``Effects.require_exec_access 2 then
    let some r := rangeOf? (← proj (e.getArg! 0)) | throwThe WalkError (.notLiteral "code range" (e.getArg! 0))
    go inst ctx d { acc with checks := acc.checks.push r } (mkApp (e.getArg! 1) (mkConst ``Unit.unit))
  else if e.isAppOfArity ``MachineData.load 4 then
    let some w := widthOf? (e.getArg! 2) | throwThe WalkError (.width (e.getArg! 2))
    let D ← proj (e.getArg! 0)
    let addr ← proj (e.getArg! 1)
    let mem ← proj (← mkAppM ``MachineData.dmem #[D])
    let r := e.getArg! 3
    let vty ← whnfD (← inferType r).bindingDomain!
    withLocalDeclD (Name.mkSimple s!"v{acc.accesses.size}") vty fun v =>
      go inst ctx d { acc with accesses := acc.accesses.push (.load addr w mem v.fvarId!) } (mkApp2 r v D)
  else if e.isAppOfArity ``MachineData.store 5 then
    let some w := widthOf? (e.getArg! 2) | throwThe WalkError (.width (e.getArg! 2))
    let D ← proj (e.getArg! 0)
    let addr ← proj (e.getArg! 1)
    let val ← proj (e.getArg! 3)
    let mem ← proj (← mkAppM ``MachineData.dmem #[D])
    withLocalDeclD (Name.mkSimple s!"m{acc.accesses.size}") (mkConst ``DataMem) fun m => do
      let D' ← withMem inst D m
      go inst ctx d { acc with accesses := acc.accesses.push (.store addr w val mem m.fvarId!) }
        (mkApp (e.getArg! 4) D')
  else if e.isAppOfArity ``Effects.undefined 3 then
    let ty := e.getArg! 0
    withLocalDeclD (Name.mkSimple s!"u{acc.undefs.size}") ty fun u =>
      go inst ctx d { acc with undefs := acc.undefs.push ⟨u.fvarId!, ty⟩ } (mkApp (e.getArg! 2) u)
  else if e.isAppOfArity ``ite 5 then
    throwThe WalkError .twoPaths
  else if e.isAppOfArity ``Effects.done 1 then
    finish inst ctx d acc (e.getArg! 0)
  else if e.isAppOfArity ``Effects.fault 1 then
    pure { start := d, checks := acc.checks, accesses := acc.accesses, undefs := acc.undefs, exit := .trap,
           regs := #[], dmem := none, flags := #[] }
  else
    throwThe WalkError (.stuck e.getAppFn.constName)

/-- N3 and N4 (the diff of the registers, the memory and the flags before the filter of `Walk.diff`): the walk of the
block term `fun d => effects` of `blockTerm`. `ctx` simplifies the flag values (`blockContext`). The result or the
error. An exception of `MetaM` is not an error value. `inst := false` does not reduce projections in instance arguments
(the tests use it to show the cases that `projInst` serves). -/
def walkTerm (ctx : Simp.Context) (term : Expr) (inst : Bool := true) : MetaM (Except WalkError Walk) :=
  lambdaTelescope term fun xs body =>
    if h : xs.size = 1 then
      (go inst ctx xs[0].fvarId! {} body).run
    else pure (.error .notBlock)

/-! ## The exit diff -/

/-- The exit diff for the flags `live` (the flags that a later block reads). -/
structure ExitDiff where
  /-- The registers that the block changes, with their values. -/
  regs : Array (Reg64 × Expr)
  /-- The memory after the last store; `none` when the block does not store. -/
  dmem : Option FVarId
  /-- The flags that the block changes and that a later block reads, with their values: flag inputs of that block. -/
  flags : Array (Flag × Expr)
  /-- The flags of the block start that the kept parts read (a flag input of this block). -/
  inputs : Array Flag
  /-- The undefined values that a kept part uses. -/
  undefs : Array Var

/-- The expression with the `Decidable` instances of `ite`, `dite` and `decide` replaced by `True`: `simp` leaves there the
instance of the condition before its rewrite, which is not a read of the block. -/
private partial def stripInst (e : Expr) : Expr :=
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    mkAppN e.getAppFn #[stripInst (e.getArg! 0), stripInst (e.getArg! 1), mkConst ``True,
      stripInst (e.getArg! 3), stripInst (e.getArg! 4)]
  else if e.isAppOfArity ``Decidable.decide 2 then
    mkAppN e.getAppFn #[stripInst (e.getArg! 0), mkConst ``True]
  else match e with
    | .app f a => .app (stripInst f) (stripInst a)
    | .lam n t b bi => .lam n (stripInst t) (stripInst b) bi
    | .forallE n t b bi => .forallE n (stripInst t) (stripInst b) bi
    | .letE n t v b nd => .letE n (stripInst t) (stripInst v) (stripInst b) nd
    | .mdata m b => .mdata m (stripInst b)
    | .proj s i b => .proj s i (stripInst b)
    | x => x

/-- The flags of the status of `d` that `e` reads, outside the instances. -/
def flagReads (d : FVarId) (e : Expr) : List Flag :=
  let e := stripInst e
  let st := mkApp (mkConst ``MachineData.status) (mkFVar d)
  Flag.all.filter fun f => (e.find? fun x => x.isAppOfArity f.proj 1 && x.getArg! 0 == st).isSome

/-- The expressions of an exit that a block reads: the condition of a branch, the target of an indirect exit. -/
def BlockExit.reads : BlockExit → List Expr
  | .branch c _ _ _ => [c]
  | .indirect t => [t]
  | _ => []

/-- All expressions of an exit: also the instance of a branch. -/
def BlockExit.exprs : BlockExit → List Expr
  | .branch c i _ _ => [c, i]
  | e => e.reads

/-- The expressions of an access, except its memories. -/
def MemAccess.exprs : MemAccess → List Expr
  | .load a _ _ _ => [a]
  | .store a _ v _ _ => [a, v]

/-- All expressions of the walk: the accesses, the exit (with the instance of a branch), the registers, the flags and
the memories before the accesses. -/
def Walk.exprs (w : Walk) : List Expr :=
  (w.accesses.toList.flatMap MemAccess.exprs) ++ w.exit.exprs ++ (w.regs.toList.map (·.2)) ++ (w.flags.toList.map (·.2)) ++
    (w.accesses.toList.filterMap fun | .load _ _ m _ => some m | .store _ _ _ m _ => some m)

/-- N4: the exit diff of the block for the flags `live`. The flags that the block changes and that are not in `live` are
dropped, with the undefined values that only they use. -/
def Walk.diff (w : Walk) (live : List Flag) : ExitDiff :=
  let flags := w.flags.filter fun (f, _) => live.contains f
  let kept : List Expr :=
    (w.accesses.toList.flatMap MemAccess.exprs) ++ w.exit.reads ++ (w.regs.toList.map (·.2)) ++ (flags.toList.map (·.2))
  { regs := w.regs, dmem := w.dmem, flags,
    inputs := (Flag.all.filter fun f => kept.any fun e => (flagReads w.start e).contains f).toArray,
    undefs := w.undefs.filter fun u => kept.any (·.containsFVar u.id) }

end Skel.Gen.Derive
