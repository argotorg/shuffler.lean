import Skel.Gen.Derive.Walk
import Skel.Gen.Sym
import Skel.Test.DeriveRun

/-! The tests of `Skel/Gen/Derive/Walk.lean` (tasks N3 and N4 of `docs/research/symexec-pilot-20261118.md`, section 5). The
module is checked by `lake build Skel.Test.DeriveWalk`: each `#eval` throws when a check fails. No `set_option` changes a
limit.

Pilot: the 49 blocks of the 8 functions of `Lift.Level3.Code.code`, 25 with a table block. Level 2: the 79 blocks of the 17
functions of `Lift.Level2.Code.code`, 48 with a table block. The table blocks are the 73 blocks of E2 (section 2).

The comparison with the table: the number of accesses, their kinds (load or store) and widths, the changed registers
(a subset of the registers of the table block), the exit (the targets, as a set for a branch). The values, the addresses
and the conditions are not compared: N7 and N10 compare them. -/

open Lean Meta Elab Term Skel.Gen Skel.Gen.Derive DeriveSiteTests DeriveRunTests

namespace DeriveWalkTests

/-- The walks of the rows of `runAll` (the block terms of N2), or the first error. -/
def walksOf (ctx : Simp.Context) (rows : List Row) (inst : Bool := true) : TermElabM (List (Spec × Walk)) :=
  rows.mapM fun (s, r, _) => do
    match r with
    | .error e => throwError "{s.fn} {s.name}: no term: {repr e}"
    | .ok t =>
      match ← walkTerm ctx t inst with
      | .ok w => pure (s, w)
      | .error e => throwError "{s.fn} {s.name}: walk error: {repr e}"

/-- The walks of the blocks of `specs`. -/
def walkAll (step pfx : Name) (specs : List Spec) : TermElabM (List (Spec × Walk)) := do
  let (eqs, rows) ← runAll step pfx specs
  walksOf (← blockContext eqs) rows

def isLoadAcc : MemAccess → Bool
  | .load .. => true
  | .store .. => false

def tableIsLoad : Skel.Gen.Access → Bool
  | .load .. => true
  | .store .. => false

def tableWidth : Skel.Gen.Access → Width
  | .load _ _ w => w
  | .store _ _ w _ => w

/-- The exit of the walk against the exit of the table block, for the function at `base` (a branch: the targets as a
set, because the PC of the term may have the arms in the other order). -/
def exitMatches (base : Nat) (e : BlockExit) (t : Skel.Gen.Term) : Bool :=
  match e, t with
  | .goto p, .exit (.goto x) => p == base + x
  | .ret, .exit .ret => true
  | .trap, .exit .trap => true
  | .call _ c, .exit (.call _ cont) => c == base + cont
  | .branch _ _ y n, .branch _ (.goto a) (.goto b) =>
    (y == base + a && n == base + b) || (y == base + b && n == base + a)
  | _, _ => false

/-- The code ranges chain: the first starts at `pc`, each one ends where the next starts. -/
def chained (pc : Nat) (cs : Array (Nat × Nat)) : Bool :=
  (cs[0]?.map (·.1) == some pc || cs.isEmpty) && (cs.toList.zip (cs.toList.drop 1)).all fun (a, b) => a.2 == b.1

/-- A projection of a constructor application stays in the term (a copy of the rule of `projInst` for the tests). -/
partial def hasCtorProj (e : Expr) : MetaM Bool := do
  if let .const n _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? n then
      if let some s := e.getAppArgs[info.numParams]? then
        if s.isApp && (← isConstructorApp s) then return true
  match e with
  | .app f a => return (← hasCtorProj f) || (← hasCtorProj a)
  | .lam _ t b _ | .forallE _ t b _ => return (← hasCtorProj t) || (← hasCtorProj b)
  | .letE _ t v b _ => return (← hasCtorProj t) || (← hasCtorProj v) || (← hasCtorProj b)
  | .mdata _ b | .proj _ _ b => hasCtorProj b
  | _ => return false

/-- The `Decidable` instance arguments of `ite`, `dite` and `decide` in `e`. -/
partial def instances (e : Expr) : List Expr :=
  let here :=
    if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then [e.getArg! 2]
    else if e.isAppOfArity ``Decidable.decide 2 then [e.getArg! 1] else []
  here ++ match e with
    | .app f a => instances f ++ instances a
    | .lam _ t b _ | .forallE _ t b _ => instances t ++ instances b
    | .letE _ t v b _ => instances t ++ instances v ++ instances b
    | .mdata _ b | .proj _ _ b => instances b
    | _ => []

/-- The expression with each instance argument of `ite`, `dite` and `decide` replaced by `True`. -/
partial def stripInstances (e : Expr) : Expr :=
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    mkAppN e.getAppFn #[stripInstances (e.getArg! 0), stripInstances (e.getArg! 1), mkConst ``True,
      stripInstances (e.getArg! 3), stripInstances (e.getArg! 4)]
  else if e.isAppOfArity ``Decidable.decide 2 then
    mkAppN e.getAppFn #[stripInstances (e.getArg! 0), mkConst ``True]
  else match e with
    | .app f a => .app (stripInstances f) (stripInstances a)
    | .lam n t b bi => .lam n (stripInstances t) (stripInstances b) bi
    | .forallE n t b bi => .forallE n (stripInstances t) (stripInstances b) bi
    | .letE n t v b nd => .letE n (stripInstances t) (stripInstances v) (stripInstances b) nd
    | .mdata m b => .mdata m (stripInstances b)
    | .proj s i b => .proj s i (stripInstances b)
    | x => x

def name (s : Spec) : String := s!"{s.fn} {s.name}"

end DeriveWalkTests

open DeriveWalkTests

/-! ## The pilot: the table, the shape, the instance cases -/

#eval show TermElabM Unit from do
  let ws ← walkAll pilotStep `Skel.Test.DeriveWalk.l3 pilotSpecs
  check (ws.length == 49) s!"49 pilot walks, got {ws.length}"
  let mut covered : Nat := 0
  let mut accesses : Nat := 0
  for (s, w) in ws do
    -- one code range for each instruction, in a chain from the PC of the block
    check (w.checks.size == s.n) s!"{name s}: {w.checks.size} code ranges for {s.n} instructions"
    check (chained s.pc w.checks) s!"{name s}: the code ranges do not chain"
    -- the memory after the last store is the variable of that store
    let lastStore := (w.accesses.toList.reverse.filterMap fun | .store _ _ _ _ m => some m | _ => none).head?
    check (w.dmem == lastStore) s!"{name s}: dmem is the memory of the last store"
    -- no flag of the block start is read outside an instance
    check ((w.diff []).inputs.isEmpty) s!"{name s}: a flag input"
    -- no projection of a literal stays, also inside instances
    for e in w.exprs do check (!(← hasCtorProj e)) s!"{name s}: a projection of a constructor application stays"
    if let some b := s.table then
      covered := covered + 1
      accesses := accesses + w.accesses.size
      check (w.accesses.size == b.accesses.length) s!"{name s}: {w.accesses.size} accesses, table {b.accesses.length}"
      for (a, t) in w.accesses.toList.zip b.accesses do
        check (isLoadAcc a == tableIsLoad t) s!"{name s}: the kind of an access"
        check (a.width == tableWidth t) s!"{name s}: the width of an access"
      for (r, _) in w.regs do
        check (b.regs.any (·.1 == r)) s!"{name s}: a changed register that the table block does not have"
      check (exitMatches (s.pc - b.offset) w.exit b.term) s!"{name s}: the exit"
  logInfo m!"pilot: {covered} table blocks compared, {accesses} accesses"
  check (covered == 25) s!"25 pilot table blocks, got {covered}"

/-! ## The instance cases of `projInst`

The walk continues a load or a store with a state literal, so that the instance argument of an `ite` (the `Decidable`
instance of its condition before the rewrite) holds projections of that literal. `dsimp` does not visit instance
arguments. With `inst := false` (no `projInst`), a projection of a constructor application (`MachineData.regs` of a
`MachineData.mk`) stays in 3 pilot blocks, in an instance and nowhere else: `shallowestCopyPosition` o12 and `mapInPlace`
entry (the two blocks of E2, section 2) and `closestCopy` o114; in a branch, the instance is that of the PC. With the
default, none stays in any of the 128 blocks (the checks above and below). -/

/-- The names of the blocks with a projection of a constructor application in an instance argument, and (marked) outside
every instance. The instance of a branch is an instance argument. -/
def stays (ws : List (Spec × Walk)) : MetaM (List String) :=
  ws.filterMapM fun (s, w) => do
    let branchInst := match w.exit with | .branch _ i _ _ => [i] | _ => []
    let inInst ← (w.exprs.filter (!branchInst.contains ·)).anyM fun e => (instances e).anyM hasCtorProj
    let inInst ← if inInst then pure true else branchInst.anyM hasCtorProj
    let outInst ← (w.exprs.filter (!branchInst.contains ·)).anyM fun e => hasCtorProj (stripInstances e)
    if inInst || outInst then pure (some s!"{name s}{if outInst then " (outside an instance)" else ""}") else pure none

#eval show TermElabM Unit from do
  let (eqs, rows) ← runAll pilotStep `Skel.Test.DeriveWalk.inst pilotSpecs
  let ctx ← blockContext eqs
  let without ← stays (← walksOf ctx rows (inst := false))
  logInfo m!"pilot, without projInst: {without}"
  check (without == [".Lshuffler.Emission.shallowestCopyPosition o12", ".Lshuffler.MappingBuilder.closestCopy o114",
      ".Lshuffler.MappingBuilder.mapInPlace entry"]) s!"the instance cases, got {without}"
  check ((← stays (← walksOf ctx rows)).isEmpty) "with projInst no projection stays"

/-! ## The negative cases

A term with two paths is the error `twoPaths`. A term that is not a block, a node that is not a step, a width and a code
range that are not literals are errors that name the cause. -/

private def elabE (stx : TermElabM Syntax) : TermElabM Expr := do
  let e ← Term.elabTerm (← stx) none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

private def walkOf (e : Expr) : TermElabM (Except WalkError Walk) := do
  walkTerm (← blockContext []) e

private def isErr (r : Except WalkError Walk) (p : WalkError → Bool) : Bool :=
  match r with | .error e => p e | .ok _ => false

#eval show TermElabM Unit from do
  -- two paths: an `ite` of effects
  let e ← elabE `(fun d : MachineData =>
    if d.regs.rax = 0 then Effects.done ⟨d, 1⟩ else Effects.done ⟨d, 2⟩)
  check (isErr (← walkOf e) fun | .twoPaths => true | _ => false) "two paths are the error twoPaths"
  -- two paths after a load
  let e ← elabE `(fun d : MachineData =>
    d.load 0#64 Width.W64 fun _ s => if s.regs.rax = 0 then Effects.done ⟨s, 1⟩ else Effects.done ⟨s, 2⟩)
  check (isErr (← walkOf e) fun | .twoPaths => true | _ => false) "two paths after a load are the error twoPaths"
  -- not a block: two binders, and no binder
  let e ← elabE `(fun (a _b : MachineData) => Effects.done ⟨a, 1⟩)
  check (isErr (← walkOf e) fun | .notBlock => true | _ => false) "two binders are the error notBlock"
  check (isErr (← walkOf (mkConst ``True)) fun | .notBlock => true | _ => false) "no binder is the error notBlock"
  -- a node that is not a step
  let e ← elabE `(fun _d : MachineData => Effects.unimplemented "x")
  check (isErr (← walkOf e) fun | .stuck n => n == ``Effects.unimplemented | _ => false) "unimplemented is stuck"
  -- a width that is not a literal
  let e ← elabE `(fun d : MachineData =>
    d.load 0#64 (if d.regs.rax = 0 then Width.W8 else Width.W16) fun _ s => Effects.done ⟨s, 1⟩)
  check (isErr (← walkOf e) fun | .width _ => true | _ => false) "a width that is not a literal"
  -- a code range that is not a literal
  let e ← elabE `(fun d : MachineData =>
    Effects.require_exec_access ⟨1, Int64.ofBitVec d.regs.rax.toBitVec⟩ fun _ => Effects.done ⟨d, 1⟩)
  check (isErr (← walkOf e) fun | .notLiteral "code range" _ => true | _ => false) "a code range that is not a literal"
  -- a branch target that is not a literal
  let e ← elabE `(fun d : MachineData =>
    Effects.done ⟨d, if d.regs.rax = 0 then 1 else Int64.ofBitVec d.regs.rbx.toBitVec⟩)
  check (isErr (← walkOf e) fun | .notLiteral "branch target" _ => true | _ => false) "a branch target that is not a literal"

/-! ## The exits, on small terms -/

#eval show TermElabM Unit from do
  let ok (e : Expr) : TermElabM Walk := do
    match ← walkOf e with
    | .ok w => pure w
    | .error err => throwError "walk error: {repr err}"
  -- goto, with a changed register and no access
  let w ← ok (← elabE `(fun d : MachineData =>
    Effects.require_exec_access ⟨10, 14⟩ fun _ => Effects.done ⟨{ d with regs := { d.regs with rax := 3 } }, 14⟩))
  check (match w.exit with | .goto 14 => true | _ => false) "goto 14"
  check (w.regs.map (·.1) == #[Reg64.rax]) "rax changed"
  check (w.checks == #[(10, 14)]) "one code range"
  check (w.dmem.isNone && w.accesses.isEmpty && w.flags.isEmpty) "no memory, no access, no flag"
  -- trap
  let w ← ok (← elabE `(fun _d : MachineData => Effects.fault Fault.invalidOpcode))
  check (match w.exit with | .trap => true | _ => false) "trap"
  check (w.regs.isEmpty && w.flags.isEmpty && w.dmem.isNone) "a trap has no state"
  -- indirect: a PC from a register
  let w ← ok (← elabE `(fun d : MachineData => Effects.done ⟨d, Int64.ofBitVec d.regs.rax.toBitVec⟩))
  check (match w.exit with | .indirect _ => true | _ => false) "indirect"
  -- ret: a PC that is the value of the last load
  let w ← ok (← elabE `(fun d : MachineData =>
    d.load d.regs.rsp.toBitVec Width.W64 fun ra s => Effects.done ⟨s, Int64.ofBitVec ra⟩))
  check (match w.exit with | .ret => true | _ => false) "ret"
  check (w.accesses.size == 1 && w.accesses[0]?.map isLoadAcc == some true && w.accesses[0]?.map MemAccess.width == some .W64) "one load of 64 bits"
  -- call: a store of the address after the last instruction, then a literal PC
  let w ← ok (← elabE `(fun d : MachineData =>
    Effects.require_exec_access ⟨10, 15⟩ fun _ =>
      d.store (w := Width.W64) (d.regs.rsp.toBitVec - 8#64) (15#64 : BitVec 64) fun s => Effects.done ⟨s, 100⟩))
  check (match w.exit with | .call 100 15 => true | _ => false) "call 100 15"
  check (w.dmem.isSome) "a call changes the memory"
  -- a store of another value is a goto, not a call
  let w ← ok (← elabE `(fun d : MachineData =>
    Effects.require_exec_access ⟨10, 15⟩ fun _ =>
      d.store (w := Width.W64) (d.regs.rsp.toBitVec - 8#64) (16#64 : BitVec 64) fun s => Effects.done ⟨s, 100⟩))
  check (match w.exit with | .goto 100 => true | _ => false) "a store of another value is a goto"
  -- branch
  let w ← ok (← elabE `(fun d : MachineData =>
    Effects.done ⟨d, if d.regs.rax = 0 then 7 else 9⟩))
  check (match w.exit with | .branch _ _ 7 9 => true | _ => false) "branch 7 9"
  -- an undefined value: dropped when no kept part uses it, kept when a register uses it
  let w ← ok (← elabE `(fun d : MachineData =>
    Effects.undefined fun (b : Bool) =>
      Effects.done ⟨{ d with regs := { d.regs with rax := if b then 1 else 2 } }, 1⟩))
  check (w.undefs.size == 1 && (w.diff []).undefs.size == 1) "an undefined value that a register uses is kept"
  let w ← ok (← elabE `(fun d : MachineData =>
    Effects.undefined fun (b : Bool) =>
      Effects.done ⟨{ d with status := { d.status with af := b } }, 1⟩))
  check (w.undefs.size == 1 && w.flags.map (·.1) == #[Flag.af]) "an undefined flag is a changed flag"
  check ((w.diff []).undefs.isEmpty && (w.diff []).flags.isEmpty) "an undefined flag that no block reads is dropped"
  check ((w.diff [.af]).undefs.size == 1 && (w.diff [.af]).flags.size == 1) "an undefined flag that a block reads is kept"
  check ((w.diff [.cf]).undefs.isEmpty) "an undefined flag is dropped when another flag is live"

/-! ## Level 2: the table, the flags -/

#eval show TermElabM Unit from do
  let ws ← walkAll level2Step `Skel.Test.DeriveWalk.l2 level2Specs
  check (ws.length == 79) s!"79 level 2 walks, got {ws.length}"
  let mut covered : Nat := 0
  let mut withUndef : Nat := 0
  let mut dropped : Nat := 0
  let mut keptByFlag : Nat := 0
  let mut flagInputs : List String := []
  for (s, w) in ws do
    check (w.checks.size == s.n) s!"{name s}: {w.checks.size} code ranges for {s.n} instructions"
    check (chained s.pc w.checks) s!"{name s}: the code ranges do not chain"
    let lastStore := (w.accesses.toList.reverse.filterMap fun | .store _ _ _ _ m => some m | _ => none).head?
    check (w.dmem == lastStore) s!"{name s}: dmem is the memory of the last store"
    for e in w.exprs do check (!(← hasCtorProj e)) s!"{name s}: a projection of a constructor application stays"
    let d0 := w.diff []
    let d1 := w.diff Flag.all
    check (d0.undefs.size ≤ d1.undefs.size && d1.undefs.size ≤ w.undefs.size) s!"{name s}: the undefined values of the diffs"
    check (d0.flags.isEmpty) s!"{name s}: a flag is kept when none is live"
    if !w.undefs.isEmpty then
      withUndef := withUndef + 1
      if d0.undefs.isEmpty then dropped := dropped + 1
      if d1.undefs.size > d0.undefs.size then keptByFlag := keptByFlag + 1
    unless d0.inputs.isEmpty do flagInputs := flagInputs ++ [s!"{name s}: {repr d0.inputs}"]
    if let some b := s.table then
      covered := covered + 1
      check (w.accesses.size == b.accesses.length) s!"{name s}: {w.accesses.size} accesses, table {b.accesses.length}"
      for (a, t) in w.accesses.toList.zip b.accesses do
        check (isLoadAcc a == tableIsLoad t) s!"{name s}: the kind of an access"
        check (a.width == tableWidth t) s!"{name s}: the width of an access"
      for (r, _) in w.regs do
        check (b.regs.any (·.1 == r)) s!"{name s}: a changed register that the table block does not have"
      check (exitMatches (s.pc - b.offset) w.exit b.term) s!"{name s}: the exit"
  logInfo m!"level 2: {covered} table blocks compared; {withUndef} blocks with an undefined value, all dropped in {dropped}, one kept by a live flag in {keptByFlag}"
  check (covered == 48) s!"48 level 2 table blocks, got {covered}"
  -- E1, section 4: 23 blocks have an `undefined` node; the drop with no live flag removes all of them; 18 blocks have a
  -- flag that a later block could read and that has an undefined value
  check (withUndef == 23 && dropped == 23) s!"undefined values: {withUndef} blocks, dropped in {dropped}"
  check (keptByFlag == 18) s!"undefined values kept by a live flag in {keptByFlag} blocks"
  -- the only block that reads a flag of its start is `l2Flags` LBB0_1 (`cmovb` reads the carry of the `cmpq` of `entry`)
  check (flagInputs == ["l2Flags LBB0_1: #[Skel.Gen.Flag.cf]"]) s!"flag inputs: {flagInputs}"
  -- `entry` writes `cf`; it is dropped when no later block reads it, and kept when LBB0_1 reads it (decision D43)
  let some (_, entry) := ws.find? fun (s, _) => s.fn == "l2Flags" && s.name == "entry" | throwError "no l2Flags entry"
  check (entry.flags.any (·.1 == .cf)) "entry changes cf"
  check ((entry.diff []).flags.isEmpty) "cf is dropped when no later block reads it"
  let kept := (entry.diff [.cf]).flags
  check (kept.map (·.1) == #[Flag.cf]) "cf is kept when LBB0_1 reads it"
  check (kept.all fun (_, v) => v.containsFVar entry.start) "the kept cf is a value of the registers of entry"
  check (!(kept.any fun (_, v) => (flagReads entry.start v).contains .cf)) "the kept cf does not read the carry of the start"
  let some (_, lbb1) := ws.find? fun (s, _) => s.fn == "l2Flags" && s.name == "LBB0_1" | throwError "no l2Flags LBB0_1"
  check ((lbb1.diff []).inputs == #[Flag.cf]) "LBB0_1 reads cf at its start"
  check (lbb1.undefs.size == 7 && (lbb1.diff []).undefs.isEmpty) "the 7 undefined values of LBB0_1 are dropped"
