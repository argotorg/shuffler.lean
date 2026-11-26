module

public import Lift.Tactic.FrameMemLemmas
public meta import Lift.Tactic.Mem
public meta import Lean.Elab.Tactic
public meta import Kraken.SeparationTactics

@[expose] public section

/-! `frame_mem`: the memory side goals of a block lemma, when the memory is a separation formula.

The facts in the context: `room : SysV.StackRoom policy s n` (the permits; as for `room_mem`) and
`h : m =⋆ P`, where `P` is a `⋆`-sequence of slots `SysV.Word a v` or `Mem.Bytes a bs` and the rest
`Eq rest`. The goals:

1. `readRam policy m a .W64 = .ok v` (a slot `Word a₀ v` with `a = a₀`; or the return word at `rsp`,
   from `Outside` and a read of the start memory);
2. `writeRam policy m a .W64 v = .ok M'` (a slot of 8 bytes; `M'` may be a metavariable);
3. `m =⋆ P'` (the entailment at a block border), also under `∃` and `∧`: a witness is found by
   matching, a length is `Int.toBytes_length` or a fact, `Outside s n rest` is a fact;
4. `SysV.Outside s n m`, from the room, through `Outside.of_sep`.
5. After a callee, with `out' : SysV.Outside s' n' m` in the context (the `post` of the callee that
   was called in `s'`, whose `rsp` is `rsp - j` of a room): a read in `m` of a word that the room of
   the callee does not meet is the read in the memory `s'.data.dmem` (`readRam_far`), and `Outside s
   n m` is `Outside s n s'.data.dmem` when `j + n' ≤ n` (`outside_compose`). `j` and the offset of
   the word are the linear forms of the addresses.

6. `frame_call` (a second tactic, same file) closes in addition the goals of the return of a call: the
   room of the callee, the words that stay mapped, and the mapped word of a write (see "The call
   return").

`m` is a variable with a fact, a `let` variable, a variable with an equation `m = m'` (one step), or
a chain of stores `Mem.storeInt m₀ a 8 x.toInt` on such a memory: the formula of the chain is made
from the formula of `m₀`, one store at a time, so that the holes of a block lemma need no fact about
the memories that earlier holes made. A goal about a memory with no formula goes to `room_mem`.

The front end is that of `Lift/Tactic/Mem.lean`: `prep` (the equations of `rsp`), `offset` and
`addrEq` (the linear form of an address), the permits of the room (`provePermit`), `closeRfl`. Each
address of the goal is compared with the address of a slot by its linear form; an address of `P'` is
then rewritten to the spelling of the fact before the cancellation of Kraken (`solveSepEq`). Each
step is bounded by the size of the formula; there is no `repeat`. When it fails, `frame_mem` gives an
error with the goals that stay. -/

namespace Lift.Tactic.Frame

open Lean Meta Elab Tactic
open Lift.P2.Total Lift.Sem
open Lift.Tactic.Room (Env mkEnv offset addrEq prep unlet lemApp isW64)
open Kraken.Tactic (extHashMapOps reifyClauses solveSepEq)

/-! ## Slots and formulas -/

/-- A slot of a formula: its atom, its address, a proof that it has 8 bytes, and its word. -/
meta structure Slot where
  atom : Expr
  addr : Expr
  len? : Option Expr
  val? : Option Expr

meta def isSepPred (p : Expr) : Bool :=
  p.isAppOf ``Std.ExtHashMap.sep || p.isAppOfArity ``SysV.Word 2 || p.isAppOfArity ``Mem.Bytes 3

/-- `i` when `bs` is `Int.toBytes 8 i`. -/
meta def toBytes8? (bs : Expr) : MetaM (Option Expr) := do
  unless bs.isAppOfArity ``Int.toBytes 2 do return none
  return if (← (evalNat bs.appFn!.appArg!).run) == some 8 then some bs.appArg! else none

meta def slot? (env : Env) (atom : Expr) : MetaM (Option Slot) := do
  let atom := atom.consumeMData
  if atom.isAppOfArity ``SysV.Word 2 then
    let v := atom.appArg!
    let len ← mkAppM ``Int.toBytes_length #[mkNatLit 8, ← mkAppM ``BitVec.toInt #[v]]
    return some { atom, addr := atom.appFn!.appArg!, len? := some len, val? := some v }
  if atom.isAppOfArity ``Mem.Bytes 3 then
    let bs := atom.appArg!
    let addr := atom.appFn!.appArg!
    if let some i ← toBytes8? bs then
      if i.isAppOfArity ``BitVec.toInt 2 then
        let len ← mkAppM ``Int.toBytes_length #[mkNatLit 8, i]
        return some { atom, addr, len? := some len, val? := some i.appArg! }
    let len? ← if bs.hasExprMVar then pure none else env.hyps.findSomeM? fun (pf, ty) => do
      let some (_, l, r) := ty.eq? | return none
      unless l.isAppOfArity ``List.length 2 && (← (evalNat r).run) == some 8 do return none
      return if ← withReducible (isDefEq l.appArg! bs) then some pf else none
    return some { atom, addr, len?, val? := none }
  return none

/-- The atom of the slot of the formula whose address is `a`, and a proof of `a = slot.addr`. -/
meta def findSlot (env : Env) (atoms : List Expr) (a : Expr) : MetaM (Option (Slot × Expr)) := do
  for atom in atoms do
    let some sl ← slot? env atom | continue
    if let some p ← addrEq a sl.addr then return some (sl, p)
  return none

/-- The `⋆`-sequence of the atoms. -/
meta def mkChain : List Expr → MetaM (Option Expr)
  | [] => pure none
  | [a] => pure (some a)
  | a :: as => do
    let some r ← mkChain as | return none
    return some (← mkAppM ``Std.ExtHashMap.sep #[a, r])

/-- `Q m` from `h : P m`, when `P` and `Q` have the same atoms. -/
meta def reorder (P h m Q : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  let some eq ← solveSepEq extHashMapOps P Q | do s.restore; return none
  return some (← mkEqMP (← mkCongrFun eq m) h)

/-- `slot.atom ⋆ F`, with `F` the other atoms, from a fact `h : P m`. -/
meta def slotFirst (P h m : Expr) (atoms : List Expr) (sl : Slot) :
    MetaM (Option Expr) := do
  let some F ← mkChain (atoms.filter (· != sl.atom)) | return none
  reorder P h m (← mkAppM ``Std.ExtHashMap.sep #[sl.atom, F])

mutual

/-- The formula of `m` and a proof of it: a fact of the context about `m`, the store on a memory with
a formula, or (`fuel > 0`) a fact `m = m'` or `m' = m` and the formula of `m'`. -/
meta partial def sepOf (env : Env) (fuel : Nat) (m0 : Expr) : MetaM (Option (Expr × Expr)) := do
  let m0 ← instantiateMVars m0
  let m ← whnfR (← unlet m0)
  if m.hasExprMVar then return none
  for (pf, ty) in env.hyps do
    unless ty.isApp && isSepPred ty.appFn! do continue
    if (← withReducible (isDefEq ty.appArg! m)) || (← withReducible (isDefEq ty.appArg! m0)) then
      return some (ty.appFn!, pf)
  if m.isAppOfArity ``Mem.storeInt 5 then
    if let some r ← storeStep env fuel m then return some r
  if fuel > 0 && !m.isAppOfArity ``Mem.storeInt 5 then
    for (pf, ty) in env.hyps do
      let some (_, l, r) := ty.eq? | continue
      if (← withReducible (isDefEq l m)) then
        if let some (P, h) ← sepOf env (fuel - 1) r then
          return some (P, ← mkEqMP (← mkCongrArg P (← mkEqSymm pf)) h)
      if (← withReducible (isDefEq r m)) then
        if let some (P, h) ← sepOf env (fuel - 1) l then
          return some (P, ← mkEqMP (← mkCongrArg P pf) h)
  return none

/-- The formula of `Mem.storeInt m₀ a 8 x.toInt` from that of `m₀`: the slot at `a` holds `x`. -/
meta partial def storeStep (env : Env) (fuel : Nat) (m : Expr) : MetaM (Option (Expr × Expr)) := do
  let_expr Mem.storeInt _ m₀ a n v := m | return none
  unless (← (evalNat n).run) == some 8 && v.isAppOfArity ``BitVec.toInt 2 do return none
  let some (P₀, h₀) ← sepOf env fuel m₀ | return none
  let atoms ← reifyClauses extHashMapOps (← instantiateMVars P₀)
  let some (sl, ha) ← findSlot env atoms a | return none
  let some len := sl.len? | return none
  let some hm ← slotFirst P₀ h₀ m₀ atoms sl | return none
  let pf ← lemApp ``storeInt_slot #[hm, ha, len, v.appArg!]
  return some ((← instantiateMVars (← inferType pf)).appFn!, pf)

end

/-! ## After a callee

A fact `out' : Outside s' n' m` of the context is the `post` of a callee that was called in the
state `s'` (its `rsp` is `rsp - j` of a room, and its room is the `n'` bytes below). The lemmas are
`readRam_far` and `outside_compose` of `FrameMemLemmas.lean`. -/

/-- `UInt64.toBitVec` of the `rsp` of the state `s`. -/
meta def rspOf (s : Expr) : MetaM Expr := do
  let data ← mkAppM ``MachineState.data #[s]
  mkAppM ``UInt64.toBitVec #[← mkAppM ``Reg64s.rsp #[← mkAppM ``MachineData.regs #[data]]]

/-- The facts `Outside s' n' m` of the context for the memory `m`: the fact, `s'` and `n'`. -/
meta def calleesOf (env : Env) (m : Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  let mut out := #[]
  for (pf, ty) in env.hyps do
    unless ty.isAppOfArity ``SysV.Outside 3 do continue
    if ← withReducible (isDefEq (ty.getArg! 2) m) then out := out.push (pf, ty.getArg! 0, ty.getArg! 1)
  return out

/-- `a` after the equations of `rsp` of the context (the simp set of `prep`). -/
meta def normBV (env : Env) (a : Expr) : MetaM Expr := do
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
  return (← Meta.simp a ctx).1.expr

/-- A proof of the address equation `a = b`, with `a` and `b` prepared as for a goal. -/
meta def proveAddr (env : Env) (a b : Expr) : MetaM (Option Expr) := do
  let g ← mkFreshExprMVar (← mkEq a b)
  match ← Lift.Tactic.Room.prep env g.mvarId! with
  | none => return some (← instantiateMVars g)
  | some g' =>
    if (← Lift.Tactic.Room.closeAddr g').isEmpty then return some (← instantiateMVars g) else return none

/-- `r - BitVec.ofNat 64 k`. -/
meta def subOf (r : Expr) (k : Nat) : MetaM Expr := do
  mkAppM ``HSub.hSub #[r, ← mkAppM ``BitVec.ofNat #[mkNatLit 64, mkNatLit k]]

/-- The facts `Mapped sp lo hi m'` of the context with `m'` the memory `m`: the fact and its type. -/
meta def mappedOf (env : Env) (m : Expr) : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for (pf, ty) in env.hyps do
    unless ty.isAppOfArity ``SysV.Mapped 4 do continue
    if ← withReducible (isDefEq (ty.getArg! 3) m) then out := out.push (pf, ty)
  return out

/-- The addresses `a` and `b` are the same (as terms, or by their linear forms). -/
meta def sameAddr (env : Env) (a b : Expr) : MetaM Bool := do
  if ← withReducible (isDefEq a b) then return true
  return (← proveAddr env a b).isSome

/-! ## The goals -/

mutual

/-- `g.apply f`, then each new goal. A failure of the application leaves the goal as it is. -/
meta partial def applyAllF (env : Env) (g : MVarId) (f : Expr) : MetaM (Array MVarId) := do
  let gs ← try g.apply f catch _ => return #[g]
  let mut stuck := #[]
  for g' in gs do
    unless ← g'.isAssigned do stuck := stuck ++ (← proveF env g')
  stuck.filterM fun g' => return !(← g'.isAssigned)

/-- `applyLemF`, with `prep` on each new goal (the memory of a goal can be a projection of a state
that a callee made). -/
meta partial def applyPrepF (env : Env) (g : MVarId) (name : Name) (args : Array Expr) :
    MetaM (Array MVarId) := do
  let some f ← (try some <$> lemApp name args catch _ => pure none) | return #[g]
  let gs ← try g.apply f catch _ => return #[g]
  let mut stuck := #[]
  for g' in gs do
    unless ← g'.isAssigned do
      if let some g'' ← Lift.Tactic.Room.prep env g' then stuck := stuck ++ (← proveF env g'')
  stuck.filterM fun g' => return !(← g'.isAssigned)

meta partial def applyLemF (env : Env) (g : MVarId) (name : Name) (args : Array Expr) :
    MetaM (Array MVarId) := do
  let some f ← (try some <$> lemApp name args catch _ => pure none) | return #[g]
  applyAllF env g f

meta partial def proveF (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  if let some (_, l, _) := t.eq? then
    let l := (← instantiateMVars l).consumeMData
    if l.isAppOfArity ``readRam 4 then return ← proveRead env g l
    if l.isAppOfArity ``writeRam 5 then return ← proveWrite env g l
    if l.isAppOfArity ``List.length 2 then return ← proveLen env g l
    return ← Lift.Tactic.Room.prove env g
  if t.isAppOfArity ``SysV.Outside 3 then return ← proveOutside env g
  if t.isAppOfArity ``SysV.InRoom 3 then return ← proveInRoom env g
  if t.isAppOf ``Std.ExtHashMap.sep then return ← proveSep env g
  if t.isAppOfArity ``Exists 2 || t.isAppOfArity ``And 2 then return ← proveBorder env g
  Lift.Tactic.Room.prove env g

/-- A read in the memory after a callee: the word is outside the room of the callee, so that it is
read in the memory at the call. -/
meta partial def readFar (env : Env) (g : MVarId) (policy m a : Expr) : MetaM (Option (Array MVarId)) := do
  for (pf, s', _) in ← calleesOf env m do
    let sp ← rspOf s'
    let sp' ← normBV env sp
    for r in env.rooms do
      unless ← withReducible (isDefEq r.policy policy) do continue
      let some j ← offset r.rsp sp' | continue
      let some k ← offset r.rsp a | continue
      let some hs ← proveAddr env sp (← subOf r.rsp j) | continue
      let some ha ← proveAddr env a (← subOf r.rsp k) | continue
      let s ← saveState
      let res ← applyPrepF env g ``readRam_far #[pf, hs, ha]
      if res.isEmpty then return some #[]
      s.restore
  return none

/-- `Outside` of a caller after a callee: the room of the callee is inside the room of the caller. -/
meta partial def outsideCompose (env : Env) (g : MVarId) (s m : Expr) :
    MetaM (Option (Array MVarId)) := do
  for (pf, s', _) in ← calleesOf env m do
    if ← withReducible (isDefEq s' s) then continue
    let sp := ← rspOf s'
    let R ← rspOf s
    let some j ← offset R (← normBV env sp) | continue
    let some hs ← proveAddr env sp (← subOf R j) | continue
    let saved ← saveState
    let res ← applyPrepF env g ``outside_compose #[pf, hs, ← mkEqRefl R]
    if res.isEmpty then return some #[]
    saved.restore
  return none

/-- A read: a slot of the formula, or the return word. -/
meta partial def proveRead (env : Env) (g : MVarId) (l : Expr) : MetaM (Array MVarId) := do
  let args := l.getAppArgs
  unless ← isW64 args[3]! do return ← Lift.Tactic.Room.prove env g
  let m ← instantiateMVars args[1]!
  let a ← instantiateMVars args[2]!
  if let some r ← readFar env g args[0]! m a then return r
  let some (P, h) ← sepOf env 1 m | return ← Lift.Tactic.Room.prove env g
  let atoms ← reifyClauses extHashMapOps (← instantiateMVars P)
  if let some (sl, ha) ← findSlot env atoms a then
    unless sl.val?.isSome do return #[g]
    let some hm ← slotFirst P h m atoms sl | return #[g]
    return ← applyLemF env g ``readRam_slot #[hm, ha]
  for r in env.rooms do
    unless ← withReducible (isDefEq args[0]! r.policy) do continue
    unless (← offset r.rsp a) == some 0 do continue
    let s ← saveState
    let res ← applyLemF env g ``readRam_ret #[r.pf]
    if res.isEmpty then return #[]
    s.restore
  return #[g]

/-- A write: a slot of 8 bytes, the permit of the room, and the new memory. -/
meta partial def proveWrite (env : Env) (g : MVarId) (l : Expr) : MetaM (Array MVarId) := do
  let args := l.getAppArgs
  unless ← isW64 args[3]! do return ← Lift.Tactic.Room.prove env g
  let m ← instantiateMVars args[1]!
  let a ← instantiateMVars args[2]!
  let some (P, h) ← sepOf env 1 m | return ← Lift.Tactic.Room.prove env g
  let atoms ← reifyClauses extHashMapOps (← instantiateMVars P)
  let some (sl, ha) ← findSlot env atoms a | return #[g]
  let some len := sl.len? | return #[g]
  let some hm ← slotFirst P h m atoms sl | return #[g]
  applyLemF env g ``writeRam_slot #[hm, ha, len]

/-- The length of a word, or a fact (only for bytes without metavariables). -/
meta partial def proveLen (env : Env) (g : MVarId) (l : Expr) : MetaM (Array MVarId) := do
  let bs ← instantiateMVars l.appArg!
  if bs.hasExprMVar then return #[g]
  if let some i ← toBytes8? bs then
    g.assign (← mkAppM ``Int.toBytes_length #[mkNatLit 8, i])
    return #[]
  for (pf, ty) in env.hyps do
    unless ty.isAppOf ``Eq && (ty.eq?.map (·.2.1.isAppOfArity ``List.length 2)).getD false do continue
    if ← withReducible (isDefEq ty (← g.getType)) then
      g.assign pf
      return #[]
  return #[g]

/-- The bytes outside the room: the formula of `m` is the slots and `Eq rest`, and each slot is in
the room. -/
meta partial def proveOutside (env : Env) (g : MVarId) : MetaM (Array MVarId) := do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let m ← instantiateMVars t.appArg!
  if let some r ← outsideCompose env g (← instantiateMVars (t.getArg! 0)) m then return r
  let some (P, h) ← sepOf env 1 m | return ← Lift.Tactic.Room.prove env g
  let atoms ← reifyClauses extHashMapOps (← instantiateMVars P)
  let some rest := atoms.find? (·.isAppOfArity ``Eq 2) | return #[g]
  let some Q ← mkChain (atoms.filter (· != rest)) | return #[g]
  let some hm ← reorder P h m (← mkAppM ``Std.ExtHashMap.sep #[Q, rest]) | return #[g]
  applyLemF env g ``SysV.Outside.of_sep #[hm]

/-- The footprint of a formula: `InRoom.sep` for each `⋆`, and one lemma for each slot. -/
meta partial def proveInRoom (env : Env) (g : MVarId) : MetaM (Array MVarId) := do
  let args := (← instantiateMVars (← g.getType)).consumeMData.getAppArgs
  let P ← instantiateMVars args[2]!
  if P.isAppOf ``Std.ExtHashMap.sep then
    return ← applyAllF env g (← mkConstWithFreshMVarLevels ``SysV.InRoom.sep)
  let some sl ← slot? env P | return #[g]
  let some k ← offset args[0]! sl.addr | return #[g]
  applyLemF env g (if sl.val?.isSome then ``inRoom_word else ``inRoom_bytes) #[mkNatLit k]

/-- An entailment `m =⋆ P'` from the formula of `m`. The addresses of `P'` are first written in the
spelling of the formula. -/
meta partial def proveSep (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let m := (← instantiateMVars (← g.getType)).appArg!
  let some (P, h) ← sepOf env 1 m | return #[g]
  let atoms ← reifyClauses extHashMapOps (← instantiateMVars P)
  let mut g := g
  for atom in ← reifyClauses extHashMapOps (← instantiateMVars (← g.getType)).appFn! do
    let some sl ← slot? env atom | continue
    let some (sl₀, p) ← findSlot env atoms sl.addr | continue
    if sl.addr == sl₀.addr then continue
    let r ← g.rewrite (← g.getType) p
    g ← g.replaceTargetEq r.eNew r.eqProof
  -- A slot with an unknown part (`Mem.Bytes a ?bs`) is matched with the slot of the same address,
  -- so that the cancellation of Kraken compares closed atoms only.
  for atom in ← reifyClauses extHashMapOps (← instantiateMVars (← g.getType)).appFn! do
    unless atom.hasExprMVar do continue
    let some sl ← slot? env atom | continue
    let some (sl₀, _) ← findSlot env atoms sl.addr | continue
    let s ← saveState
    unless ← isDefEq atom sl₀.atom do s.restore
  let t ← instantiateMVars (← g.getType)
  let s ← saveState
  let some eq ← solveSepEq extHashMapOps P t.appFn! | do s.restore; return #[g]
  g.assign (← mkEqMP (← mkCongrFun eq t.appArg!) h)
  return #[]

/-- A border goal: `∃` and `∧` are cut into goals (the witnesses are metavariables), the formula
first, then the lengths and `Outside`. -/
meta partial def proveBorder (env : Env) (g : MVarId) : MetaM (Array MVarId) := do
  let leaves ← cut g
  let isSep (l : MVarId) : MetaM Bool := do return (← instantiateMVars (← l.getType)).isAppOf ``Std.ExtHashMap.sep
  let mut stuck := #[]
  for l in leaves do
    if ← isSep l then stuck := stuck ++ (← proveF env l)
  for l in leaves do
    unless ← isSep l do stuck := stuck ++ (← proveF env l)
  return stuck

meta partial def cut (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  if t.isAppOfArity ``Exists 2 then
    let α := t.appFn!.appArg!
    let p := t.appArg!
    let w ← mkFreshExprMVar α
    let g' ← mkFreshExprMVar (mkApp p w).headBeta
    g.assign (mkApp4 (mkConst ``Exists.intro t.getAppFn.constLevels!) α p w g')
    return ← cut g'.mvarId!
  if t.isAppOfArity ``And 2 then
    let ga ← mkFreshExprMVar t.appFn!.appArg!
    let gb ← mkFreshExprMVar t.appArg!
    g.assign (mkApp4 (mkConst ``And.intro) t.appFn!.appArg! t.appArg! ga gb)
    return (← cut ga.mvarId!) ++ (← cut gb.mvarId!)
  return #[g]

end

/-! ## The call return (`frame_call`)

The goals of the return of a call that `frame_mem` does not close: the room of the callee, the words
of the room that stay mapped, and a mapped word that a write needs. They are in `frame_call`, not in
`frame_mem`, so that a proof that closes them by hand (`Lift/Spike/OuterMemSep.lean`) keeps its
`case` lines. -/

mutual

/-- `g.apply f`, then each new goal by `proveCall`. A failure of the application leaves the goal. -/
meta partial def applyCall (env : Env) (g : MVarId) (f : Expr) : MetaM (Array MVarId) := do
  let gs ← try g.apply f catch _ => return #[g]
  let mut stuck := #[]
  for g' in gs do
    unless ← g'.isAssigned do stuck := stuck ++ (← proveCall env g')
  stuck.filterM fun g' => return !(← g'.isAssigned)

/-- The goals of a call return, or a goal of `frame_mem` (then a stuck `Mem.loadInt m a 8 ≠ none`,
which the permit of a write leaves, is `proveLoaded`). -/
meta partial def proveCall (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  if t.isAppOfArity ``SysV.StackRoom 3 then return ← proveCalleeRoom env g
  if t.isAppOfArity ``SysV.Mapped 4 then return ← proveWords env g
  let mut stuck := #[]
  for g' in ← proveF env g do stuck := stuck ++ (← proveLoaded env g')
  return stuck

/-- The room of a callee (`SysV.StackRoom policy t n'`, with `t` the state at the entry of the
callee): the permits are those of a room of the caller whose `rsp` is `j` bytes above the `rsp` of
`t` (`StackRoom.callee`), and the words of the callee room are `proveWords`. When no attempt
closes the goal, the side goals of the first attempt stay (a `decide` that is false, a word that is
not mapped). -/
meta partial def proveCalleeRoom (env : Env) (g : MVarId) : MetaM (Array MVarId) := do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let sp ← rspOf (t.getArg! 1)
  let sp' ← normBV env sp
  let mut first : Option (Expr × Expr) := none
  for r in env.rooms do
    unless ← withReducible (isDefEq r.policy (t.getArg! 0)) do continue
    let some j ← offset r.rsp sp' | continue
    let some hs ← proveAddr env sp (← subOf r.rsp j) | continue
    let s ← saveState
    let res ← applyCall env g (← lemApp ``SysV.StackRoom.callee #[r.pf, hs])
    if res.isEmpty then return #[]
    s.restore
    if first.isNone then first := some (r.pf, hs)
  let some (pf, hs) := first | return #[g]
  applyCall env g (← lemApp ``SysV.StackRoom.callee #[pf, hs])

/-- The words `Mapped R lo hi m` of a room, in this order: no word (`hi < lo`); a fact `Mapped` about
`m`, or the words of a room whose start memory is `m` (`Mapped.mono`); a store on `m₀` (the store
keeps the words mapped: `Mapped.storeInt`); the memory after a callee, with its `post`
`Outside s' n' m` and `Mapped (rsp s') 8 n' m` in the context (`Mapped.after`; the words of the
memory at the call are `s'.data.dmem`). -/
meta partial def proveWords (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let R ← instantiateMVars (t.getArg! 0)
  let m0 ← instantiateMVars (t.getArg! 3)
  let m ← whnfR (← unlet m0)
  let s ← saveState
  if (← applyCall env g (← mkConstWithFreshMVarLevels ``SysV.Mapped.of_lt)).isEmpty then return #[]
  s.restore
  for (pf, ty) in ← mappedOf env m do
    unless ← sameAddr env (ty.getArg! 0) R do continue
    let s ← saveState
    if (← applyCall env g (← lemApp ``SysV.Mapped.mono #[pf])).isEmpty then return #[]
    s.restore
  for r in env.rooms do
    unless ← withReducible (isDefEq r.dmem m) do continue
    unless ← sameAddr env r.rsp R do continue
    let s ← saveState
    let pf ← mkAppM ``SysV.StackRoom.mapped #[r.pf]
    if (← applyCall env g (← lemApp ``SysV.Mapped.mono #[pf])).isEmpty then return #[]
    s.restore
  if m.isAppOfArity ``Mem.storeInt 5 then
    return ← applyCall env g (← mkConstWithFreshMVarLevels ``SysV.Mapped.storeInt)
  for (pf, s', _) in ← calleesOf env m do
    let sp ← rspOf s'
    let sp' ← normBV env sp
    let some j ← offset R sp' | continue
    let some hs ← proveAddr env sp (← subOf R j) | continue
    for (mp, ty) in ← mappedOf env m do
      unless ← withReducible (isDefEq (ty.getArg! 0) sp) do continue
      let some f ← (try some <$> lemApp ``SysV.Mapped.after #[pf, hs, mp] catch _ => pure none) | continue
      return ← applyCall env g f
  return #[g]

/-- A goal `Mem.loadInt m a 8 ≠ none` that stays after `Lift.Tactic.Room.prove` (the permission of a
write needs it): the word is one of the words of a `Mapped` fact, or of the room of the caller,
which `proveWords` proves. -/
meta partial def proveLoaded (env : Env) (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let_expr Ne _ l _ := t | return #[g]
  let_expr Mem.loadInt _ _ a n := l | return #[g]
  unless (← (evalNat n).run) == some 8 do return #[g]
  let mut sps := env.rooms.map (·.rsp)
  for (_, ty) in env.hyps do
    if ty.isAppOfArity ``SysV.Mapped 4 then sps := sps.push (ty.getArg! 0)
  for sp in sps do
    let some k ← offset sp a | continue
    let some ha ← proveAddr env a (← subOf sp k) | continue
    let s ← saveState
    if (← applyCall env g (← lemApp ``SysV.Mapped.loadInt #[ha])).isEmpty then return #[]
    s.restore
  return #[g]

end

/-! ## The tactic -/

/-- A fact that a side goal can need (`Lift.Tactic.Room.relevant`, and a formula, a length). -/
meta def relevant (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  Lift.Tactic.Room.relevant ty || (ty.isApp && isSepPred ty.appFn!) ||
    ty.isAppOfArity ``SysV.Mapped 4 ||
    (match ty.eq? with
      | some (_, l, _) => l.isAppOfArity ``List.length 2
      | none => false)

/-- The goal without the facts of the context that are not `relevant`. -/
meta def tidy (g : MVarId) : MetaM MVarId := g.withContext do
  let mut drop := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail || d.isLet then continue
    if (← isProp d.type) && !relevant (← instantiateMVars d.type) then drop := drop.push d.fvarId
  g.tryClearMany drop

/-- The side goals that stay (none: the goal is closed). -/
meta def frameMemCore (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let env ← mkEnv
  let some g ← prep env g | return #[]
  proveF env g

/-- The side goals that stay after `frame_call` (none: the goal is closed). -/
meta def frameCallCore (g : MVarId) : MetaM (Array MVarId) := g.withContext do
  let env ← mkEnv
  let some g ← prep env g | return #[]
  proveCall env g

end Lift.Tactic.Frame

/-- `frame_mem`: closes a memory side goal of a stack room in separation form, or fails with the side
goals that it cannot close (see `Lift/Tactic/FrameMem.lean`). -/
syntax (name := frameMem) "frame_mem" : tactic

open Lean Elab Tactic Lift.Tactic.Frame in
@[tactic frameMem] meta def evalFrameMem : Tactic := fun _ => withMainContext do
  let rest ← Lean.Meta.withAssignableSyntheticOpaque (frameMemCore (← getMainGoal))
  unless rest.isEmpty do
    let shown ← rest.mapM (fun g => (tidy g : MetaM MVarId))
    throwError "frame_mem: stuck at{indentD (MessageData.joinSep (shown.toList.map MessageData.ofGoal) "\n\n")}"
  replaceMainGoal []

/-- `frame_call`: `frame_mem`, and the goals of the return of a call: the room of the callee
(`SysV.StackRoom policy t n'` for the state `t` at the entry of the callee), the words of the room
that stay mapped (`SysV.Mapped R lo hi m`), and the mapped word that a write needs. It uses the
facts of the context, the room of the caller and the `post` of the callee
(`Outside s' n' m`, `Mapped (rsp s') 8 n' m`). It fails with the side goals that it cannot close
(see `Lift/Tactic/FrameMem.lean`). -/
syntax (name := frameCall) "frame_call" : tactic

open Lean Elab Tactic Lift.Tactic.Frame in
@[tactic frameCall] meta def evalFrameCall : Tactic := fun _ => withMainContext do
  let rest ← Lean.Meta.withAssignableSyntheticOpaque (frameCallCore (← getMainGoal))
  unless rest.isEmpty do
    let shown ← rest.mapM (fun g => (tidy g : MetaM MVarId))
    throwError "frame_call: stuck at{indentD (MessageData.joinSep (shown.toList.map MessageData.ofGoal) "\n\n")}"
  replaceMainGoal []
