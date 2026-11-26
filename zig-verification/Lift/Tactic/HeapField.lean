module

public import Lift.Sem.HeapFields
public import Lift.Sem.HeapSpan
public import Lift.Sem.Bridge
public import Lift.Tactic.LoopSimpAttr
public import Std.Tactic.BVDecide
public meta import Lean.Elab.Tactic

@[expose] public section

/-! The rules of `loop_close` for the typed objects of a statement (task UP-OBJ): records with fields of several widths,
padding, vector fields, and arrays of records (`Lift/Sem/HeapFields.lean`).

- `bvOffToNat`: `(a - b).toNat` of `BitVec 64`, with `a` and `b` sums of atoms times numbers and a number, is
  `Σ atom.toNat * c + n` when `bv_omega` proves it (the bounds come from the context). It gives the offset of an access
  in an object as a natural number, of the form `k * s + r` of `cellGet_flatMap`.
- `heap_found` proves `Heap.Found a w ?v h` and `heap_store` proves `Heap.StoreAt a w v h ?h'`: each tries the objects of
  the list `h` in order and computes the cell with the simp set `heap_field`; the result `?v` (or `?h'`) is assigned by
  the proof. They are dischargers of `simp` for `Heap.load_of_found` and `Heap.store_of_storeAt`.
- `heap_obj_mem` proves `toObj o ∈ h` (for `Bridge.has_of_holds_mem`): the object of the list with the same address,
  writability and cells after `heap_field`. -/

namespace Lift.Tactic

open Lean Meta Elab Tactic

/-- A linear form over `BitVec 64`: atoms with integer coefficients, and a constant. -/
structure Lin where
  terms : List (Expr × Int) := []
  const : Int := 0

meta def Lin.add (a b : Lin) : Lin :=
  { terms := b.terms.foldl (fun acc (e, c) =>
      match acc.find? (·.1 == e) with
      | some _ => acc.map fun (e', c') => if e' == e then (e', c' + c) else (e', c')
      | none => acc ++ [(e, c)]) a.terms,
    const := a.const + b.const }

meta def Lin.scale (k : Int) (a : Lin) : Lin :=
  { terms := a.terms.map fun (e, c) => (e, k * c), const := k * a.const }

/-- A number of 64 bits as a signed number: `2 ^ 64 - k` (the `- k` of the code) is `-k`. -/
meta def signed64 (n : Nat) : Int := if n < 2 ^ 63 then n else (n : Int) - 2 ^ 64

/-- The linear form of a term of `BitVec 64`; `toBitVec` of a sum or a product of `UInt64` goes inside. A number is signed
(`signed64`): the code writes `x - 1` as `x + 18446744073709551615`. -/
meta partial def linOf (e : Expr) : MetaM Lin := do
  let e ← instantiateMVars e
  if let .fvar id := e then
    if let some value := (← id.getDecl).value? then return ← linOf value
  if let some ⟨64, v⟩ ← getBitVecValue? e then return { const := signed64 v.toNat }
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, y]) => return (← linOf x).add (← linOf y)
  | (``HSub.hSub, #[_, _, _, _, x, y]) => return (← linOf x).add ((← linOf y).scale (-1))
  | (``HMul.hMul, #[_, _, _, _, x, y]) =>
    if let some ⟨64, v⟩ ← getBitVecValue? y then return (← linOf x).scale (signed64 v.toNat)
    if let some ⟨64, v⟩ ← getBitVecValue? x then return (← linOf y).scale (signed64 v.toNat)
    return { terms := [(e, 1)] }
  | (``UInt64.toBitVec, #[u]) =>
    let tb (x : Expr) : Expr := mkApp (mkConst ``UInt64.toBitVec) x
    match u.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, x, y]) => return (← linOf (tb x)).add (← linOf (tb y))
    | (``HMul.hMul, #[_, _, _, _, x, y]) =>
      if let some n ← getUInt64Value? y then return (← linOf (tb x)).scale (signed64 n.toNat)
      if let some n ← getUInt64Value? x then return (← linOf (tb y)).scale (signed64 n.toNat)
      return { terms := [(e, 1)] }
    | _ =>
      if let some n ← getUInt64Value? u then return { const := signed64 n.toNat }
      return { terms := [(e, 1)] }
  | _ => return { terms := [(e, 1)] }

/-- `e.toNat` of an atom of `BitVec 64`; `u.toNat` for `u.toBitVec`, the form of the statements and of `omega`. -/
meta def atomToNat (e : Expr) : MetaM Expr := do
  match e.getAppFnArgs with
  | (``UInt64.toBitVec, #[u]) => mkAppM ``UInt64.toNat #[u]
  | _ => mkAppM ``BitVec.toNat #[e]

/-- The natural number `Σ atom.toNat * c + const` of a linear form with no negative part. With `down`, a negative constant
`-d` goes into the first term `(e, c)`: `(e.toNat - q) * c + r` with `q * c - r = d` and `r < c` (an index `i - q` of a
loop that counts down, the form `k * s + r` of `cellGet_flatMap`); `omega` checks it. -/
meta partial def Lin.toNatExpr (l : Lin) (atom : Expr → MetaM Expr := atomToNat) (down : Bool := false) : MetaM (Option Expr) := do
  let terms := l.terms.filter (·.2 != 0)
  if terms.any (·.2 < 0) then return none
  if l.const < 0 then
    let (e, c) :: rest := terms | return none
    unless down do return none
    let q := (-l.const + c - 1) / c
    let first ← mkAppM ``HSub.hSub #[← atom e, mkNatLit q.toNat]
    let first ← if c == 1 then pure first else mkAppM ``HMul.hMul #[first, mkNatLit c.toNat]
    let l' : Lin := { terms := rest, const := q * c + l.const }
    let some r ← l'.toNatExpr atom | return none
    return some (← if r.nat? == some 0 then pure first else mkAppM ``HAdd.hAdd #[first, r])
  let parts ← terms.mapM fun (e, c) => do mkAppM ``HMul.hMul #[← atom e, mkNatLit c.toNat]
  let sum? ← parts.foldlM (init := none) fun acc p => do
    match acc with
    | none => pure (some p)
    | some a => some <$> mkAppM ``HAdd.hAdd #[a, p]
  match sum? with
  | none => return some (mkNatLit l.const.toNat)
  | some s => if l.const == 0 then return some s else some <$> mkAppM ``HAdd.hAdd #[s, mkNatLit l.const.toNat]

/-- `uint_bounds`: `u.toNat < 2 ^ 64` for each `u.toNat` of `UInt64` of the goal and the hypotheses, which `omega` does not
know. A fact that the context has already is not added again. -/
syntax (name := uintBounds) "uint_bounds" : tactic

@[tactic uintBounds] meta def evalUintBounds : Tactic := fun _ => do
  let g ← getMainGoal
  let g ← g.withContext do
    let decls := (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d
    let tys ← (decls.map (·.type) |>.push (← g.getType)).mapM instantiateMVars
    let r ← IO.mkRef (#[] : Array Expr)
    for t in tys do
      Meta.forEachExpr t fun e => do
        if e.isAppOfArity ``UInt64.toNat 1 && !e.hasLooseBVars then
          r.modify fun a => if a.contains e then a else a.push e
    let atoms ← r.get
    let mut g := g
    let mut known := tys
    for a in atoms do
      let pf ← mkAppM ``UInt64.toNat_lt #[a.appArg!]
      let ty ← inferType pf
      unless known.contains ty do
        known := known.push ty
        let (_, g') ← (← g.assert `hbound ty pf).intro1P
        g := g'
    return g
  replaceMainGoal [g]

theorem toNat_sub_self (a : BitVec 64) : (a - a).toNat = 0 := by simp

/-- A sum with a number of 64 bits at or above `2 ^ 63` (the `- k` of the code) as a subtraction of `2 ^ 64 - n`. The proof
of `bitvec_to_nat` on `x + 18446744073709551608` took the kernel more than 200000 heartbeats (deterministic timeout); on
`x - 8` it takes few. -/
theorem _root_.BitVec.add_lit_eq_sub (x : BitVec 64) (n : Nat) (h : 2 ^ 63 ≤ n) (h' : n < 2 ^ 64) :
    x + (no_index (OfNat.ofNat n : BitVec 64)) = x - BitVec.ofNat 64 (2 ^ 64 - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  show (x.toNat + n % 2 ^ 64) % 2 ^ 64 = _
  omega

-- The closer `bv_norm` of `loop_close` (task LC-DOWN): `x + 18446744073709551615` as `x - 1` before `bitvec_to_nat`.
attribute [bv_norm] BitVec.add_lit_eq_sub

/-- `(a - b).toNat` of `BitVec 64` as `Σ atom.toNat * c + n`, when `bv_omega` proves it in the context. Not a default
simproc: only the steps of typed objects name it. The offset of the base of an object (`a` is `b`) is 0 with no
`omega`. -/
simproc_decl bvOffToNat (BitVec.toNat (_ - _)) := fun e => do
  let_expr BitVec.toNat w d := e | return .continue
  let some 64 ← (evalNat w).run | return .continue
  let_expr HSub.hSub _ _ _ _ a b := d | return .continue
  if a == b then return .done { expr := mkNatLit 0, proof? := some (mkApp (mkConst ``toNat_sub_self) a) }
  let l := (← linOf a).add ((← linOf b).scale (-1))
  let some n ← l.toNatExpr (down := true) | return .continue
  if n == e then return .continue
  -- Unfold scalar aliases in this offset only. Keep model records, heaps,
  -- and vectors opaque; no hypothesis is rewritten for this calculation.
  let scalar ← transform e (pre := fun sub => do
    let .fvar id := sub | return .continue
    let decl ← id.getDecl
    let some value := decl.value? | return .done sub
    let type ← whnfR decl.type
    unless type.isAppOf ``BitVec || type.isConstOf ``UInt64 || type.isConstOf ``Nat do
      return .done sub
    return .visit value)
  let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq scalar n)
  -- Only the goal: the step `flag-norm` gives the bounds of the context as facts of `toNat`, and a `simp` at each
  -- hypothesis (the heaps included) for each offset took more time (the heap-fields steps of l2zIdxPush: 34 s, not 27 s).
  let tac ← `(tactic| ((try simp only [UInt64.toBitVec_add, UInt64.toBitVec_mul, UInt64.toBitVec_ofNat,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat]) <;>
    (try simp (disch := decide) only [BitVec.add_lit_eq_sub, Nat.reducePow, Nat.reduceSub]) <;>
    (try simp only [bitvec_to_nat, UInt64.toNat_toBitVec]) <;> uint_bounds <;> omega))
  -- A failed `omega` logs an error; the state and the messages are restored after each attempt, so that only a proof
  -- with no new error is kept and no error stays in the log of the goal.
  let s ← (saveState : MetaM Meta.SavedState)
  let msgs := (← getThe Core.State).messages
  let proof? ← try
      -- Only the hypotheses that mention the atoms of the offset (`cleanup`): `omega` reads each hypothesis of the
      -- context, and the heaps of the context are large.
      -- A number offset needs no hypothesis.
      let g ← m.mvarId!.cleanup (indirectProps := l.terms.any (·.2 != 0))
      let gs ← Term.TermElabM.run' (Tactic.run g (evalTactic tac))
      let p ← instantiateMVars m
      let errs := (← getThe Core.State).messages.toList.filter (·.severity == .error) |>.length
      let errs0 := msgs.toList.filter (·.severity == .error) |>.length
      pure (if gs.isEmpty && errs == errs0 && !p.hasMVar && !p.hasSorry then some p else none)
    catch _ => pure none
  -- on success the environment keeps the auxiliary declarations of the proof
  if proof?.isNone then (s.restore : MetaM Unit)
  modifyThe Core.State fun st => { st with messages := msgs }
  let some p := proof? | return .continue
  return .done { expr := n, proof? := some p }

/-- A proof of `ty` by `tac` in the context, or `none`. A failed tactic logs errors; the state and the messages are
restored after each attempt, so that only a proof with no new error is kept and no error stays in the log of the goal. -/
meta def proveBy? (ty : Expr) (tac : TSyntax `tactic) : MetaM (Option Expr) := do
  let m ← mkFreshExprSyntheticOpaqueMVar ty
  let s ← (saveState : MetaM Meta.SavedState)
  let msgs := (← getThe Core.State).messages
  let proof? ← try
      let gs ← Term.TermElabM.run' (Tactic.run m.mvarId! (evalTactic tac))
      let p ← instantiateMVars m
      let errs := (← getThe Core.State).messages.toList.filter (·.severity == .error) |>.length
      let errs0 := msgs.toList.filter (·.severity == .error) |>.length
      pure (if gs.isEmpty && errs == errs0 && !p.hasMVar && !p.hasSorry then some p else none)
    catch _ => pure none
  -- on success the environment keeps the auxiliary declarations of the proof
  if proof?.isNone then (s.restore : MetaM Unit)
  modifyThe Core.State fun st => { st with messages := msgs }
  return proof?

/-- The linear form of a term of `Nat` with `+`, `-` (as on `Int`: `omega` checks the result), a product with a number,
and `min a b` (as `a` or `b` when `omega` proves the order). -/
meta partial def linOfNat (e : Expr) : MetaM Lin := do
  let e ← instantiateMVars e
  if let some n ← getNatValue? e then return { const := n }
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, y]) => return (← linOfNat x).add (← linOfNat y)
  | (``HSub.hSub, #[_, _, _, _, x, y]) => return (← linOfNat x).add ((← linOfNat y).scale (-1))
  | (``HMul.hMul, #[_, _, _, _, x, y]) =>
    if let some n ← getNatValue? y then return (← linOfNat x).scale n
    if let some n ← getNatValue? x then return (← linOfNat y).scale n
    return { terms := [(e, 1)] }
  | (``Min.min, #[_, _, x, y]) =>
    let omega ← `(tactic| omega)
    if (← proveBy? (← mkAppM ``LE.le #[x, y]) omega).isSome then return ← linOfNat x
    if (← proveBy? (← mkAppM ``LE.le #[y, x]) omega).isSome then return ← linOfNat y
    return { terms := [(e, 1)] }
  | _ => return { terms := [(e, 1)] }

/-- An offset `d : Nat` with a `-` or a `min` as `Σ atom * c + n`, with the proof of `omega`. -/
meta def normNatOff? (d : Expr) : MetaM (Option (Expr × Expr)) := do
  unless (d.find? fun x => x.isAppOf ``HSub.hSub || x.isAppOf ``Min.min).isSome do return none
  let some n ← (← linOfNat d).toNatExpr pure | return none
  if n == d then return none
  let some p ← proveBy? (← mkEq d n) (← `(tactic| omega)) | return none
  return some (n, p)

/-- The offset of `cellGet cs d w` in the form `Σ atom * c + n` (`normNatOff?`): after a store at a run-time index, the
cells of an array are three parts, and the offset of a later cell is a difference of their sizes. Not a default simproc. -/
simproc_decl natOffGet (Lift.Sem.cellGet _ _ _) := fun e => do
  let_expr Lift.Sem.cellGet cs d w := e | return .continue
  let some (n, p) ← normNatOff? d | return .continue
  let f := mkApp (mkConst ``Lift.Sem.cellGet) cs
  return .done { expr := mkApp2 f n w, proof? := some (← mkCongrFun (← mkCongrArg f p) w) }

/-- `natOffGet` for `cellSet cs d w v`. -/
simproc_decl natOffSet (Lift.Sem.cellSet _ _ _ _) := fun e => do
  let_expr Lift.Sem.cellSet cs d w v := e | return .continue
  let some (n, p) ← normNatOff? d | return .continue
  let f := mkApp (mkConst ``Lift.Sem.cellSet) cs
  return .done { expr := mkApp3 f n w v, proof? := some (← mkCongrFun (← mkCongrFun (← mkCongrArg f p) w) v) }

/-- The side conditions of the `heap_field` rules: `omega`, after `heap_field` on the sizes. `refine id ?_` gives the
proof the type of the side condition: the size rules are `rfl` lemmas, so the proof of `simp` can have the type
`8 = 8`, which the outer `simp` does not take at reducible transparency for `cellsSize (g x) = 8`. -/
syntax "field_disch" : tactic

/-- The bytes of a width constant `Width.W8` … `Width.W64`. -/
meta def widthBytes? (w : Expr) : MetaM (Option Nat) := do
  match (← instantiateMVars w).constName? with
  | some ``Width.W8 => return some 1
  | some ``Width.W16 => return some 2
  | some ``Width.W32 => return some 4
  | some ``Width.W64 => return some 8
  | _ => return none

/-- The value of a closed number term of the side conditions: a numeral, `+`, `*`, `-`, and `c.w.bytes` of a cell
`⟨W, v⟩` or `W.bytes` of a width constant. -/
meta partial def closedNat? (e : Expr) : MetaM (Option Nat) := do
  let op (f : Nat → Nat → Nat) : Option Nat → Option Nat → Option Nat
    | some a, some b => some (f a b)
    | _, _ => none
  let e ← instantiateMVars e
  if let some n := e.nat? then return some n
  if let some n := e.rawNatLit? then return some n
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, y]) => return op (· + ·) (← closedNat? x) (← closedNat? y)
  | (``HMul.hMul, #[_, _, _, _, x, y]) => return op (· * ·) (← closedNat? x) (← closedNat? y)
  | (``HSub.hSub, #[_, _, _, _, x, y]) => return op (· - ·) (← closedNat? x) (← closedNat? y)
  | (``Width.bytes, #[w]) =>
    let w := if w.isAppOfArity ``Lift.Sem.Cell.w 1 && (w.getArg! 0).isAppOfArity ``Lift.Sem.Cell.mk 2 then
      (w.getArg! 0).getArg! 0 else w
    widthBytes? w
  | _ => return none

/-- `nat_lit_check`: a side condition `a ≤ b` or `a < b` of closed numbers (`closedNat?`) fails at once when it is false
(`omega` on a false side condition read each hypothesis of the context first: `cellGet_cons_ge` at the offset 0 is tried
before `cellGet_cons_zero`). Else it does nothing. -/
syntax (name := natLitCheck) "nat_lit_check" : tactic

@[tactic natLitCheck] meta def evalNatLitCheck : Tactic := fun _ => do
  let t ← instantiateMVars (← getMainTarget)
  let rel : Option (Bool × Expr × Expr) := match t.getAppFnArgs with
    | (``LE.le, #[ty, _, a, b]) => if ty.isConstOf ``Nat then some (false, a, b) else none
    | (``LT.lt, #[ty, _, a, b]) => if ty.isConstOf ``Nat then some (true, a, b) else none
    | _ => none
  let some (strict, a, b) := rel | return
  let some x ← closedNat? a | return
  let some y ← closedNat? b | return
  unless (if strict then x < y else x ≤ y) do throwError "nat_lit_check: {x} {if strict then "<" else "≤"} {y} is false"

/-- `omega` with only the hypotheses that mention the variables of the goal (`MVarId.cleanup`). -/
syntax (name := omegaNear) "omega_near" : tactic

@[tactic omegaNear] meta def evalOmegaNear : Tactic := fun _ => do
  replaceMainGoal [← (← getMainGoal).cleanup]
  evalTactic (← `(tactic| omega))

macro_rules
  | `(tactic| field_disch) => `(tactic| (refine id ?_; nat_lit_check; first
    -- one `omega` (a failed `omega` costs as much as a proof): the sizes go to numbers first
    | ((try simp only [heap_field, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]) <;> omega_near)
    | (simp only [heap_field, Nat.reduceMul, Nat.reduceAdd, implies_true]; done)
    | fail "field_disch"))

/-- `heap_off_check`: fails when the goal has an offset `(a - b).toNat` of `BitVec 64` whose linear form has a negative
part (`a` is not at or after the base `b` of the object). Then `heap_found` and `heap_store` go to the next object at
once, with no `omega` for the side conditions of the cells of this one. -/
syntax (name := heapOffCheck) "heap_off_check" : tactic

/-- The bytes of a list literal of cells `[⟨w₁, v₁⟩, …]` with width constants. -/
meta partial def litCellsSize? (cs : Expr) : MetaM (Option Nat) := do
  let cs ← instantiateMVars cs
  if cs.isAppOfArity ``List.nil 1 then return some 0
  unless cs.isAppOfArity ``List.cons 3 do return none
  let c := cs.getArg! 1
  unless c.isAppOfArity ``Lift.Sem.Cell.mk 2 do return none
  let some b ← widthBytes? (c.getArg! 0) | return none
  let some r ← litCellsSize? (cs.getArg! 2) | return none
  return some (b + r)

@[tactic heapOffCheck] meta def evalHeapOffCheck : Tactic := fun _ => do
  let t ← instantiateMVars (← getMainTarget)
  let some d := t.find? fun e => e.isAppOfArity ``BitVec.toNat 2 && (e.getArg! 1).isAppOfArity ``HSub.hSub 6 | return
  let_expr HSub.hSub _ _ _ _ a b := d.getArg! 1 | return
  let l := (← linOf a).add ((← linOf b).scale (-1))
  if (← l.toNatExpr (down := true)).isNone then throwError "heap_off_check: the address is not at or after the base"
  -- A number offset `n` and a list literal of cells of `s` bytes: with `n + w ≥ s` no cell of width `w` starts at `n`.
  if l.terms.any (·.2 != 0) then return
  let some c := t.find? fun e => e.isAppOfArity ``Lift.Sem.cellGet 3 && e.getArg! 1 == d | return
  let some s ← litCellsSize? (c.getArg! 0) | return
  let some wb ← widthBytes? (c.getArg! 2) | return
  if l.const.toNat + wb > s then throwError "heap_off_check: the offset is not inside the object"

/-- The cell of an object at an offset, with `heap_field`. -/
syntax "field_eval" : tactic
macro_rules
  | `(tactic| field_eval) => `(tactic|
      (dsimp -failIfUnchanged only [Lift.Sem.Obj.setAt]
       all_goals heap_off_check
       all_goals simp (disch := field_disch) only [bvOffToNat, natOffGet, natOffSet, heap_field, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
         Nat.reduceMod, Nat.reduceDiv, Option.isSome_some, reduceCtorEq]
       all_goals try rfl))

/-- `Heap.Found a w ?v h`: the first object of `h` whose cell at `a` the rules compute. -/
syntax "heap_found" : tactic
macro_rules
  | `(tactic| heap_found) => `(tactic| first
    | (apply Lift.Sem.Heap.Found.head; field_eval; done)
    | (apply Lift.Sem.Heap.Found.tail; heap_found)
    | fail "heap_found")

/-- `Heap.StoreAt a w v h ?h'`: the first writable object of `h` that has a cell at `a`. -/
syntax "heap_store" : tactic
macro_rules
  | `(tactic| heap_store) => `(tactic| first
    | (refine Lift.Sem.Heap.StoreAt.head ?_ ?_; (rfl); (field_eval; done))
    | (apply Lift.Sem.Heap.StoreAt.tail; heap_store)
    | fail "heap_store")

/-- `Heap.StoreSpanAt a w v h ?h'`: the first writable object of `h` with no cell of width `w` at `a` and whole cells
over `[a, a + w)` (a store over several fields, `Lift/Sem/HeapSpan.lean`). -/
syntax "heap_store_span" : tactic
macro_rules
  | `(tactic| heap_store_span) => `(tactic| first
    | (apply Lift.Sem.Heap.StoreSpanAt.head; (rfl); (focus (field_eval; done)); (focus (field_eval; done)))
    | (apply Lift.Sem.Heap.StoreSpanAt.tail; heap_store_span)
    | fail "heap_store_span")

/-- The discharger of the access rules of `loop_close` (step `heap-fields`): only the tactic for the form of the goal
(`Holds` by `assumption`, `Found`, `StoreAt`, `StoreSpanAt`, else `field_disch`). A side condition of one form does not
run the tactics of the other forms: `field_disch` on a `Holds` goal ran `omega` and a `simp` of the heap. -/
syntax (name := heapDisch) "heap_disch" : tactic

@[tactic heapDisch] meta def evalHeapDisch : Tactic := fun _ => do
  let t ← instantiateMVars (← getMainTarget)
  match t.getAppFn.constName? with
  | some ``Lift.Sem.Heap.Holds => evalTactic (← `(tactic| assumption))
  | some ``Lift.Sem.Heap.Found => evalTactic (← `(tactic| heap_found))
  | some ``Lift.Sem.Heap.StoreAt => evalTactic (← `(tactic| heap_store))
  | some ``Lift.Sem.Heap.StoreSpanAt => evalTactic (← `(tactic| heap_store_span))
  | _ => evalTactic (← `(tactic| first | assumption | field_disch))

/-- `toObj o ∈ h`: an object of the list `h` equal to `toObj o` after `heap_field`. -/
syntax "heap_obj_mem" : tactic
macro_rules
  | `(tactic| heap_obj_mem) => `(tactic| first
    | (apply List.mem_cons.mpr
       left
       simp (disch := field_disch) only [bvOffToNat, natOffGet, natOffSet, heap_field, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
         Lift.Sem.Obj.mk.injEq, reduceCtorEq, true_and, and_true,
         -- the field of a spec after a store (`(xs.set 0 v h)[0]`), and the casts of a narrow store as `setWidth`
         Vector.getElem_set_self, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth,
         BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, UInt64.toNat_toBitVec,
         -- the bytes of a number that a store of 16 bits writes over two fields of 8 bits
         BitVec.reduceSetWidth, BitVec.reduceExtractLsb', BitVec.ofNat_eq_ofNat, Width.bits,
         -- a narrow store of a bitwise operation
         BitVec.setWidth_xor, BitVec.setWidth_and, BitVec.setWidth_or,
         -- a value that the code computes as `x + 1 - 1` (an index after its increment)
         BitVec.add_sub_cancel]; done)
    | (apply List.mem_cons_of_mem; heap_obj_mem)
    | fail "heap_obj_mem")

/-- `Mem.has policy m o` from a hypothesis `Heap.Holds policy h m` with `toObj o ∈ h` (rule below `has_of_holds_mem`). -/
syntax "heap_has" : tactic

/-- The value of `f xs : List Object`, a definition `f` whose value is a list literal (`a :: t` or `[]`), such as the
objects of a statement that `loop_close` is not given. -/
meta def unfoldObjList? (e : Expr) : MetaM (Option Expr) := do
  let .const fn _ := e.getAppFn | return none
  let some (.defnInfo _) := (← getEnv).find? fn | return none
  if e.hasLooseBVars then return none
  let objs := mkApp (mkConst ``List [levelZero]) (mkConst ``Lift.Trusted.Object)
  let ty ← try instantiateMVars (← inferType e) catch _ => return none
  unless ty == objs do return none
  let some v ← unfoldDefinition? e | return none
  let v := v.headBeta
  if v.isAppOfArity ``List.cons 3 || v.isAppOfArity ``List.nil 1 then return some v
  return none

/-- `(f xs).addr`, `.fields` and `.writable` of an `Object` that a definition `f` gives: the field of the constructor
of `f xs`. Only the projections of `Object`. Also each `f xs : List Object` whose value is a list literal
(`unfoldObjList?`). -/
meta def reduceObjProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let .const fn _ := e.getAppFn | return .done e
    if let some v ← unfoldObjList? e then return .visit v
    unless fn == ``Lift.Trusted.Object.addr || fn == ``Lift.Trusted.Object.fields ||
      fn == ``Lift.Trusted.Object.writable do return .done e
    let some info ← getProjectionFnInfo? fn | return .done e
    if e.getAppNumArgs != info.numParams + 1 then return .done e
    let s := e.appArg!
    let .const sf _ := s.getAppFn | return .done e
    if (← getEnv).isConstructor sf then return .done e
    let s ← whnfD s
    let some c ← isConstructorApp? s | return .done e
    return .done (s.getArg! (c.numParams + info.i)))

/-- `reduceObjProjs` in each hypothesis and the goal of `g`. -/
meta def reduceObjProjsAll (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let t' ← reduceObjProjs t
    if t' != t then g ← g.replaceLocalDeclDefEq d.fvarId t'
  let t ← instantiateMVars (← g.getType)
  let t' ← reduceObjProjs t
  if t' != t then g ← g.replaceTargetDefEq t'
  return g

/-- The heaps `(h, h')` of a hypothesis `h.store a w v = .ok h'` or `h.storeB a w v = .ok h'`, and the lemma that gives
a `Holds` of `h'`. -/
meta def storeHeaps? (t : Expr) : Option (Expr × Expr × Name) := do
  let (_, l, r) ← t.eq?
  guard (r.isAppOfArity ``Lift.Sem.Res.ok 2)
  if l.isAppOfArity ``Lift.Sem.Heap.store 4 then return (l.getArg! 0, r.getArg! 1, ``Lift.Sem.Heap.store_holds)
  guard (l.isAppOfArity ``Lift.Sem.Heap.storeB 4)
  return (l.getArg! 0, r.getArg! 1, ``Lift.Sem.Heap.storeB_holds)

/-- The heap `h` of a hypothesis `Heap.Holds policy h m`. -/
meta def holdsHeap? (t : Expr) : Option Expr :=
  if t.isAppOfArity ``Lift.Sem.Heap.Holds 3 then some (t.getArg! 1) else none

/-- For each hypothesis `h.store a w v = .ok h'` with a `Holds` of `h` and none of `h'`, a new hypothesis
`Heap.Holds policy h' m'` (`Heap.store_holds`), so that the next access of a chain of stores has a `Holds`. -/
meta def addStoreHolds (g : MVarId) : MetaM MVarId := do
  let mut g := g
  for _ in [0:16] do
    let next ← g.withContext do
      let decls := (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d
      let types ← decls.mapM fun d => instantiateMVars d.type
      let held := types.filterMap holdsHeap?
      let pairs := (decls.zip types).filterMap fun (d, t) => do
        let (h, h', lem) ← storeHeaps? t
        guard !(held.contains h')
        let i ← types.findIdx? fun t => holdsHeap? t == some h
        return (decls[i]!.toExpr, d.toExpr, lem)
      match pairs[0]? with
      | none => return none
      | some (hh, hs, lem) =>
        let ex ← mkAppM lem #[hh, hs]
        return some (← instantiateMVars (← inferType ex), ex)
    let some (t, ex) := next | return g
    let (fv, g') ← (← g.assert `hstore t ex).intro1P
    let subgoals ← g'.cases fv
    let some sg := subgoals[0]? | return g
    -- the goal keeps its tag (`ret_1`, `nofault_2`, ...)
    sg.mvarId.setTag (← g.getTag)
    g := sg.mvarId
  return g

/-- For each object `o` of the list of a hypothesis `Heap.Holds policy (o₁ :: … :: t) m` (each `oᵢ` a constructor), a new
hypothesis `o.addr.toNat + o.size ≤ 2 ^ 64` (`Holds.noWrap`) in the form of `heap_field`, such as
`p.toNat + n.toNat * 8 ≤ 2 ^ 64` for an array of `n` words at `p`: `omega` needs it for the offset of an element at an
index below a length `n` that is not a number. Each object gives one fact, also when several `Holds` have it. -/
meta def addObjSizes : TacticM Unit := do
  let g ← getMainGoal
  let (g, names) ← g.withContext do
    let decls := (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d
    let mut seen : Array Expr := #[]
    let mut facts : Array (Expr × Expr) := #[]
    for d in decls do
      let t ← instantiateMVars d.type
      let some h := holdsHeap? t | continue
      -- the objects of the spine of `h`, each with the proof of its membership
      let mut rest := h
      let mut mem : Expr → MetaM Expr := pure
      while rest.isAppOfArity ``List.cons 3 do
        let o := rest.getArg! 1
        let t' := rest.getArg! 2
        let memHere := mem
        if o.isAppOfArity ``Lift.Sem.Obj.mk 3 && !seen.contains o then
          seen := seen.push o
          let pf ← memHere (← mkAppOptM ``List.mem_cons_self #[none, o, t'])
          let nw ← mkAppM ``Lift.Sem.Heap.Holds.noWrap #[d.toExpr]
          facts := facts.push (← inferType (mkApp2 nw o pf), mkApp2 nw o pf)
        mem := fun p => do memHere (← mkAppM ``List.mem_cons_of_mem #[o, p])
        rest := t'
    let mut g := g
    let mut names := #[]
    for (ty, pf) in facts do
      let n := Name.mkSimple s!"hsize{names.size}"
      let (_, g') ← (← g.assert n ty pf).intro1P
      g := g'
      names := names.push (mkIdent n)
    return (g, names)
  replaceMainGoal [g]
  if names.isEmpty then return
  evalTactic (← `(tactic| simp -failIfUnchanged only [Lift.Sem.Obj.size_eq_cellsSize, heap_field, Nat.reducePow,
    Nat.reduceMul, Nat.reduceAdd, UInt64.toNat_toBitVec] at $names*))

end Lift.Tactic

namespace Lift.Sem.Bridge

open Lift.P2.Total Lift.Trusted

/-- A memory that holds a heap has each object of the heap. -/
theorem has_of_holds_mem {policy : CpuPolicy} {h : Heap} {m : DataMem} {o : Object} (hh : h.Holds policy m)
    (ho : toObj o ∈ h) : Mem.has policy m o :=
  (has_iff policy m o).mpr ⟨hh.noWrap _ ho, hh.read _ ho, hh.write _ ho⟩

end Lift.Sem.Bridge

/-- `Mem.has policy m o`: `Bridge.has_of_holds_mem` with a hypothesis `Heap.Holds policy h m` (`assumption` finds `h`),
then `heap_obj_mem` for `toObj o ∈ h`. -/
macro_rules
  | `(tactic| heap_has) => `(tactic| (apply Lift.Sem.Bridge.has_of_holds_mem; (assumption); heap_obj_mem))

open Lift.Sem in
attribute [heap_field] cellsSize_nil cellsSize_cons cellsSize_append cellsSize_flatMap sum_map_const cellsSize_eq
  cellGet_nil cellGet_cons_zero cellGet_cons_ge cellGet_cons_mid cellGet_append_left cellGet_append_right
  cellGet_flatMap cellGet_flatMap_zero Cell.get_self cellSet_nil cellSet_cons_zero cellSet_cons_ge
  cellSet_append_left cellSet_append_right cellSet_flatMap cellSet_flatMap_zero flatMap_set Obj.setAt
  Lift.Sem.Bridge.toObj Lift.Sem.Bridge.toCell Lift.Trusted.Encode.encode
  List.map_append List.map_flatMap List.map_cons List.map_nil List.flatMap_cons List.flatMap_nil
  List.append_assoc List.cons_append List.nil_append List.append_nil
  Vector.length_toList Vector.getElem_toList Vector.toList_set List.length_take List.length_drop
  Width.bytes Nat.add_sub_assoc Nat.add_zero Nat.sub_self ite_true ite_false
  spanSet_zero_zero spanSet_cons_ge spanSet_cons_zero spanSet_append_left spanSet_append_right spanSet_flatMap
  spanSet_flatMap_zero Cell.get_ne_bytes Option.map_some
