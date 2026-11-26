module
public import Lean
public import Lift.Sem.Heap
@[expose] public section
namespace Lift.Tactic.HeapPartitionExact
open Lift.Sem

theorem extract_cons {a b : Obj} {xs ys : Heap} (h : xs.Perm (a :: ys)) :
    (b :: xs).Perm (a :: b :: ys) := by
  exact (h.cons b).trans (List.Perm.swap a b ys)

theorem extract_append_left {a : Obj} {xs ys : Heap} (h : xs.Perm (a :: ys)) (zs : Heap) :
    (xs ++ zs).Perm (a :: (ys ++ zs)) := by
  exact h.append_right zs

theorem extract_append_right {a : Obj} {xs ys : Heap} (h : xs.Perm (a :: ys)) (zs : Heap) :
    (zs ++ xs).Perm (a :: (zs ++ ys)) := by
  induction zs with
  | nil => exact h
  | cons b zs ih => exact extract_cons ih

theorem prefix_cons {a : Obj} {large xs pre rest : Heap}
    (h : large.Perm (a :: xs)) (p : xs.Perm (pre ++ rest)) :
    large.Perm ((a :: pre) ++ rest) := by
  exact h.trans (p.cons a)

theorem prefix_append {large pre xs next rest : Heap}
    (h : large.Perm (pre ++ xs)) (p : xs.Perm (next ++ rest)) :
    large.Perm ((pre ++ next) ++ rest) := by
  simpa only [List.append_assoc] using h.trans (p.append_left pre)

theorem prefix_exact (xs : Heap) : xs.Perm (xs ++ []) := by
  simp

open Lean Meta Elab Tactic
private meta def emptyHeap : Expr := mkApp (mkConst ``List.nil [.zero]) (mkConst ``Obj)

/-- Unfold list structure, while keeping elements and unknown frames opaque. -/
private meta partial def shape (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let .fvar id := e then
    if let some value := (← id.getDecl).value? then return ← shape value
    return e
  if e.isAppOfArity ``HAppend.hAppend 6 then
    return ← mkAppM ``List.append #[e.getArg! 4, e.getArg! 5]
  if e.isAppOfArity ``List.cons 3 || e.isAppOfArity ``List.append 3 ||
      e.isAppOfArity ``List.nil 1 then return e
  whnfR e

private meta def equal (a b : Expr) : MetaM Bool :=
  withoutModifyingState do
    tryCatchRuntimeEx (isDefEq a b) fun error => do
      if error.isMaxRecDepth then return false
      throw error

/-- Extract one explicit occurrence. An unknown frame supplies no objects. -/
private meta partial def extract (obj heap : Expr) (fuel : Nat) : MetaM (Option (Expr × Expr)) := do
  if fuel == 0 then return none
  let heap ← shape heap
  if heap.isAppOfArity ``List.cons 3 then
    let head := heap.getArg! 1
    let tail := heap.getArg! 2
    if ← equal obj head then
      return some (tail, ← mkAppM ``List.Perm.refl #[heap])
    if let some (rest, proof) ← extract obj tail (fuel - 1) then
      return some (← mkAppM ``List.cons #[head, rest],
        ← mkAppOptM ``extract_cons #[none, some head, none, none, some proof])
  if heap.isAppOfArity ``List.append 3 then
    let left := heap.getArg! 1
    let right := heap.getArg! 2
    if let some (rest, proof) ← extract obj left (fuel - 1) then
      return some (← mkAppM ``List.append #[rest, right],
        ← mkAppM ``extract_append_left #[proof, right])
    if let some (rest, proof) ← extract obj right (fuel - 1) then
      return some (← mkAppM ``List.append #[left, rest],
        ← mkAppM ``extract_append_right #[proof, left])
  return none

/-- Consume every selected occurrence once; retain all other objects. -/
private meta partial def partition (pre heap : Expr) (fuel : Nat) : MetaM (Option (Expr × Expr)) := do
  if fuel == 0 then return none
  if pre == heap then
    return some (emptyHeap, ← mkAppM ``prefix_exact #[heap])
  let pre ← shape pre
  if pre.isAppOfArity ``List.nil 1 then
    return some (heap, ← mkAppM ``List.Perm.refl #[heap])
  if pre.isAppOfArity ``List.cons 3 then
    let obj := pre.getArg! 1
    let tail := pre.getArg! 2
    if let some (next, hp) ← extract obj heap (fuel - 1) then
      if let some (rest, hq) ← partition tail next (fuel - 1) then
        return some (rest, ← mkAppOptM ``prefix_cons #[some obj, some heap,
          some next, some tail, some rest, some hp, some hq])
  if pre.isAppOfArity ``List.append 3 then
    if let some (next, hp) ← partition (pre.getArg! 1) heap (fuel - 1) then
      if let some (rest, hq) ← partition (pre.getArg! 2) next (fuel - 1) then
        return some (rest, ← mkAppOptM ``prefix_append #[some heap, some (pre.getArg! 1),
          some next, some (pre.getArg! 2), some rest, some hp, some hq])
  return none

/-- Infer the remaining frame in a heap permutation from explicit objects. -/
elab "heap_partition_exact" : tactic => withoutRecover do
  let saved ← saveState
  try
    withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      unless target.isAppOfArity ``Exists 2 do
        throwError "heap_partition_exact: expected an existential heap frame"
      let pred := target.getAppArgs[1]!
      let (rest, proof) ← withLocalDeclD `frame (mkConst ``Heap) fun frame => do
        let goal ← instantiateMVars (pred.beta #[frame])
        unless goal.isAppOfArity ``List.Perm 3 do
          throwError "heap_partition_exact: expected a heap permutation"
        let heap := goal.getAppArgs[1]!
        let right ← shape goal.getAppArgs[2]!
        unless right.isAppOfArity ``List.append 3 && right.getArg! 2 == frame do
          throwError "heap_partition_exact: expected prefix ++ frame"
        let pre := right.getArg! 1
        if heap.hasExprMVar || pre.hasExprMVar || pre.containsFVar frame.fvarId! then
          throwError "heap_partition_exact: input heaps must be fixed"
        let some answer ← partition pre heap 256 |
          throwError "heap_partition_exact: selected objects are not explicit in this heap"
        return answer
      let value ← mkAppOptM ``Exists.intro #[some (mkConst ``Heap), some pred, some rest, some proof]
      if value.hasSorry || value.hasExprMVar then throwError "heap_partition_exact: incomplete proof"
      unless ← isDefEq (← inferType value) target do throwError "heap_partition_exact: result does not match the goal"
      (← getMainGoal).assign value
      replaceMainGoal []
  catch error =>
    saved.restore
    throw error


end Lift.Tactic.HeapPartitionExact
