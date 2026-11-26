module

public import Lift.Tactic.HeapSlice
public import Lift.Sem.HeapFrame

@[expose] public section

/-! Typed heap operations with explicit, unchanged list frames. The tactic only
closes a goal when all checks succeed. `heap_call rule` applies a supplied
checked rule and leaves preconditions that the heap rules cannot prove. -/

namespace Lift.Tactic
open Lean Meta Elab Tactic

meta initialize registerTraceClass `heap_frame

private structure HeapFocus where
  pre : Expr
  obj : Expr
  post : Expr

private meta def emptyHeap : Expr := mkApp (mkConst ``List.nil [.zero]) (mkConst ``Lift.Sem.Obj)

private meta def appendHeap (a b : Expr) : MetaM Expr := do
  if a.isAppOfArity ``List.nil 1 then return b
  if b.isAppOfArity ``List.nil 1 then return a
  mkAppM ``List.append #[a, b]

/-- Expose only local aliases of a list. Keep append and computed elements
intact so that an unknown frame does not unfold to a stuck matcher. -/
private meta partial def heapAlias (heap : Expr) : MetaM Expr := do
  let heap ← instantiateMVars heap
  if let .fvar id := heap then
    if let some value := (← id.getDecl).value? then return ← heapAlias value
  return heap

/-- Enumerate explicit objects through cons and append. An opaque list remains
an opaque frame. Do not inspect its elements or assume that it is empty. -/
private meta partial def heapFocuses (heap : Expr) : MetaM (Array HeapFocus) := do
  let heap ← heapAlias heap
  -- A mapped list can contain large encoded arrays. It is a frame until the
  -- caller exposes its list constructors or supplies object membership.
  if heap.isAppOfArity ``List.map 4 || heap.isAppOfArity ``List.flatMap 4 then return #[]
  let heap ← if heap.isAppOfArity ``HAppend.hAppend 6 then
      appendHeap (heap.getArg! 4) (heap.getArg! 5)
    else if heap.isAppOfArity ``List.append 3 || heap.isAppOfArity ``List.cons 3 then pure heap
    else whnfR heap
  if heap.isAppOfArity ``List.cons 3 then
    let o := heap.getArg! 1
    let tail := heap.getArg! 2
    let later ← (← heapFocuses tail).mapM fun f => do
      return { f with pre := ← mkAppM ``List.cons #[o, f.pre] }
    return #[{ pre := emptyHeap, obj := o, post := tail }] ++ later
  if heap.isAppOfArity ``List.append 3 then
    let left := heap.getArg! 1
    let right := heap.getArg! 2
    let before ← (← heapFocuses left).mapM fun f => do
      return { f with post := ← appendHeap f.post right }
    let after ← (← heapFocuses right).mapM fun f => do
      return { f with pre := ← appendHeap left f.pre }
    return before ++ after
  return #[]

private meta def tryHeapTactic (t : TSyntax `tactic) : TacticM Bool := do
  let state ← saveState
  try
    let goal ← getMainGoal
    focusAndDone (withoutRecover (evalTactic t))
    let proof ← instantiateMVars (mkMVar goal)
    if proof.hasSorry || proof.hasExprMVar then
      throwError "heap_frame: the rule did not produce a complete proof"
    return true
  catch error =>
    trace[heap_frame] "{error.toMessageData}"
    for goal in ← getGoals do
      trace[heap_frame] "{MessageData.ofGoal goal}"
    state.restore
    return false

/-- Parse list constructors without unfolding an append with an unknown left side. -/
private meta def listShape (e : Expr) : MetaM Expr := do
  let e ← heapAlias e
  if e.isAppOfArity ``HAppend.hAppend 6 then
    mkAppM ``List.append #[e.getArg! 4, e.getArg! 5]
  else if e.isAppOfArity ``List.append 3 || e.isAppOfArity ``List.cons 3 ||
      e.isAppOfArity ``List.nil 1 then pure e
  else whnfR e

/-- Prove an ordered sublist relation. Each occurrence is consumed once. -/
private meta partial def subheapProof (small large : Expr) (fuel : Nat := 64) : MetaM (Option Expr) := do
  if fuel == 0 || small.hasExprMVar || large.hasExprMVar then return none
  if ← withoutModifyingState (isDefEq small large) then
    return some (← mkAppM ``List.Sublist.refl #[small])
  let small ← listShape small
  let large ← listShape large
  if small.isAppOfArity ``List.nil 1 then
    return some (← mkAppM ``List.nil_sublist #[large])
  if large.isAppOfArity ``List.cons 3 then
    let head := large.getArg! 1
    let tail := large.getArg! 2
    if small.isAppOfArity ``List.cons 3 then
      if ← withoutModifyingState (isDefEq (small.getArg! 1) head) then
        if let some pf ← subheapProof (small.getArg! 2) tail (fuel - 1) then
          return some (← mkAppM ``List.Sublist.cons_cons #[head, pf])
        -- Consume the first equal occurrence; skipping it repeats the same search.
        return none
    if let some pf ← subheapProof small tail (fuel - 1) then
      return some (← mkAppM ``List.Sublist.cons #[head, pf])
  if large.isAppOfArity ``List.append 3 then
    let left := large.getArg! 1
    let right := large.getArg! 2
    if small.isAppOfArity ``List.append 3 then
      if let some lp ← subheapProof (small.getArg! 1) left (fuel - 1) then
        if let some rp ← subheapProof (small.getArg! 2) right (fuel - 1) then
          return some (← mkAppM ``List.Sublist.append #[lp, rp])
    if let some pf ← subheapProof small left (fuel - 1) then
      return some (← mkAppM ``List.Sublist.trans #[pf,
        ← mkAppM ``List.sublist_append_left #[left, right]])
    if let some pf ← subheapProof small right (fuel - 1) then
      return some (← mkAppM ``List.Sublist.trans #[pf,
        ← mkAppM ``List.sublist_append_right #[left, right]])
  return none

private meta def tryObjectTactic (hh obj heap : TSyntax `term)
    (body : TSyntax `tactic) : TacticM Bool := do
  tryHeapTactic (← `(tactic|
    (have hobj : $obj ∈ $heap := by
       first | assumption | simp only [List.mem_append, List.mem_cons, List.mem_singleton,
         List.mem_nil_iff, or_false, true_or, or_true]
     have hsize := Lift.Sem.Heap.Holds.noWrap $hh $obj hobj
     first
     | (simp -failIfUnchanged only [Lift.Sem.Obj.words,
          Lift.Sem.Obj.size_eq_cellsSize, Lift.Sem.cellsSize] at hsize
        rw [Lift.Sem.words_bytes] at hsize)
     | skip
     simp -failIfUnchanged only [Lift.Sem.Obj.words, Lift.Sem.Obj.size_eq_cellsSize, heap_field,
       Nat.reduceMul, Nat.reduceAdd, Nat.reducePow] at hsize
     $body)))

syntax (name := heapFrame) "heap_frame" : tactic

@[tactic heapFrame] meta def evalHeapFrame : Tactic := fun _ => focus <| withoutRecover do
  trace[heap_frame] "normalize list frames"
  evalTactic (← `(tactic| simp -failIfUnchanged only
    [List.append_eq, List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at *))
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| simp -failIfUnchanged only
    [BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
  if (← getGoals).isEmpty then return
  withMainContext do
    trace[heap_frame] "inspect the target"
    if ← tryHeapTactic (← `(tactic| (with_reducible assumption; done))) then return
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.isAppOfArity ``Lift.Sem.Heap.Holds 3 then
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        unless ty.isAppOfArity ``Lift.Sem.Heap.Holds 3 do continue
        unless ← withoutModifyingState (isDefEq (ty.getArg! 0) (target.getArg! 0)) do continue
        if ← withoutModifyingState (isDefEq (ty.getArg! 2) (target.getArg! 2)) then
          if let some sub ← subheapProof (target.getArg! 1) (ty.getArg! 1) then
            let pf ← mkAppM ``Lift.Sem.Heap.Holds.sublist #[d.toExpr, sub]
            (← getMainGoal).assign pf
            replaceMainGoal []
            return
        let hh ← Term.exprToSyntax d.toExpr
        if ← tryHeapTactic (← `(tactic|
            (apply Lift.Sem.Heap.Holds.reassemble $hh; all_goals assumption; done))) then return
        if ← tryHeapTactic (← `(tactic|
            (apply Lift.Sem.Heap.Holds.reassemble_of_frame $hh; all_goals assumption; done))) then return
      throwError "heap_frame: no held subheap or checked frame-preservation rule matches"
    let some (_, lhs, _) := target.eq? |
      throwError "heap_frame: expected a heap operation equality or a held frame"
    let op := lhs.getAppFn.constName?
    unless op == some ``Lift.Sem.Heap.load || op == some ``Lift.Sem.Heap.loadB ||
        op == some ``Lift.Sem.Heap.store || op == some ``Lift.Sem.Heap.storeB do
      throwError "heap_frame: expected Heap.load, Heap.loadB, Heap.store, or Heap.storeB"
    let heap := lhs.getArg! 0
    trace[heap_frame] "find explicit objects"
    -- Prove the operation on arbitrary words. Reducing a computed encoding
    -- during field matching can evaluate a whole vector or list range.
    for f in ← heapFocuses heap do
      if f.obj.isAppOfArity ``Lift.Sem.Obj.words 4 then
        let words := (f.obj.getArg! 3).consumeMData
        -- Explicit lists retain the scalar values needed by loads. Abstract
        -- computed encodings without hiding the contents of literal fields.
        unless words.isFVar || words.isAppOfArity ``List.cons 3 ||
            words.isAppOfArity ``List.nil 1 do
          trace[heap_frame] "abstract a computed word array"
          let words ← Term.exprToSyntax words
          if ← tryHeapTactic (← `(tactic|
              (generalize hwords : $words = heapWords at *
               have hlength := congrArg List.length hwords
               simp -failIfUnchanged only [List.length_map, List.length_range,
                 List.length_set, Vector.length_toList, Array.length_toList] at hlength
               clear hwords
               heap_frame))) then return
    let heapTerm ← Term.exprToSyntax (← heapAlias heap)
    let address ← Term.exprToSyntax (lhs.getArg! 1)
    let width ← Term.exprToSyntax (lhs.getArg! 2)
    let field ← `(tactic|
      (simp -failIfUnchanged only [Lift.Sem.Obj.words, List.map_eq_flatMap]
       all_goals field_eval
       all_goals
         simp -failIfUnchanged (disch := field_disch) only
           [BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.mul_one]
         all_goals field_eval))
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ty.isAppOfArity ``Lift.Sem.Heap.Holds 3 do continue
      trace[heap_frame] "match a held heap"
      unless ← withoutModifyingState (isDefEq (ty.getArg! 1) heap) do continue
      let hh ← Term.exprToSyntax d.toExpr
      let policy ← Term.exprToSyntax (ty.getArg! 0)
      let memory ← Term.exprToSyntax (ty.getArg! 2)
      let explicit ← heapFocuses heap
      let context ← getLCtx
      let fromMembership := if op == some ``Lift.Sem.Heap.load || op == some ``Lift.Sem.Heap.loadB then
        context.foldl (init := #[]) fun objects decl =>
          if decl.type.isAppOfArity ``Membership.mem 5 then
            if decl.type.getArg! 3 == heap then
              objects.push { pre := emptyHeap, obj := decl.type.getArg! 4, post := emptyHeap }
            else objects
          else objects
        else #[]
      for f in explicit ++ fromMembership do
        let pre ← Term.exprToSyntax f.pre
        let obj ← Term.exprToSyntax f.obj
        let post ← Term.exprToSyntax f.post
        if op == some ``Lift.Sem.Heap.load || op == some ``Lift.Sem.Heap.loadB then
          let rule := if op == some ``Lift.Sem.Heap.load then
            mkIdent ``Lift.Sem.Heap.load_of_found else mkIdent ``Lift.Sem.Heap.loadB_of_found
          if ← tryObjectTactic hh obj heapTerm (← `(tactic|
              (apply ($rule (h := $heapTerm) $hh)
               apply Lift.Sem.Heap.Found.of_mem (o := $obj)
               · first | assumption | simp only [List.mem_append, List.mem_cons, List.mem_singleton,
                   List.mem_nil_iff, or_false, true_or, or_true]
               · first | assumption | ($field:tactic)
               done))) then return
          if op == some ``Lift.Sem.Heap.loadB then
            if ← tryObjectTactic hh obj heapTerm (← `(tactic|
                (have hobj : $obj ∈ $heapTerm := by
                   simp only [List.mem_append, List.mem_cons, List.mem_singleton,
                     List.mem_nil_iff, or_false, true_or, or_true]
                 heap_slice
                 done))) then return
        else
          let value ← Term.exprToSyntax (lhs.getArg! 3)
          let focusedHolds ← `(term|
            (show Lift.Sem.Heap.Holds $policy ($pre ++ $obj :: $post) $memory from by
              simpa only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append,
                List.append_nil] using $hh))
          let rule := if op == some ``Lift.Sem.Heap.store then
            mkIdent ``Lift.Sem.Heap.store_of_storeAt else mkIdent ``Lift.Sem.Heap.storeB_of_storeAt
          if ← tryObjectTactic hh obj heapTerm (← `(tactic|
              (have hs : Lift.Sem.Heap.StoreAt $address $width $value
                  ($obj :: $post) (Lift.Sem.Obj.setAt $address $width $value $obj :: $post) := by
                  apply Lift.Sem.Heap.StoreAt.head
                  · first | assumption | rfl
                  · first | assumption | ($field:tactic)
               have hstep := $rule $focusedHolds (hs.append_prefix $pre)
               simp -failIfUnchanged only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append,
                 List.append_nil] at hstep
               apply Eq.trans hstep
               all_goals ($field:tactic)
               done))) then return
          if op == some ``Lift.Sem.Heap.storeB then
            let rhs := target.getArg! 2
            if rhs.isAppOfArity ``Lift.Sem.Res.ok 2 then
              for out in ← heapFocuses (rhs.getArg! 1) do
                unless ← withoutModifyingState (isDefEq f.pre out.pre) do continue
                unless ← withoutModifyingState (isDefEq f.post out.post) do continue
                let cells ← Term.exprToSyntax (← mkAppM ``Lift.Sem.Obj.cells #[out.obj])
                if ← tryObjectTactic hh obj heapTerm (← `(tactic|
                    (have hstep := Lift.Sem.Heap.storeB_span_at_append
                      (pre := $pre) (post := $post) (o := $obj) (cs := $cells) $focusedHolds
                      (a := $address) (w := $width) (v := $value)
                      (by first | assumption | rfl) (by first | assumption | field_eval)
                      (by first | assumption | field_eval)
                     simpa only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append,
                       List.append_nil] using hstep))) then return
            if ← tryObjectTactic hh obj heapTerm (← `(tactic|
                (have hobj : $obj ∈ $heapTerm := by
                   simp only [List.mem_append, List.mem_cons, List.mem_singleton,
                     List.mem_nil_iff, or_false, true_or, or_true]
                 have hsize := Lift.Sem.Heap.Holds.noWrap $hh $obj hobj
                 have hspan : Lift.Sem.Obj.Spans $obj $address $width :=
                   (Lift.Sem.Obj.spans_of_offset
                     (Lift.Sem.add_toNat_sub (Lift.Sem.Obj.addr $obj) $address).symm
                     (by
                       simp only [Lift.Sem.Obj.size_eq_cellsSize]
                       simp only [bvOffToNat, heap_field, Nat.reduceMul, Nat.reduceAdd]
                       all_goals omega) hsize).1
                 have hstep := Lift.Sem.Heap.storeB_bytes_at_append $focusedHolds
                   (a := $address) (w := $width) (v := $value)
                   (by first | assumption | rfl) (by first | assumption | field_eval) hspan
                 simp -failIfUnchanged only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append,
                   List.append_nil] at hstep
                 apply Eq.trans hstep
                 all_goals first | rfl | (field_eval; done)
                 done))) then return
    if op == some ``Lift.Sem.Heap.loadB then
      if ← tryHeapTactic (← `(tactic| (heap_slice; done))) then return
    throwError "heap_frame: no held object proves this operation and result; check the address, bounds, width, and write permission"

syntax (name := heapCall) "heap_call " term : tactic

@[tactic heapCall] meta def evalHeapCall : Tactic := fun stx => focus <| withoutRecover do
  let rule : TSyntax `term := ⟨stx[1]⟩
  evalTactic (← `(tactic| apply $rule))
  evalTactic (← `(tactic| all_goals try first | heap_frame | assumption | (field_disch; done)))

end Lift.Tactic
