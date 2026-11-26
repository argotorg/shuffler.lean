module

public import Lift.Sem.HeapSlice
public import Lift.Sem.HeapFrame
public import Lift.Sem.HeapWF
public import Lift.Tactic.HeapField

@[expose] public section

/-! `heap_slice` uses the held-heap rules for exact cells and for a byte
range inside one cell of a fixed-width array. It also proves a byte-range
load from one object, including ranges across typed cells. It requires the
array index and the byte range to be in bounds. It changes no proof limits.

`heap_admit` constructs a policy and a memory for a concrete sample heap.
It requires disjoint objects with nonwrapping addresses (`Heap.WF`). -/

namespace Lift.Tactic

open Lean Meta Elab Tactic

/-- Read the array cell width before applying the rule. Asking unification to
infer a width through bit-vector arithmetic can unfold large modular terms. -/
meta def sliceWidth? (rhs : Expr) : MetaM (Option (TSyntax `term)) := do
  unless rhs.isAppOfArity ``Lift.Sem.Res.ok 2 do return none
  let value := rhs.getArg! 1
  unless value.isAppOfArity ``BitVec.extractLsb' 4 do return none
  let some bits ← getNatValue? (value.getArg! 0) | return none
  match bits with
  | 8 => return some (← `(term| (.W8)))
  | 16 => return some (← `(term| (.W16)))
  | 32 => return some (← `(term| (.W32)))
  | 64 => return some (← `(term| (.W64)))
  | _ => return none

/-- Read a byte range from the result without unfolding heap operations. -/
meta def resultByteRange? (rhs : Expr) : Option (Expr × Expr) := do
  guard (rhs.isAppOfArity ``Lift.Sem.Res.ok 2)
  let value := rhs.getArg! 1
  guard (value.isAppOfArity ``BitVec.ofInt 2)
  let bytes := value.getArg! 1
  guard (bytes.isAppOfArity ``Int.ofBytes 1)
  let take := bytes.getArg! 0
  guard (take.isAppOfArity ``List.take 3)
  let range := take.getArg! 2
  guard (range.isAppOfArity ``List.drop 3)
  return (range.getArg! 2, range.getArg! 1)

/-- Read the object and byte offset from the byte range in the result. -/
meta def objectRange? (rhs : Expr) : Option (Expr × Expr) := do
  let (bytes, offset) ← resultByteRange? rhs
  guard (bytes.isAppOfArity ``Lift.Sem.Obj.bytes 1)
  return (bytes.getArg! 0, offset)

/-- A record-array result selects the bytes of one indexed record. -/
meta def recordRangeIndex? (rhs : Expr) : Option Expr := do
  let (bytes, _) ← resultByteRange? rhs
  guard (bytes.isAppOfArity ``List.flatMap 4)
  guard ((bytes.getArg! 2).isConstOf ``Lift.Sem.Cell.bytes)
  let indexed ← (bytes.getArg! 3).find? (·.isAppOfArity ``GetElem.getElem 8)
  return indexed.getArg! 6

/-- Fix the record size from its typed cells or an explicit encoder-size hypothesis. -/
meta def recordSize? (alpha encode : Expr) : MetaM (Option Expr) :=
  withLocalDeclD `record alpha fun x => do
    let cells := mkApp encode x
    if let some n ← litCellsSize? (← whnfD cells) then return some (mkNatLit n)
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let type ← instantiateMVars d.type
      unless type.isForall do continue
      let body := type.bindingBody!.instantiate1 x
      unless body.isAppOfArity ``Eq 3 do continue
      let lhs := body.getArg! 1
      unless lhs.isAppOfArity ``Lift.Sem.cellsSize 1 && lhs.getArg! 0 == cells do continue
      let rhs := body.getArg! 2
      if (rhs.find? (· == x)).isNone then return some rhs
    return none

/-- A record membership fixes the encoder before the arithmetic rule is applied. -/
meta def tryRecordRange (heap held rhs width : Expr) : TacticM Bool := do
  let some index := recordRangeIndex? rhs | return false
  let some (_, offset) := resultByteRange? rhs | return false
  let isBv := index.isAppOfArity ``BitVec.toNat 2
  let rule ← if index.isAppOfArity ``BitVec.toNat 2 then
    `(term| Lift.Sem.Heap.loadB_records_slice_bv)
    else `(term| Lift.Sem.Heap.loadB_records_slice)
  let index ← Term.exprToSyntax (if isBv then index.getArg! 1 else index)
  let offset ← Term.exprToSyntax offset
  let hh ← Term.exprToSyntax held
  let width ← Term.exprToSyntax width
  let goals ← getGoals
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let type ← instantiateMVars d.type
    unless type.isAppOfArity ``Membership.mem 5 && type.getArg! 3 == heap do continue
    let obj ← whnf (type.getArg! 4)
    unless obj.isAppOfArity ``Lift.Sem.Obj.mk 3 &&
        (obj.getArg! 2).isAppOfArity ``List.flatMap 4 do continue
    let cells := obj.getArg! 2
    let some size ← recordSize? (cells.getArg! 0) (cells.getArg! 2) | continue
    let size ← Term.exprToSyntax size
    let member ← Term.exprToSyntax d.toExpr
    evalTactic (← `(tactic|
      first
      | (focus
           refine $rule (size := $size) (index := $index) (offset := $offset)
             $hh $member ?_ $width ?_ ?_
           all_goals first
             | assumption
             | (intros; rfl)
             | (simp only [Width.bytes]; omega)
           done)
      | skip))
    if (← getGoals) != goals then return true
  return false

syntax (name := heapSlice) "heap_slice" : tactic

@[tactic heapSlice] meta def evalHeapSlice : Tactic := fun _ => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOfArity ``Eq 3 do
    throwError "heap_slice: expected an equality for Heap.loadB"
  let lhs := target.getArg! 1
  unless lhs.isAppOfArity ``Lift.Sem.Heap.loadB 3 do
    throwError "heap_slice: expected an equality for Heap.loadB"
  let heap := lhs.getArg! 0
  let mut held? := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let type ← instantiateMVars d.type
    if type.isAppOfArity ``Lift.Sem.Heap.Holds 3 && type.getArg! 1 == heap then
      held? := some d.toExpr
      break
  let some held := held? | throwError "heap_slice: no Holds hypothesis for this heap"
  let hh ← Term.exprToSyntax held
  if ← tryRecordRange heap held (target.getArg! 2) (lhs.getArg! 2) then return
  if let some (obj, offset) := objectRange? (target.getArg! 2) then
    let obj ← Term.exprToSyntax obj
    let offset ← Term.exprToSyntax offset
    let heap ← Term.exprToSyntax heap
    let width ← Term.exprToSyntax (lhs.getArg! 2)
    evalTactic (← `(tactic|
      (have hmem : $obj ∈ $heap := by
         first
         | assumption
         | (simp only [List.mem_cons, List.mem_append, List.mem_singleton,
             List.mem_nil_iff, or_false, true_or, or_true]; done)
       have hbound : $offset + ($width).bytes ≤ ($obj).size := by
         first
         | assumption
         | (simp only [Lift.Sem.Obj.size, Lift.Sem.Obj.words, List.map_map,
             Function.comp_def, Lift.Sem.sum_map_const, Width.bytes]; omega)
       simpa only [Lift.Sem.Obj.words, Width.bits, Width.bytes,
         BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.ofNat_mul,
         BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc] using
         (Lift.Sem.Heap.loadB_slice $hh hmem $width hbound))))
    return
  match ← sliceWidth? (target.getArg! 2) with
  | some wide =>
    let source := ((target.getArg! 2).getArg! 1).getArg! 3
    let bvIndex := source.isAppOfArity ``GetElem.getElem 8 &&
      (source.getArg! 6).isAppOfArity ``BitVec.toNat 2
    let rule ← if bvIndex then `(term| Lift.Sem.Heap.loadB_words_slice_bv)
      else `(term| Lift.Sem.Heap.loadB_words_slice)
    let solve ← `(tactic|
      all_goals first
        | assumption
        | (simp only [List.mem_cons, List.mem_append, List.mem_singleton,
            List.mem_nil_iff, or_false, true_or, or_true]; done)
        | (simp only [Width.bytes]; omega))
    evalTactic (← `(tactic|
      first
      | (apply ($rule (wide := $wide) (writable := false) $hh)
         $solve:tactic
         done)
      | (apply ($rule (wide := $wide) (writable := true) $hh)
         $solve:tactic
         done)))
  | none =>
    evalTactic (← `(tactic|
      (apply (Lift.Sem.Heap.loadB_of_found $hh)
       try simp only [Lift.Sem.Obj.words, List.map_cons, List.map_nil]
       heap_found
       done)))

syntax "heap_admit" : tactic
macro_rules
  | `(tactic| heap_admit) => `(tactic| (apply Lift.Sem.Heap.WF.holds; decide))

end Lift.Tactic
