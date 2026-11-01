module

public import BbuKraken.Unit.Plan.PlannerRunData
import all BbuKraken.Unit.Plan.PlannerRunData
public import BbuKraken.FlatList.Basic
import all BbuKraken.FlatList.Basic

@[expose] public section

namespace Bbu.Flat

set_option maxRecDepth 4096

@[simp] theorem restoreData_target (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    (restoreData cap old st).target = st.target := by unfold restoreData; rfl
@[simp] theorem restoreData_targetSize (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    (restoreData cap old st).targetSize = st.targetSize := by unfold restoreData; rfl
@[simp] theorem restoreData_spills (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    (restoreData cap old st).spills = st.spills := by unfold restoreData; rfl
@[simp] theorem restoreData_size (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    (restoreData cap old st).size = st.size := by unfold restoreData; rfl
@[simp] theorem restoreData_trace (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    (restoreData cap old st).trace = st.trace := by unfold restoreData; rfl
@[simp] theorem restoreData_dest (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    (restoreData cap old st).dest = st.dest := by unfold restoreData; rfl
@[simp] theorem restoreData_pos (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    (restoreData cap old st).pos = st.pos := by unfold restoreData; rfl
@[simp] theorem restoreData_pend (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    (restoreData cap old st).pend = st.pend := by unfold restoreData; rfl
@[simp] theorem restoreData_blockedOffset (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    (restoreData cap old st).blockedOffset = st.blockedOffset := by unfold restoreData; rfl
@[simp] theorem restoreData_blockedExcess (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) :
    (restoreData cap old st).blockedExcess = st.blockedExcess := by unfold restoreData; rfl

theorem restoreData_get (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (i : Word) (hi : i.toNat < cap) :
    get (restoreData cap old st).data i = get st.data i := by
  unfold get restoreData
  split <;> simp_all

theorem restoreData_put (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (i : Word) (x : StackSlot) (hi : i.toNat < cap) :
    put (restoreData cap old st).data i x =
      (restoreData cap old {st with data := put st.data i x}).data := by
  apply Vector.ext
  intro j hj
  simp only [put, restoreData, Vector.getElem_ofFn, Vector.getElem_setIfInBounds hj]
  split
  · rename_i he
    simp only [← he, hi, ↓reduceIte]
  · rfl

theorem restoreData_bind (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (p d : Word) :
    bind (restoreData cap old st) p d = restoreData cap old (bind st p d) := by unfold restoreData; rfl

theorem restoreData_swapDestinations (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (a b : Word) :
    swapDestinations (restoreData cap old st) a b =
      restoreData cap old (swapDestinations st a b) := by unfold restoreData; rfl

theorem restoreData_stackSwap (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (p : Word)
    (hp : p.toNat < cap) (ht : (st.size - 1#64).toNat < cap) :
    stackSwap (restoreData cap old st) p = restoreData cap old (stackSwap st p) := by
  have hd : put (put (restoreData cap old st).data p
      (get (restoreData cap old st).data (st.size - 1#64))) (st.size - 1#64)
      (get (restoreData cap old st).data p) =
      (restoreData cap old (stackSwap st p)).data := by
    rw [restoreData_get cap old st _ hp, restoreData_get cap old st _ ht,
      restoreData_put cap old st p _ hp,
      restoreData_put cap old {st with data := put st.data p (get st.data (st.size - 1#64))}
        (st.size - 1#64) (get st.data p) ht]
    rfl
  simpa only [stackSwap, restoreData, BitVec.ofNat_eq_ofNat] using congrArg
    (fun (data : Vector StackSlot MAX_N) =>
    {st with data := data, trace := st.trace ++ [Op.swapW (st.size - 1#64 - p)]}) hd

theorem restoreData_stackPush (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (slot : StackSlot) (hs : st.size.toNat < cap) :
    stackPush (restoreData cap old st) slot = restoreData cap old (stackPush st slot) := by
  simp only [stackPush, restoreData_size, restoreData_trace, restoreData_put _ _ _ _ _ hs]
  rfl

theorem restoreData_stackDup (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (p : Word)
    (hs : st.size.toNat < cap) (hp : p.toNat < cap) :
    stackDup (restoreData cap old st) p = restoreData cap old (stackDup st p) := by
  simp only [stackDup, restoreData_size, restoreData_trace]
  rw [restoreData_get _ _ _ _ hp, restoreData_put _ _ _ _ _ hs]
  rfl

theorem restoreData_copyBelow (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (slot : StackSlot) (p : Word) (hp : p.toNat ≤ cap) :
    copyBelow (restoreData cap old st) slot p = copyBelow st slot p := by
  conv => lhs; rw [copyBelow]
  conv => rhs; rw [copyBelow]
  simp only [BitVec.ofNat_eq_ofNat]
  split
  · rfl
  · rename_i h0
    have ht : (p - 1#64).toNat < cap := by bv_omega
    rw [restoreData_get _ _ _ _ ht]
    split
    · rfl
    · exact restoreData_copyBelow cap old st slot (p - 1#64) (by bv_omega)
termination_by p.toNat
decreasing_by bv_omega

theorem restoreData_shallowestCopyPosition (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (slot : StackSlot) (hs : st.size.toNat ≤ cap) :
    shallowestCopyPosition (restoreData cap old st) slot = shallowestCopyPosition st slot :=
  by
    unfold shallowestCopyPosition
    rw [restoreData_size]
    exact restoreData_copyBelow cap old st slot st.size hs

theorem restoreData_swapWith (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (p : Word) (hs : st.size.toNat ≤ cap) :
    swapWith (restoreData cap old st) p =
      let r := swapWith st p; (r.1, restoreData cap old r.2) := by
  simp only [swapWith, restoreData_size, isFinal, restoreData_dest, depthOf,
    BitVec.ofNat_eq_ofNat]
  split
  · rfl
  · rename_i hp
    split
    · simp_all only [↓reduceIte]
    · split
      · simp_all only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      · rw [restoreData_stackSwap cap old st p (by bv_omega) (by bv_omega),
          restoreData_swapDestinations]
        simp_all only [restoreData_size, Bool.false_eq_true, ↓reduceIte]

theorem restoreData_push (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (slot : StackSlot) (d : Word) (hs : st.size.toNat < cap) :
    push (restoreData cap old st) slot d =
      let r := push st slot d; (r.1, restoreData cap old r.2) := by
  simp only [push, restoreData_stackPush _ _ _ _ hs, restoreData_pos]
  split
  · rfl
  · simp only [restoreData_size, restoreData_bind]

theorem restoreData_dup (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (p d : Word)
    (hs : st.size.toNat < cap) (hp : p.toNat < cap) :
    dup (restoreData cap old st) p d =
      let r := dup st p d; (r.1, restoreData cap old r.2) := by
  simp only [dup, restoreData_get _ _ _ _ hp]
  split
  · rfl
  · simp only [restoreData_stackDup _ _ _ _ hs hp, restoreData_pos]
    split
    · rfl
    · simp only [restoreData_size, restoreData_bind]

theorem restoreData_block (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (p e : Word) :
    block (restoreData cap old st) p e =
      let r := block st p e; (r.1, restoreData cap old r.2) := by
  unfold block
  split <;> rfl

theorem restoreData_blockSwapUnreachable (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (p : Word) :
    blockSwapUnreachable (restoreData cap old st) p =
      let r := blockSwapUnreachable st p; (r.1, restoreData cap old r.2) :=
  by
    unfold blockSwapUnreachable depthOf
    rw [restoreData_size]
    exact restoreData_block cap old st p _

theorem restoreData_blockDupUnreachable (cap : Nat) (old : Vector StackSlot MAX_N) (st : St) (p : Word) :
    blockDupUnreachable (restoreData cap old st) p =
      let r := blockDupUnreachable st p; (r.1, restoreData cap old r.2) :=
  by
    unfold blockDupUnreachable depthOf
    rw [restoreData_size]
    exact restoreData_block cap old st p _

end Bbu.Flat
