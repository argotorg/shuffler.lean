module

public import FlatShuffler.Unit.Plan.PlannerRunSafeCtor
import all FlatShuffler.Unit.Plan.PlannerRunSafeCtor
public import FlatShuffler.Unit.ProduceLemmas
import all FlatShuffler.Unit.ProduceLemmas

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open Flat

structure BlockedBounds (n : Word) (st : Flat.St) : Prop where
  size : st.size.toNat ≤ maxStackSize
  offset : st.blockedOffset.toNat < maxStackSize
  excess : st.blockedExcess.toNat ≤ maxStackSize
  current : ∀ i : Word, i.toNat < st.size.toNat →
    get st.dest i = NONE ∨ (get st.dest i).toNat < n.toNat

theorem BlockedBounds.of_dest {st : Flat.St} (hm : st.size.toNat ≤ maxStackSize)
    (hd : DestOk st) (ho : st.blockedOffset.toNat < maxStackSize)
    (he : st.blockedExcess.toNat ≤ maxStackSize) : BlockedBounds st.targetSize st := by
  refine ⟨hm, ho, he, ?_⟩
  intro i hi
  have hnat := hd i.toNat hi
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hnat

theorem block_bounds {st out : Flat.St} {p e : Word}
    (hm : st.size.toNat ≤ maxStackSize) (hd : DestOk st) (hp : p < st.size)
    (he : e.toNat ≤ maxStackSize) (hr : Flat.block st p e = (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  unfold Flat.block at hr
  split at hr
  · cases hr
  · cases hr
    exact BlockedBounds.of_dest (st := { st with blockedOffset := p, blockedExcess := e }) hm hd
      (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hm) he

theorem blockSwap_bounds {st out : Flat.St} {p : Word}
    (hm : st.size.toNat ≤ maxStackSize) (hd : DestOk st) (hp : p < st.size)
    (hu : Flat.isSwapReachable st p = false)
    (hr : Flat.blockSwapUnreachable st p = (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  apply block_bounds hm hd hp ?_ hr
  have hN : maxStackSize = 1024 := rfl
  simp only [Flat.isSwapReachable, Flat.depthOf,
    Flat.maxSwapDepth, BitVec.ofNat_eq_ofNat] at hu
  have hu' : ¬st.size - 1#64 - p ≤ 16#64 := of_decide_eq_false hu
  simp only [Flat.depthOf, Flat.maxSwapDepth, BitVec.ofNat_eq_ofNat]
  bv_omega

theorem blockDup_bounds {st out : Flat.St} {p : Word}
    (hm : st.size.toNat ≤ maxStackSize) (hd : DestOk st) (hp : p < st.size)
    (hu : Flat.isDupReachable st p = false)
    (hr : Flat.blockDupUnreachable st p = (.blocked, out)) :
    BlockedBounds st.targetSize out := by
  apply block_bounds hm hd hp ?_ hr
  have hN : maxStackSize = 1024 := rfl
  simp only [Flat.isDupReachable, Flat.depthOf,
    Flat.maxDupDepth, BitVec.ofNat_eq_ofNat] at hu
  have hu' : ¬st.size - 1#64 - p ≤ 15#64 := of_decide_eq_false hu
  simp only [Flat.depthOf, Flat.maxDupDepth, BitVec.ofNat_eq_ofNat]
  bv_omega

theorem shallowestCopy_lt {st : Flat.St} {slot : StackSlot}
    (hn : Flat.shallowestCopyPosition st slot ≠ NONE) :
    Flat.shallowestCopyPosition st slot < st.size := by
  rcases ProduceProof.copyBelow_lt st slot st.size.toNat st.size rfl with he | he
  · exact False.elim (hn he)
  · exact BitVec.lt_def.mpr he

end FlatShuffler.Unit.PlannerRunU
