module

public import Lift.Sem.CallArm
public import Lift.Sem.HeapBytesFrame

@[expose] public section

namespace Lift.Sem.CallArm

open Lift.P2.Total CallFrame

/-- A call keeps heap coverage, ownership, and each existing byte-range permission. -/
def ShapeB (h h' : Heap) : Prop :=
  Shape h h' ∧ ∀ policy, h.Permits policy → h'.Permits policy

theorem ShapeB.refl (h : Heap) : ShapeB h h := ⟨.refl h, fun _ hp => hp⟩

theorem ShapeB.trans {h h' h'' : Heap} (h₁ : ShapeB h h') (h₂ : ShapeB h' h'') : ShapeB h h'' :=
  ⟨h₁.1.trans h₂.1, fun policy hp => h₂.2 policy (h₁.2 policy hp)⟩

theorem ShapeB.perm {h h' k k' : Heap} (hs : ShapeB k k')
    (hp : h.Perm k) (hp' : h'.Perm k') : ShapeB h h' :=
  ⟨hs.1.perm hp hp', fun _ hpm =>
    (Heap.Permits_perm hp').mpr (hs.2 _ ((Heap.Permits_perm hp).mp hpm))⟩

/-- A successful byte store preserves the permissions of the input heap. -/
theorem ShapeB.storeB {h₀ h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : ShapeB h₀ h) (hst : h.storeB a w v = .ok h') : ShapeB h₀ h' :=
  hs.trans ⟨⟨Heap.covered_storeB hst, Heap.owned_storeB hst⟩,
    fun _ hp => Heap.Permits_storeB hst hp⟩

/-- The byte-mode call rule carries the callee's permission preservation to its caller. -/
theorem calleeB {X Xl : Type} (heapOf : X → Heap) (setHeap : X → Heap → X) (spOf : Xl → BitVec 64)
    (memOf : Xl → DataMem) {simX : X → Xl → Prop} {simY : X → Xl → UInt64 × Heap → UInt64 × DataMem → Prop}
    {Rh : X → UInt64 × Heap → Prop} {Rl : Xl → UInt64 × DataMem → Prop} (K : Nat)
    (hheap : ∀ x k, heapOf (setHeap x k) = k)
    (h : Refines simX simY Rh Rl)
    (hX : ∀ x xl k, (heapOf x).Perm k → simX x xl → simX (setHeap x k) xl)
    (hY : ∀ x xl y yl k k', (heapOf x).Perm k → y.2.Perm k' → simY (setHeap x k) xl (y.1, k') yl →
      simY x xl y yl)
    (hframe : ∀ x xl y yl, simY x xl y yl → ∀ c, ¬ (heapOf x).Owned c → yl.2.get? c = (memOf xl).get? c)
    (hshape : ∀ x y, Rh x y → ShapeB (heapOf x) y.2) :
    Refines (fun x xl => simX x xl ∧ ∀ i, i < K → ¬ (heapOf x).Owned (spOf xl + BitVec.ofNat 64 i))
      (fun x xl y yl => simY x xl y yl ∧ ShapeB (heapOf x) y.2)
      (fun x y => PermLift (fun k k' => Rh (setHeap x k) (y.1, k')) (heapOf x) y.2)
      (fun xl yl => Rl xl yl ∧ Kept (spOf xl) K (memOf xl) yl.2) := by
  rintro x xl y hx hp
  obtain ⟨yl, hlo, hy, hsh⟩ :=
    callee heapOf setHeap spOf memOf K hheap h hX hY hframe (fun x y hr => (hshape x y hr).1) x xl y hx hp
  obtain ⟨k, k', hr, hs⟩ := hp
  have hshB : ShapeB k k' := by
    have := hshape _ _ hr
    rwa [hheap] at this
  exact ⟨yl, hlo, hy, hshB.perm hs.perm_in hs.perm_out⟩

end Lift.Sem.CallArm
