module

public import Lift.Sem.CallFrame
public import Lift.Sem.CallMem
public import Lift.Sem.StackPush

@[expose] public section

/-! The callee arm of a caller at L2⁺ with a callee with memory (PIL-CALL4).

The caller's L2⁺ model calls the callee's `l2p.returns` up to one permutation of the heap (`PermLift`, L3-U6a). The
caller's L2 model calls the callee's `l2` restricted to the results that keep the caller's bytes (`Kept`, PIL-CALL). The
callee fact of `Blocks.Returns.sim` (or `simAt`) for this pair is `CallArm.callee`, from:

* the callee's `refines_l2p` (`h`), and the two order facts of `Refines.permLift` (`hX`, `hY`);
* the frame clause of the callee's `SimOut` (`hframe`): each byte that the callee heap does not own is the byte of the
  memory at the call;
* the shape of the callee's L2⁺ result (`hshape`): the heap after the call covers and owns the bytes of the heap before
  it. The `SimOut` of the generated texts does not say it; it is a row of the callee.

The relation of the inputs has one more fact: the callee heap does not own the kept bytes (`free`), so the frame clause
keeps them. The relation of the results has the shape, so that the caller keeps its facts of the heap
(`cont`, `word`). -/

namespace Lift.Sem.CallArm

open Lift.P2.Total CallFrame

/-- The heap `h'` after a call covers and owns the bytes that `h` covers and owns. -/
def Shape (h h' : Heap) : Prop := (∀ c, Covered h' c ↔ Covered h c) ∧ (∀ c, h'.Owned c ↔ h.Owned c)

theorem Shape.refl (h : Heap) : Shape h h := ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem Shape.perm {h h' k k' : Heap} (hs : Shape k k') (hp : h.Perm k) (hp' : h'.Perm k') : Shape h h' :=
  ⟨fun c => (covered_perm hp' c).trans ((hs.1 c).trans (covered_perm hp c).symm),
    fun c => (Heap.owned_perm hp' c).trans ((hs.2 c).trans (Heap.owned_perm hp c).symm)⟩

theorem Shape.trans {h h' h'' : Heap} (h₁ : Shape h h') (h₂ : Shape h' h'') : Shape h h'' :=
  ⟨fun c => (h₂.1 c).trans (h₁.1 c), fun c => (h₂.2 c).trans (h₁.2 c)⟩

/-- A store keeps the covered and the owned bytes. -/
theorem Shape.store {h₀ h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type} (hs : Shape h₀ h)
    (hst : h.store a w v = .ok h') : Shape h₀ h' :=
  hs.trans ⟨Heap.covered_store hst, Heap.owned_store hst⟩

/-! ### The shape row of a callee (PIL-CALL5)

The row `<F>.shape : ∀ a r, l2p.returns a r → Shape a.heap r.2` of a callee with memory. Its proof is
`Blocks.Returns.inv` with the invariant `Shape a.heap x.mem`: each store of a block keeps it
(`Shape.store`). -/

/-- The invariant `I` of the states holds after a step, and `Q` of a result: at the target of a jump,
at the result of a return, and at the continuation of a call for each result `y` of the callee. -/
def Next.Inv {L σ R F : Type} {X Y : F → Type} (I : L → σ → Prop) (Q : R → Prop)
    (callee : ∀ f, X f → Y f → Prop) : Next L σ R F X Y → Prop
  | .goto l x => I l x
  | .ret r => Q r
  | .call f x k => ∀ y, callee f x y → I (k y).1 (k y).2

/-- An invariant of the steps holds at each result. -/
theorem Blocks.Returns.inv {L σ R F : Type} {X Y : F → Type} {b : Blocks L σ R F X Y}
    {callee : ∀ f, X f → Y f → Prop} (I : L → σ → Prop) (Q : R → Prop)
    (block : ∀ l x n, I l x → b.step l x = .ok n → Next.Inv I Q callee n)
    {l : L} {x : σ} {r : R} (h : b.Returns callee l x r) (hx : I l x) : Q r := by
  induction h with
  | ret hstep => exact block _ _ _ hx hstep
  | goto hstep _ ih => exact ih (block _ _ _ hx hstep)
  | call hstep hc _ ih => exact ih (block _ _ _ hx hstep _ hc)

/-- The callee arm. The L2⁺ side is the callee relation up to one permutation of the heap; the L2 side is the callee
restricted to the results that keep the `K` bytes from the `sp` of the call. -/
theorem callee {X Xl : Type} (heapOf : X → Heap) (setHeap : X → Heap → X) (spOf : Xl → BitVec 64)
    (memOf : Xl → DataMem) {simX : X → Xl → Prop} {simY : X → Xl → UInt64 × Heap → UInt64 × DataMem → Prop}
    {Rh : X → UInt64 × Heap → Prop} {Rl : Xl → UInt64 × DataMem → Prop} (K : Nat)
    (hheap : ∀ x k, heapOf (setHeap x k) = k)
    (h : Refines simX simY Rh Rl)
    (hX : ∀ x xl k, (heapOf x).Perm k → simX x xl → simX (setHeap x k) xl)
    (hY : ∀ x xl y yl k k', (heapOf x).Perm k → y.2.Perm k' → simY (setHeap x k) xl (y.1, k') yl →
      simY x xl y yl)
    (hframe : ∀ x xl y yl, simY x xl y yl → ∀ c, ¬ (heapOf x).Owned c → yl.2.get? c = (memOf xl).get? c)
    (hshape : ∀ x y, Rh x y → Shape (heapOf x) y.2) :
    Refines (fun x xl => simX x xl ∧ ∀ i, i < K → ¬ (heapOf x).Owned (spOf xl + BitVec.ofNat 64 i))
      (fun x xl y yl => simY x xl y yl ∧ Shape (heapOf x) y.2)
      (fun x y => PermLift (fun k k' => Rh (setHeap x k) (y.1, k')) (heapOf x) y.2)
      (fun xl yl => Rl xl yl ∧ Kept (spOf xl) K (memOf xl) yl.2) := by
  rintro x xl y ⟨hx, hfree⟩ hp
  obtain ⟨yl, hlo, hy⟩ := Refines.permLift heapOf setHeap Prod.snd (fun y k => (y.1, k)) h hX hY x xl y hx hp
  obtain ⟨k, k', hr, hs⟩ := hp
  have hsh : Shape k k' := by
    have := hshape _ _ hr
    rwa [hheap] at this
  exact ⟨yl, ⟨hlo, fun i hi => hframe x xl y yl hy _ (hfree i hi)⟩, hy,
    hsh.perm hs.perm_in hs.perm_out⟩

/-- The facts of the caller's heap and memory after the call. Before the call: the frame clause of the memory `m` at the
call against the entry memory `m₀` outside the room, the owned bytes of `H` in `H₀`, no object of `H` in the room, and the
room of `m`. The callee keeps each byte that `H` does not own (`hcf`) and has the shape `H → H'`. Then the same facts hold
for `H'` and the memory `m'` after the call. -/
theorem cont {policy : CpuPolicy} {H H₀ H' : Heap} {m₀ m m' : DataMem} {sp : BitVec 64} {n : Nat}
    (hfr : ∀ c, ¬ H₀.Owned c → ¬ SysV.Below sp n c → m.get? c = m₀.get? c) (hown : ∀ c, H.Owned c → H₀.Owned c)
    (hcv : ∀ c, SysV.Below sp n c → ¬ Covered H c) (hroom : SysV.RoomAt policy m sp n) (hn : n < 2 ^ 64)
    (hcf : ∀ c, ¬ H.Owned c → m'.get? c = m.get? c) (hsh : Shape H H') :
    (∀ c, ¬ H₀.Owned c → ¬ SysV.Below sp n c → m'.get? c = m₀.get? c) ∧ (∀ c, H'.Owned c → H₀.Owned c) ∧
      (∀ c, SysV.Below sp n c → ¬ Covered H' c) ∧ SysV.RoomAt policy m' sp n :=
  ⟨fun c hc hb => (hcf c fun ho => hc (hown c ho)).trans (hfr c hc hb),
    fun c ho => hown c ((hsh.2 c).mp ho),
    fun c hb hc => hcv c hb ((hsh.1 c).mp hc),
    hroom.congr hn fun c hb => hcf c fun ho => hcv c hb (covered_of_owned ho)⟩

/-- A word of the room stays after the call. -/
theorem word {policy : CpuPolicy} {H : Heap} {m m' : DataMem} {sp a v : BitVec 64} {n k : Nat}
    (hcv : ∀ c, SysV.Below sp n c → ¬ Covered H c) (hcf : ∀ c, ¬ H.Owned c → m'.get? c = m.get? c)
    (hr : readRam policy m a .W64 = .ok v) (hk8 : 8 ≤ k) (hkn : k ≤ n) (hn : n < 2 ^ 64)
    (ha : a = sp - BitVec.ofNat 64 k) : readRam policy m' a .W64 = .ok v :=
  SysV.readRam_below hr ha hk8 hkn hn fun c hb => hcf c fun ho => hcv c hb (covered_of_owned ho)

/-- The heap `H` does not own the `K` bytes from `sp'`, when they are in the private area of a room of `n` bytes below `sp`
(the room and the return word, `Private` of `Frame.lean`) and no object of the input heap `H₀` covers that area: the
hypothesis of `callee` at a call with `sp' = sp - d`. -/
theorem free {H H₀ : Heap} {sp sp' : BitVec 64} {n d K : Nat}
    (harea : ∀ c, (c - (sp - BitVec.ofNat 64 n)).toNat < n + 8 → ¬ Covered H₀ c) (hown : ∀ c, H.Owned c → H₀.Owned c)
    (hsp : sp' = sp - BitVec.ofNat 64 d) (hdn : d ≤ n) (hK : K ≤ d + 8) (hn : n < 2 ^ 63) :
    ∀ i, i < K → ¬ H.Owned (sp' + BitVec.ofNat 64 i) := by
  intro i hi ho
  subst hsp
  refine harea _ ?_ (covered_of_owned (hown _ ho))
  bv_omega

/-- The private area of a callee with room 0 (its return word at `sp'`) is in the room of the caller, when `sp' = sp - d`
with `8 ≤ d ≤ n`: no object of the current heap covers it. -/
theorem free_callee {H : Heap} {sp sp' : BitVec 64} {n d : Nat}
    (hcv : ∀ c, SysV.Below sp n c → ¬ Covered H c) (hsp : sp' = sp - BitVec.ofNat 64 d)
    (hd : 8 ≤ d) (hdn : d ≤ n) (hn : n < 2 ^ 63) : ∀ c, (c - (sp' - BitVec.ofNat 64 0)).toNat < 0 + 8 → ¬ Covered H c := by
  intro c hc
  subst hsp
  refine hcv _ ?_
  unfold SysV.Below
  bv_omega

end Lift.Sem.CallArm
