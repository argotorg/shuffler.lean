module

public import Lift.Sem.Heap
public meta import Lift.Meta.MatchCache

@[expose] public section

namespace Lift.Sem

/-- The bytes of the object in order; each cell gives its bytes in little-endian order. -/
def Obj.bytes (o : Obj) : List UInt8 :=
  o.cells.flatMap fun c => Int.toBytes c.w.bytes c.v.toInt

/-- The bytes `[a, a + w)` are bytes of the object. -/
def Obj.Spans (o : Obj) (a : BitVec 64) (w : Width) : Prop :=
  o.addr.toNat ≤ a.toNat ∧ a.toNat + w.bytes ≤ o.addr.toNat + o.size

instance (o : Obj) (a : BitVec 64) (w : Width) : Decidable (o.Spans a w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The value of the access of width `w` at `a` in the bytes of the object, if the object spans
the access. -/
def Obj.loadBytes (o : Obj) (a : BitVec 64) (w : Width) : Option w.type :=
  if o.Spans a w then
    some (BitVec.ofInt w.bits (Int.ofBytes ((o.bytes.drop (a.toNat - o.addr.toNat)).take w.bytes)))
  else none

/-- The cells of `cs` with the value of each cell read from its bytes in `bs`, in order. -/
def cellsOfBytes (bs : List UInt8) : List Cell → List Cell
  | [] => []
  | c :: cs =>
    ⟨c.w, BitVec.ofInt c.w.bits (Int.ofBytes (bs.take c.w.bytes))⟩ ::
      cellsOfBytes (bs.drop c.w.bytes) cs

/-- The object after a store of `v` in the bytes `[a, a + w)` of the object: the cells keep their
widths and take the new bytes. A writable object that does not span the access does not change. -/
def Obj.setBytes (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) : Obj :=
  if o.writable ∧ o.Spans a w then
    let off := a.toNat - o.addr.toNat
    let bs := o.bytes.take off ++ Int.toBytes w.bytes v.toInt ++ o.bytes.drop (off + w.bytes)
    { o with cells := cellsOfBytes bs o.cells }
  else o

/-- A load: the result of `load` when it is `.ok`; else the value of the bytes `[a, a + w)` of
the first object that spans the access. -/
def Heap.loadB (h : Heap) (a : BitVec 64) (w : Width) : Res w.type :=
  match h.load a w with
  | .ok v => .ok v
  | _ => match h.findSome? fun o => o.loadBytes a w with
    | some v => .ok v
    | none => .stuck "load: no cell of this width at this address"

/-- A store: the result of `store` when some object has a cell of width `w` at `a`; else a
writable object that spans the access takes the new bytes, and a read-only object that spans it is
stuck. -/
def Heap.storeB (h : Heap) (a : BitVec 64) (w : Width) (v : w.type) : Res Heap :=
  if h.any fun o => (o.get a w).isSome then h.store a w v
  else if h.any fun o => o.writable && decide (o.Spans a w) then
    .ok (h.map (Obj.setBytes a w v))
  else if h.any fun o => decide (o.Spans a w) then .stuck "store: the object is not writable"
  else .stuck "store: no cell of this width at this address"

/-- A load that gives `v` gives `v` in `loadB`. -/
theorem Heap.loadB_of_load {h : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hl : h.load a w = .ok v) : h.loadB a w = .ok v := by
  unfold Heap.loadB
  rw [hl]

/-- A store that gives `h'` gives `h'` in `storeB`. -/
theorem Heap.storeB_of_store {h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.store a w v = .ok h') : h.storeB a w v = .ok h' := by
  have hc : h.any (fun o => (o.get a w).isSome) = true := by
    unfold Heap.store at hs
    split at hs
    · rename_i hc0
      obtain ⟨O, hO, hO'⟩ := List.any_eq_true.mp hc0
      exact List.any_eq_true.mpr ⟨O, hO, by simp only [Bool.and_eq_true] at hO'; exact hO'.2⟩
    · split at hs <;> cases hs
  unfold Heap.storeB
  simp only [hc, ↓reduceIte]
  exact hs

end Lift.Sem

#realize_match_congruences
