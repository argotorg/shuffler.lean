module

public import Lift.Sem.HeapBytes

@[expose] public section

/-! Compiled code of `Heap.load`, `Heap.store`, `Heap.loadB` and `Heap.storeB`.

Each `@[csimp]` lemma below states that an old function is equal to a new one. The kernel and the
proofs keep the old definitions; only the compiled code of a definition that is compiled after an
import of this module calls the new function.

The old `Obj.get` builds the list `offsets 0 o.cells` and, for each cell, computes
`o.addr + BitVec.ofNat 64 off` on `Nat`: `BitVec.ofNat` and `BitVec.add` each compute `2 ^ 64`, a
`Nat` above the scalar range, and divide by it. The new `getAt` walks the cells with the address of
each cell as a `UInt64`, without a list of offsets; a `UInt64` addition wraps around `2 ^ 64` as
`BitVec.add` does. -/

namespace Lift.Sem

open Lift.P2.Total

/-! ### Addresses as `UInt64` -/

/-- `Width.bytes` as a `UInt64`. -/
def bytes64 : Width → UInt64
  | .W8 => 1
  | .W16 => 2
  | .W32 => 4
  | .W64 => 8

theorem bytes64_eq (w : Width) : bytes64 w = UInt64.ofNat w.bytes := by cases w <;> rfl

theorem addr64_step (b : BitVec 64) (n k : Nat) :
    UInt64.ofBitVec (b + BitVec.ofNat 64 n) + UInt64.ofNat k =
      UInt64.ofBitVec (b + BitVec.ofNat 64 (n + k)) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  rfl

theorem ofBitVec_eq_iff (x y : BitVec 64) : UInt64.ofBitVec x = UInt64.ofBitVec y ↔ x = y :=
  ⟨fun h => congrArg UInt64.toBitVec h, fun h => h ▸ rfl⟩

theorem addr64_zero (b : BitVec 64) : UInt64.ofBitVec (b + BitVec.ofNat 64 0) = UInt64.ofBitVec b :=
  by rw [BitVec.add_zero]

theorem ite_of_iff {p q : Prop} [Decidable p] [Decidable q] (e : p ↔ q) {α : Type} (x y : α) :
    (if p then x else y) = if q then x else y := by
  by_cases hp : p
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h, ite_eq_left_iff.mpr fun h => absurd (e.mp hp) h]
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp,
      ite_eq_right_iff.mpr fun h => absurd (e.mpr h) hp]

/-! ### Load -/

/-- The value of the first cell of width `w` at the address `a`; the first cell is at `p`. -/
def getAt (w : Width) (a : UInt64) : UInt64 → List Cell → Option w.type
  | _, [] => none
  | p, c :: cs =>
    match (if p = a then c.get w else none) with
    | some v => some v
    | none => getAt w a (p + bytes64 c.w) cs

theorem getAt_eq (w : Width) (b a : BitVec 64) (n : Nat) (cs : List Cell) :
    getAt w (UInt64.ofBitVec a) (UInt64.ofBitVec (b + BitVec.ofNat 64 n)) cs =
      (offsets n cs).findSome? fun x =>
        if b + BitVec.ofNat 64 x.1 = a then x.2.get w else none := by
  induction cs generalizing n with
  | nil => rfl
  | cons c cs ih =>
    simp only [getAt, offsets, List.findSome?_cons, bytes64_eq, addr64_step, ih,
      ite_of_iff (ofBitVec_eq_iff _ a)]
    generalize (if b + BitVec.ofNat 64 n = a then c.get w else none) = r
    cases r <;> rfl

def Obj.getFast (o : Obj) (a : BitVec 64) (w : Width) : Option w.type :=
  getAt w (UInt64.ofBitVec a) (UInt64.ofBitVec o.addr) o.cells

theorem Obj.get_eq_getFast : @Obj.get = @Obj.getFast := by
  funext o a w
  have := getAt_eq w o.addr a 0 o.cells
  rw [addr64_zero] at this
  exact this.symm

def Heap.loadFast (h : Heap) (a : BitVec 64) (w : Width) : Res w.type :=
  match h.findSome? fun o => o.getFast a w with
  | some v => .ok v
  | none => .stuck "load: no cell of this width at this address"

@[csimp] theorem Heap.load_eq_loadFast : @Heap.load = @Heap.loadFast := by
  funext h a w
  simp only [Heap.load, Heap.loadFast, Obj.get_eq_getFast]
  generalize List.findSome? (fun o => o.getFast a w) h = r
  cases r <;> rfl

/-! ### Store -/

/-- The cells (the first at `p`) with the value `v` in each cell of width `w` at the address
`a`. -/
def setAt (a : UInt64) (w : Width) (v : w.type) : UInt64 → List Cell → List Cell
  | _, [] => []
  | p, c :: cs => (if p = a ∧ c.w = w then ⟨w, v⟩ else c) :: setAt a w v (p + bytes64 c.w) cs

theorem setCells_eq_setAt (base a : BitVec 64) (w : Width) (v : w.type) (n : Nat)
    (cs : List Cell) :
    setCells base a w v n cs =
      setAt (UInt64.ofBitVec a) w v (UInt64.ofBitVec (base + BitVec.ofNat 64 n)) cs := by
  induction cs generalizing n with
  | nil => rfl
  | cons c cs ih =>
    simp only [setCells, setAt, ih, bytes64_eq, addr64_step,
      ite_of_iff (and_congr_left' (ofBitVec_eq_iff _ a))]

/-- A cell list in which no cell has the width `w` and the address `a` does not change. -/
theorem setAt_of_getAt_none {w : Width} {v : w.type} {a : UInt64} :
    ∀ {p : UInt64} {cs : List Cell}, getAt w a p cs = none → setAt a w v p cs = cs
  | _, [], _ => rfl
  | p, c :: cs, h => by
    have hr : getAt w a (p + bytes64 c.w) cs = none := by
      cases hx : (if p = a then c.get w else none) with
      | some _ => simp only [getAt, hx] at h; cases h
      | none => simp only [getAt, hx] at h; exact h
    have hc : ¬ (p = a ∧ c.w = w) := by
      rintro ⟨hp, hw⟩
      have hg : c.get w = some (hw ▸ c.v) := by unfold Cell.get; simp only [hw, ↓reduceDIte]
      simp only [getAt, hp, ↓reduceIte, hg] at h
      cases h
    simp only [setAt, hc, ↓reduceIte, setAt_of_getAt_none hr]

/-- `setAt`, which keeps the list `cs` after the changed cell when no cell in it changes. -/
def setAtS (a : UInt64) (w : Width) (v : w.type) : UInt64 → List Cell → List Cell
  | _, [] => []
  | p, c :: cs =>
    if p = a ∧ c.w = w then
      ⟨w, v⟩ :: if (getAt w a (p + bytes64 c.w) cs).isSome then setAtS a w v (p + bytes64 c.w) cs
        else cs
    else c :: setAtS a w v (p + bytes64 c.w) cs

theorem setAtS_eq (a : UInt64) (w : Width) (v : w.type) :
    ∀ (p : UInt64) (cs : List Cell), setAtS a w v p cs = setAt a w v p cs
  | _, [] => rfl
  | p, c :: cs => by
    by_cases hc : p = a ∧ c.w = w
    · simp only [setAtS, setAt, hc, and_self, ↓reduceIte]
      split
      · rw [setAtS_eq]
      · rw [setAt_of_getAt_none (Option.not_isSome_iff_eq_none.mp ‹_›)]
    · simp only [setAtS, setAt, hc, ↓reduceIte, setAtS_eq]

/-- `Obj.set`, which gives `o` itself when no cell of `o` changes. -/
def Obj.setFast (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) : Obj :=
  if o.writable && (o.getFast a w).isSome then
    { o with cells := setAtS (UInt64.ofBitVec a) w v (UInt64.ofBitVec o.addr) o.cells }
  else o

theorem Obj.set_eq_setFast : @Obj.set = @Obj.setFast := by
  funext a w v o
  obtain ⟨b, wr, cs⟩ := o
  have e := setCells_eq_setAt b a w v 0 cs
  rw [addr64_zero] at e
  cases wr
  · rfl
  · unfold Obj.set Obj.setFast Obj.getFast
    simp only [Bool.true_and, ↓reduceIte, e]
    cases hg : getAt w (UInt64.ofBitVec a) (UInt64.ofBitVec b) cs with
    | none => simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, setAt_of_getAt_none hg]
    | some _ => simp only [Option.isSome_some, ↓reduceIte, setAtS_eq]

def Heap.storeFast (h : Heap) (a : BitVec 64) (w : Width) (v : w.type) : Res Heap :=
  if h.any fun o => o.writable && (o.getFast a w).isSome then .ok (h.map (Obj.setFast a w v))
  else if h.any fun o => (o.getFast a w).isSome then .stuck "store: the object is not writable"
  else .stuck "store: no cell of this width at this address"

@[csimp] theorem Heap.store_eq_storeFast : @Heap.store = @Heap.storeFast := by
  funext h a w v
  simp only [Heap.store, Heap.storeFast, Obj.get_eq_getFast, Obj.set_eq_setFast]

/-! ### Byte load -/

/-- `n` plus the number of bytes of the cells. -/
def sizeAcc : Nat → List Cell → Nat
  | n, [] => n
  | n, c :: cs => sizeAcc (n + c.w.bytes) cs

theorem sizeAcc_eq (n : Nat) (cs : List Cell) :
    sizeAcc n cs = n + (cs.map fun c => c.w.bytes).sum := by
  induction cs generalizing n with
  | nil => simp [sizeAcc]
  | cons c cs ih => simp only [sizeAcc, ih, List.map_cons, List.sum_cons]; omega

def Obj.sizeFast (o : Obj) : Nat := sizeAcc 0 o.cells

theorem Obj.size_eq_sizeFast (o : Obj) : o.size = o.sizeFast := by
  simp [Obj.size, Obj.sizeFast, sizeAcc_eq]

/-- `Obj.Spans`, with `Obj.sizeFast`. -/
def Obj.spansFast (o : Obj) (a : BitVec 64) (w : Width) : Bool :=
  decide (o.addr.toNat ≤ a.toNat ∧ a.toNat + w.bytes ≤ o.addr.toNat + o.sizeFast)

theorem Obj.spans_iff (o : Obj) (a : BitVec 64) (w : Width) :
    o.Spans a w ↔ o.spansFast a w = true := by
  simp only [Obj.Spans, Obj.spansFast, Obj.size_eq_sizeFast, decide_eq_true_eq]

theorem Obj.decide_spans (o : Obj) (a : BitVec 64) (w : Width) :
    decide (o.Spans a w) = o.spansFast a w := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact o.spans_iff a w

/-- The bytes of a cell. -/
def cellBytes (c : Cell) : List UInt8 := Int.toBytes c.w.bytes c.v.toInt

/-- The `n` bytes of the cells from byte `k` on. -/
def sliceBytes : Nat → Nat → List Cell → List UInt8
  | _, _, [] => []
  | k, n, c :: cs =>
    if n = 0 then []
    else if c.w.bytes ≤ k then sliceBytes (k - c.w.bytes) n cs
    else
      let bs := ((cellBytes c).drop k).take n
      bs ++ sliceBytes 0 (n - bs.length) cs

theorem sliceBytes_eq (k n : Nat) (cs : List Cell) :
    sliceBytes k n cs = ((cs.flatMap cellBytes).drop k).take n := by
  induction cs generalizing k n with
  | nil => simp [sliceBytes]
  | cons c cs ih =>
    have hl : (cellBytes c).length = c.w.bytes := Int.toBytes_length _ _
    simp only [sliceBytes, List.flatMap_cons]
    split
    · subst ‹n = 0›; simp
    · split
      · rw [ih, List.drop_append, List.drop_eq_nil_of_le (as := cellBytes c) (by omega),
          List.nil_append, hl]
      · have e : n - (((cellBytes c).drop k).take n).length = n - ((cellBytes c).drop k).length := by
          rw [List.length_take]; omega
        rw [ih, e, List.drop_append, hl, Nat.sub_eq_zero_of_le (show k ≤ c.w.bytes by omega),
          List.drop_zero, List.take_append]

def Obj.loadBytesFast (o : Obj) (a : BitVec 64) (w : Width) : Option w.type :=
  if o.spansFast a w then
    some (BitVec.ofInt w.bits
      (Int.ofBytes (sliceBytes (a.toNat - o.addr.toNat) w.bytes o.cells)))
  else none

theorem Obj.loadBytes_eq_loadBytesFast : @Obj.loadBytes = @Obj.loadBytesFast := by
  funext o a w
  simp only [Obj.loadBytes, Obj.loadBytesFast, sliceBytes_eq, ite_of_iff (o.spans_iff a w)]
  rfl

def Heap.loadBFast (h : Heap) (a : BitVec 64) (w : Width) : Res w.type :=
  match h.loadFast a w with
  | .ok v => .ok v
  | _ => match h.findSome? fun o => o.loadBytesFast a w with
    | some v => .ok v
    | none => .stuck "load: no cell of this width at this address"

@[csimp] theorem Heap.loadB_eq_loadBFast : @Heap.loadB = @Heap.loadBFast := by
  funext h a w
  simp only [Heap.loadB, Heap.loadBFast, Heap.load_eq_loadFast, Obj.loadBytes_eq_loadBytesFast]
  generalize h.loadFast a w = r
  generalize List.findSome? (fun o => o.loadBytesFast a w) h = q
  cases r <;> cases q <;> rfl

/-! ### Byte store -/

/-- `Obj.setBytes`, with `Obj.spansFast`. -/
def Obj.setBytesFast (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) : Obj :=
  if o.writable && o.spansFast a w then
    let off := a.toNat - o.addr.toNat
    let bs := o.bytes.take off ++ Int.toBytes w.bytes v.toInt ++ o.bytes.drop (off + w.bytes)
    { o with cells := cellsOfBytes bs o.cells }
  else o

theorem Obj.setBytes_eq_setBytesFast : @Obj.setBytes = @Obj.setBytesFast := by
  funext a w v o
  simp only [Obj.setBytes, Obj.setBytesFast]
  exact ite_of_iff (by rw [Bool.and_eq_true, o.spans_iff a w]) _ _

def Heap.storeBFast (h : Heap) (a : BitVec 64) (w : Width) (v : w.type) : Res Heap :=
  if h.any fun o => (o.getFast a w).isSome then h.storeFast a w v
  else if h.any fun o => o.writable && o.spansFast a w then
    .ok (h.map (Obj.setBytesFast a w v))
  else if h.any fun o => o.spansFast a w then .stuck "store: the object is not writable"
  else .stuck "store: no cell of this width at this address"

@[csimp] theorem Heap.storeB_eq_storeBFast : @Heap.storeB = @Heap.storeBFast := by
  funext h a w v
  simp only [Heap.storeB, Heap.storeBFast, Obj.get_eq_getFast, Heap.store_eq_storeFast,
    Obj.decide_spans, Obj.setBytes_eq_setBytesFast]

end Lift.Sem
