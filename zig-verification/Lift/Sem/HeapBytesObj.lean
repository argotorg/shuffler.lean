module

public import Lift.Sem.HeapBytesStore
import all Kraken.Mem
import all Kraken.SeparationMem

@[expose] public section

/-! The object part of the soundness of the byte fallback store `Heap.storeB`: after a write of a
byte range inside one writable object, the memory holds the bytes of the object `Obj.setBytes`, and
each cell of that object reads back its value. The other objects (the frame part) are in
`Lift/Sem/HeapBytesStore.lean`. -/

namespace Lift.Sem

open Lift.P2.Total Lift.Sem.ByteLemmas

/-! ### `cellsOfBytes` -/

/-- The cells of `cellsOfBytes bs cs` have the widths of `cs`. -/
theorem cellsOfBytes_widths (bs : List UInt8) :
    ∀ cs : List Cell, (cellsOfBytes bs cs).map (·.w) = cs.map (·.w)
  | [] => rfl
  | c :: cs => by simp [cellsOfBytes, cellsOfBytes_widths _ cs]

/-- The bytes of the cells of `cellsOfBytes bs cs` are `bs`, when `bs` has the length of `cs`. -/
theorem cellsOfBytes_bytes :
    ∀ (cs : List Cell) (bs : List UInt8), bs.length = (cs.map fun c => c.w.bytes).sum →
      (cellsOfBytes bs cs).flatMap Cell.bytes = bs
  | [], bs, h => by simp at h; simp [cellsOfBytes, h]
  | c :: cs, bs, h => by
    simp only [List.map_cons, List.sum_cons] at h
    simp only [cellsOfBytes, List.flatMap_cons]
    have hl : (bs.take c.w.bytes).length = c.w.bytes := by
      simp only [List.length_take]; omega
    have e : Cell.bytes ⟨c.w, BitVec.ofInt c.w.bits (Int.ofBytes (bs.take c.w.bytes))⟩ =
        bs.take c.w.bytes := by
      unfold Cell.bytes
      show Int.toBytes c.w.bytes (BitVec.ofInt c.w.bits _).toInt = _
      have := toBytes_toInt_ofInt_ofBytes c.w.bytes (bs.take c.w.bytes) hl
      rwa [← width_bits_eq c.w] at this
    rw [e, cellsOfBytes_bytes cs _ (by simp only [List.length_drop]; omega), List.take_append_drop]

/-- Each cell is read back from its own bytes. -/
theorem cellsOfBytes_flatMap : ∀ cs : List Cell, cellsOfBytes (cs.flatMap Cell.bytes) cs = cs
  | [] => rfl
  | c :: cs => by
    obtain ⟨w, v⟩ := c
    simp only [List.flatMap_cons, cellsOfBytes]
    have hl : (Cell.bytes ⟨w, v⟩).length = w.bytes := Cell.bytes_length _
    rw [List.take_left' hl, List.drop_left' hl, cellsOfBytes_flatMap cs]
    unfold Cell.bytes
    simp only [BitVec.ofInt_ofBytes_toBytes _ _ (width_bits_eq w), BitVec.ofInt_toInt]

/-- The cells of an object are read back from its bytes. -/
theorem cellsOfBytes_self (o : Obj) : cellsOfBytes o.bytes o.cells = o.cells :=
  cellsOfBytes_flatMap o.cells

/-- The offsets and widths of the cells of `cellsOfBytes bs cs` are those of `cs`. -/
theorem offsets_cellsOfBytes : ∀ (n : Nat) (cs : List Cell) (bs : List UInt8),
    ∀ y ∈ offsets n (cellsOfBytes bs cs), ∃ x ∈ offsets n cs, y.1 = x.1 ∧ y.2.w = x.2.w
  | n, [], bs, y, hy => by simp [cellsOfBytes, offsets] at hy
  | n, c :: cs, bs, y, hy => by
    simp only [cellsOfBytes, offsets, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨(n, c), by simp [offsets], rfl, rfl⟩
    · obtain ⟨x, hx, h1, h2⟩ := offsets_cellsOfBytes (n + c.w.bytes) cs _ y hy
      exact ⟨x, by simp [offsets, hx], h1, h2⟩

/-! ### `Obj.setBytes` -/

theorem Obj.setBytes_of_not_writable {a : BitVec 64} {w : Width} {v : w.type} {o : Obj}
    (h : o.writable = false) : Obj.setBytes a w v o = o := by
  unfold Obj.setBytes
  simp [h]

/-- An object that does not span the access does not change. -/
theorem Obj.setBytes_of_not_spans {a : BitVec 64} {w : Width} {v : w.type} {o : Obj}
    (h : ¬ o.Spans a w) : Obj.setBytes a w v o = o := by
  unfold Obj.setBytes
  simp [h]

theorem Obj.setBytes_addr (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    (Obj.setBytes a w v o).addr = o.addr := by
  unfold Obj.setBytes; split <;> rfl

theorem Obj.setBytes_writable (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    (Obj.setBytes a w v o).writable = o.writable := by
  unfold Obj.setBytes; split <;> rfl

/-- The cells keep their widths. -/
theorem Obj.setBytes_widths (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    (Obj.setBytes a w v o).cells.map (·.w) = o.cells.map (·.w) := by
  unfold Obj.setBytes; split
  · exact cellsOfBytes_widths _ _
  · rfl

theorem Obj.setBytes_size (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    (Obj.setBytes a w v o).size = o.size := by
  have := congrArg (fun l => (List.map Width.bytes l).sum) (Obj.setBytes_widths a w v o)
  simpa [Obj.size, List.map_map, Function.comp_def] using this

/-- The offsets and widths of the cells do not change. -/
theorem Obj.setBytes_offsets (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    ∀ y ∈ offsets 0 (Obj.setBytes a w v o).cells,
      ∃ x ∈ offsets 0 o.cells, y.1 = x.1 ∧ y.2.w = x.2.w := by
  intro y hy
  unfold Obj.setBytes at hy
  split at hy
  · exact offsets_cellsOfBytes 0 _ _ y hy
  · exact ⟨y, hy, rfl, rfl⟩

/-- The access at the offset `k` of an object that does not wrap: the object spans it. -/
theorem Obj.spans_of_offset {o : Obj} {a : BitVec 64} {w : Width} {k : Nat}
    (ha : a = o.addr + BitVec.ofNat 64 k) (hk : k + w.bytes ≤ o.size)
    (hn : o.addr.toNat + o.size ≤ 2 ^ 64) : o.Spans a w ∧ a.toNat - o.addr.toNat = k := by
  have hw : 0 < w.bytes := by cases w <;> decide
  subst ha
  rw [toNat_add_ofNat _ _ (by omega)]
  unfold Obj.Spans
  rw [toNat_add_ofNat _ _ (by omega)]
  omega

/-- The new bytes of the object: the bytes `[k, k + w)` are replaced. -/
theorem Obj.setBytes_bytes {o : Obj} {a : BitVec 64} {w : Width} (v : w.type) {k : Nat}
    (ha : a = o.addr + BitVec.ofNat 64 k) (hk : k + w.bytes ≤ o.size)
    (hn : o.addr.toNat + o.size ≤ 2 ^ 64) (hw : o.writable = true) :
    (Obj.setBytes a w v o).bytes =
      o.bytes.take k ++ Int.toBytes w.bytes v.toInt ++ o.bytes.drop (k + w.bytes) := by
  obtain ⟨hs, hoff⟩ := Obj.spans_of_offset ha hk hn
  have hlen : (o.bytes.take k ++ Int.toBytes w.bytes v.toInt ++ o.bytes.drop (k + w.bytes)).length
      = (o.cells.map fun c => c.w.bytes).sum := by
    have := o.bytes_length
    unfold Obj.size at hk this
    simp only [List.length_append, List.length_take, List.length_drop, Int.toBytes_length]
    omega
  unfold Obj.setBytes
  simp only [hw, hs, and_self, ↓reduceIte, hoff]
  exact cellsOfBytes_bytes o.cells _ hlen

/-- The cells of the new object. -/
theorem Obj.setBytes_cells {o : Obj} {a : BitVec 64} {w : Width} (v : w.type) {k : Nat}
    (ha : a = o.addr + BitVec.ofNat 64 k) (hk : k + w.bytes ≤ o.size)
    (hn : o.addr.toNat + o.size ≤ 2 ^ 64) (hw : o.writable = true) :
    (Obj.setBytes a w v o).cells = cellsOfBytes
      (o.bytes.take k ++ Int.toBytes w.bytes v.toInt ++ o.bytes.drop (k + w.bytes)) o.cells := by
  obtain ⟨hs, hoff⟩ := Obj.spans_of_offset ha hk hn
  unfold Obj.setBytes
  simp only [hw, hs, and_self, ↓reduceIte, hoff]

/-! ### The memory after a write -/

/-- The memory with the stored integer holds the new bytes of the object. -/
theorem Obj.holds_after_storeInt {m m' : DataMem} {o : Obj} {w : Width}
    {v : w.type} {k : Nat} (hc : m.Contains o.addr o.bytes)
    (hw : m' = Mem.storeInt m (o.addr + BitVec.ofNat 64 k) w.bytes v.toInt)
    (hk : k + w.bytes ≤ o.size) (hn : o.addr.toNat + o.size ≤ 2 ^ 64)
    (hwr : o.writable = true) :
    m'.Contains o.addr (Obj.setBytes (o.addr + BitVec.ofNat 64 k) w v o).bytes := by
  rw [Obj.setBytes_bytes v rfl hk hn hwr, hw]
  have hlen := o.bytes_length
  have hwb : 0 < w.bytes := by cases w <;> decide
  have := Contains.storeBytes_slice hc k (Int.toBytes w.bytes v.toInt)
    (by rw [Int.toBytes_length, hlen]; exact hk) (by omega) (by omega)
  simpa only [Mem.storeInt, Int.toBytes_length] using this

/-- The memory holds the new bytes of the object. -/
theorem Obj.holds_after_write {policy : CpuPolicy} {m m' : DataMem} {o : Obj} {w : Width}
    {v : w.type} {k : Nat} (hc : m.Contains o.addr o.bytes)
    (hw : writeRam policy m (o.addr + BitVec.ofNat 64 k) w v = .ok m')
    (hk : k + w.bytes ≤ o.size) (hn : o.addr.toNat + o.size ≤ 2 ^ 64)
    (hwr : o.writable = true) :
    m'.Contains o.addr (Obj.setBytes (o.addr + BitVec.ofNat 64 k) w v o).bytes :=
  Obj.holds_after_storeInt hc (writeRam_ok_eq hw) hk hn hwr

/-- Each cell of the new object reads back its value from the memory with the stored integer,
when the policy permits the reads of the cells (they have the addresses and the widths of the cells
of `o`). -/
theorem Obj.reads_after_storeInt {policy : CpuPolicy} {m m' : DataMem} {o : Obj} {w : Width}
    {v : w.type} {k : Nat} (hc : m.Contains o.addr o.bytes)
    (hw : m' = Mem.storeInt m (o.addr + BitVec.ofNat 64 k) w.bytes v.toInt)
    (hk : k + w.bytes ≤ o.size) (hn : o.addr.toNat + o.size ≤ 2 ^ 64)
    (hwr : o.writable = true)
    (hp : ∀ x ∈ offsets 0 o.cells,
      policy.permits (.read (o.addr + BitVec.ofNat 64 x.1) x.2.w) = true) :
    ∀ y ∈ offsets 0 (Obj.setBytes (o.addr + BitVec.ofNat 64 k) w v o).cells,
      readRam policy m' (o.addr + BitVec.ofNat 64 y.1) y.2.w = .ok y.2.v := by
  have hh := Obj.holds_after_storeInt hc hw hk hn hwr
  have hall := read_of_contains (policy := policy) o.addr 0
    (Obj.setBytes (o.addr + BitVec.ofNat 64 k) w v o).cells
    (by simpa [Obj.bytes_eq] using hh)
    (fun y hy => by
      obtain ⟨x, hx, h1, h2⟩ := Obj.setBytes_offsets _ _ _ _ y hy
      rw [h1, h2]; exact hp x hx)
  intro y hy
  exact hall y hy

/-- Each cell of the new object reads back its value from the memory after the write, when the
policy permits the reads of the cells (they have the addresses and the widths of the cells of `o`). -/
theorem Obj.reads_after_write {policy : CpuPolicy} {m m' : DataMem} {o : Obj} {w : Width}
    {v : w.type} {k : Nat} (hc : m.Contains o.addr o.bytes)
    (hw : writeRam policy m (o.addr + BitVec.ofNat 64 k) w v = .ok m')
    (hk : k + w.bytes ≤ o.size) (hn : o.addr.toNat + o.size ≤ 2 ^ 64)
    (hwr : o.writable = true)
    (hp : ∀ x ∈ offsets 0 o.cells,
      policy.permits (.read (o.addr + BitVec.ofNat 64 x.1) x.2.w) = true) :
    ∀ y ∈ offsets 0 (Obj.setBytes (o.addr + BitVec.ofNat 64 k) w v o).cells,
      readRam policy m' (o.addr + BitVec.ofNat 64 y.1) y.2.w = .ok y.2.v :=
  Obj.reads_after_storeInt hc (writeRam_ok_eq hw) hk hn hwr hp

/-- `Obj.reads_after_storeInt` for a heap that the memory and the policy hold. -/
theorem Obj.reads_after_storeInt_of_holds {policy : CpuPolicy} {h : Heap} {m m' : DataMem}
    {o : Obj} {w : Width} {v : w.type} {k : Nat} (hh : h.Holds policy m) (ho : o ∈ h)
    (hw : m' = Mem.storeInt m (o.addr + BitVec.ofNat 64 k) w.bytes v.toInt)
    (hk : k + w.bytes ≤ o.size) (hwr : o.writable = true) :
    ∀ y ∈ offsets 0 (Obj.setBytes (o.addr + BitVec.ofNat 64 k) w v o).cells,
      readRam policy m' (o.addr + BitVec.ofNat 64 y.1) y.2.w = .ok y.2.v :=
  Obj.reads_after_storeInt (hh.contains ho) hw hk (hh.noWrap o ho) hwr
    (fun x hx => (readRam_ok (hh.read o ho x hx)).1)

/-- The form for a heap that the memory and the policy hold. -/
theorem Obj.reads_after_write_of_holds {policy : CpuPolicy} {h : Heap} {m m' : DataMem}
    {o : Obj} {w : Width} {v : w.type} {k : Nat} (hh : h.Holds policy m) (ho : o ∈ h)
    (hw : writeRam policy m (o.addr + BitVec.ofNat 64 k) w v = .ok m')
    (hk : k + w.bytes ≤ o.size) (hwr : o.writable = true) :
    ∀ y ∈ offsets 0 (Obj.setBytes (o.addr + BitVec.ofNat 64 k) w v o).cells,
      readRam policy m' (o.addr + BitVec.ofNat 64 y.1) y.2.w = .ok y.2.v :=
  Obj.reads_after_storeInt_of_holds hh ho (writeRam_ok_eq hw) hk hwr

end Lift.Sem
