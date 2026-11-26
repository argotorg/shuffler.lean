module

public import Lift.Sem.HeapFields
public import Lift.Sem.HeapBytesStoreSound

@[expose] public section

/-! A store of width `w` that covers several adjacent cells of an object (task UP-OBJ4), such as `movw $2,(%rdi)`
over the two 8-bit fields `kind` and `pos` of a record. The cells of the range must start at the offset of the access
and fill its `w` bytes; they can have any widths and any number.

- `spanSet v cs d n j`: the cells `cs` after a store of the bytes `[j, j + n)` of `v` at the byte offset `d`; each cell
  of the range takes its part of `v`, little-endian (`v.extractLsb' (8 * j') c.w.bits`). `none` when `[d, d + n)` is not
  a sequence of whole cells.
- `Heap.storeB_of_storeSpanAt`: under `Heap.Holds`, with no cell of width `w` at the address, `storeB` changes only the
  cells of the range. A load over several cells has no rule here. -/

namespace Lift.Sem

open Lift.P2.Total

/-- The cells after a store of the bytes `[j, j + n)` of `v` at the offset `d`: each cell of `[d, d + n)` takes its
part of `v`. `none` if `[d, d + n)` is not a sequence of whole cells. -/
def spanSet {m : Nat} (v : BitVec m) : List Cell → Nat → Nat → Nat → Option (List Cell)
  | [], d, n, _ => if d = 0 ∧ n = 0 then some [] else none
  | c :: cs, d, n, j =>
    if d = 0 ∧ n = 0 then some (c :: cs)
    else if c.w.bytes ≤ d then (spanSet v cs (d - c.w.bytes) n j).map (c :: ·)
    else if d = 0 ∧ c.w.bytes ≤ n then
      (spanSet v cs 0 (n - c.w.bytes) (j + c.w.bytes)).map (⟨c.w, v.extractLsb' (8 * j) c.w.bits⟩ :: ·)
    else none

/-! ### The rules of `spanSet` (simp set `heap_field`) -/

theorem spanSet_zero_zero {m : Nat} (v : BitVec m) (cs : List Cell) (j : Nat) : spanSet v cs 0 0 j = some cs := by
  cases cs <;> simp [spanSet]

theorem spanSet_cons_ge {m : Nat} (v : BitVec m) {c : Cell} {cs : List Cell} {d : Nat} (n j : Nat)
    (h : c.w.bytes ≤ d) : spanSet v (c :: cs) d n j = (spanSet v cs (d - c.w.bytes) n j).map (c :: ·) := by
  have := width_bytes_pos c.w
  rw [spanSet]
  repeat' split
  all_goals first | rfl | omega

theorem spanSet_cons_zero {m : Nat} (v : BitVec m) {c : Cell} {cs : List Cell} {n : Nat} (j : Nat)
    (h : c.w.bytes ≤ n) : spanSet v (c :: cs) 0 n j =
      (spanSet v cs 0 (n - c.w.bytes) (j + c.w.bytes)).map (⟨c.w, v.extractLsb' (8 * j) c.w.bits⟩ :: ·) := by
  have := width_bytes_pos c.w
  rw [spanSet]
  repeat' split
  all_goals first | rfl | omega

theorem spanSet_append_left {m : Nat} (v : BitVec m) {l₂ : List Cell} :
    ∀ {l₁ : List Cell} {d n : Nat} (j : Nat), d + n ≤ cellsSize l₁ → 0 < n →
      spanSet v (l₁ ++ l₂) d n j = (spanSet v l₁ d n j).map (· ++ l₂)
  | [], d, n, j, h, hn => by simp [cellsSize] at h; omega
  | c :: l₁, d, n, j, h, hn => by
    rw [cellsSize_cons] at h
    have := width_bytes_pos c.w
    rw [List.cons_append]
    by_cases hd : c.w.bytes ≤ d
    · rw [spanSet_cons_ge v n j hd, spanSet_cons_ge v n j hd, spanSet_append_left v j (by omega) hn]
      simp [Option.map_map, Function.comp_def]
    · by_cases hz : d = 0 ∧ c.w.bytes ≤ n
      · obtain ⟨rfl, hc⟩ := hz
        rw [spanSet_cons_zero v j hc, spanSet_cons_zero v j hc]
        by_cases hn' : n - c.w.bytes = 0
        · rw [hn', spanSet_zero_zero, spanSet_zero_zero]; rfl
        · rw [spanSet_append_left v (j + c.w.bytes) (by omega) (by omega)]
          simp [Option.map_map, Function.comp_def]
      · have e : ∀ l : List Cell, spanSet v (c :: l) d n j = none := by
          intro l
          rw [spanSet]
          repeat' split
          all_goals first | rfl | omega
        rw [e, e]; rfl

theorem spanSet_append_right {m : Nat} (v : BitVec m) {l₂ : List Cell} :
    ∀ {l₁ : List Cell} {d n : Nat} (j : Nat), cellsSize l₁ ≤ d → 0 < n →
      spanSet v (l₁ ++ l₂) d n j = (spanSet v l₂ (d - cellsSize l₁) n j).map (l₁ ++ ·)
  | [], d, n, j, h, hn => by simp [cellsSize]
  | c :: l₁, d, n, j, h, hn => by
    rw [cellsSize_cons] at h
    rw [List.cons_append, spanSet_cons_ge v n j (by omega), spanSet_append_right v j (by omega) hn,
      cellsSize_cons, Nat.sub_add_eq]
    simp [Option.map_map, Function.comp_def]

/-- A store over whole cells at the offset `k * s + r` of an array of elements of `s` bytes, inside the element `k`. -/
theorem spanSet_flatMap {m : Nat} (v : BitVec m) {α : Type} {l : List α} {g : α → List Cell} {s k r n : Nat}
    (j : Nat) (hs : ∀ x, cellsSize (g x) = s) (hk : k < l.length) (hr : r + n ≤ s) (hn : 0 < n) :
    spanSet v (l.flatMap g) (k * s + r) n j =
      (spanSet v (g l[k]) r n j).map fun x => (l.take k).flatMap g ++ x ++ (l.drop (k + 1)).flatMap g := by
  induction l generalizing k with
  | nil => cases hk
  | cons x l ih =>
    rw [List.flatMap_cons]
    cases k with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, spanSet_append_left v j (by rw [hs]; omega) hn]
      simp
    | succ k =>
      rw [spanSet_append_right v j (by rw [hs, Nat.succ_mul]; omega) hn, hs,
        show (k + 1) * s + r - s = k * s + r by rw [Nat.succ_mul]; omega, ih (by simpa using hk)]
      simp [Option.map_map, Function.comp_def]

theorem spanSet_flatMap_zero {m : Nat} (v : BitVec m) {α : Type} {l : List α} {g : α → List Cell} {s k n : Nat}
    (j : Nat) (hs : ∀ x, cellsSize (g x) = s) (hk : k < l.length) (hr : n ≤ s) (hn : 0 < n) :
    spanSet v (l.flatMap g) (k * s) n j =
      (spanSet v (g l[k]) 0 n j).map fun x => (l.take k).flatMap g ++ x ++ (l.drop (k + 1)).flatMap g := by
  have := spanSet_flatMap (r := 0) v j hs hk (by omega) hn
  simpa using this

/-- A cell of another width at an offset: no cell of width `w'` (the side condition on bytes, for `omega`). -/
theorem Cell.get_ne_bytes {w w' : Width} (v : w.type) (h : w.bytes ≠ w'.bytes) : (Cell.mk w v).get w' = none :=
  Cell.get_ne v fun e => h (e ▸ rfl)

/-- A range of whole cells is inside the cells. -/
theorem spanSet_size {m : Nat} {v : BitVec m} :
    ∀ {cs : List Cell} {d n j : Nat} {cs' : List Cell}, spanSet v cs d n j = some cs' → d + n ≤ cellsSize cs
  | [], d, n, j, cs', h => by
    simp only [spanSet] at h
    split at h
    · rename_i h0; simp [cellsSize, h0.1, h0.2]
    · cases h
  | c :: cs, d, n, j, cs', h => by
    rw [cellsSize_cons]
    simp only [spanSet] at h
    split at h
    · omega
    · split at h
      · obtain ⟨_, h', -⟩ := Option.map_eq_some_iff.mp h
        have := spanSet_size h'
        omega
      · split at h
        · obtain ⟨_, h', -⟩ := Option.map_eq_some_iff.mp h
          have := spanSet_size h'
          omega
        · cases h

/-! ### Bytes -/

theorem toBytes_take : ∀ (k n : Nat) (x : Int), k ≤ n → (Int.toBytes n x).take k = Int.toBytes k x
  | 0, _, _, _ => by simp [Int.toBytes]
  | k + 1, 0, _, h => by omega
  | k + 1, n + 1, x, h => by
    simp only [Int.toBytes, List.take_succ_cons, toBytes_take k n (x / 256) (by omega)]

theorem toBytes_drop : ∀ (j n : Nat) (x : Int), (Int.toBytes n x).drop j = Int.toBytes (n - j) (x / 256 ^ j)
  | 0, _, _ => by simp
  | j + 1, 0, _ => by simp [Int.toBytes]
  | j + 1, n + 1, x => by
    simp only [Int.toBytes, List.drop_succ_cons, toBytes_drop j n (x / 256)]
    rw [Int.ediv_ediv_of_nonneg (by decide), Int.pow_succ', Nat.add_sub_add_right]

/-- The bytes of the integer of a value are the bytes of its number. -/
theorem toBytes_toInt (w : Width) (v : w.type) : Int.toBytes w.bytes v.toInt = Int.toBytes w.bytes (v.toNat : Int) := by
  rw [← Int.toBytes_emod w.bytes v.toInt, ← Int.toBytes_emod w.bytes (v.toNat : Int)]
  congr 1
  show v.toInt % 2 ^ (8 * w.bytes) = (v.toNat : Int) % 2 ^ (8 * w.bytes)
  have e : (2 : Int) ^ (8 * w.bytes) = ((2 ^ w.bits : Nat) : Int) := by rw [← width_bits_eq]; push_cast; rfl
  rw [e, BitVec.toInt_eq_toNat_bmod, Int.bmod_emod]

/-- The bytes `[j, j + k)` of the number `t` read back as a number of `8 * k` bits: `t / 256 ^ j`. -/
theorem ofInt_ofBytes_slice (N j k b : Nat) (t : Nat) (hb : b = 8 * k) (h : j + k ≤ N) :
    BitVec.ofInt b (Int.ofBytes (((Int.toBytes N (t : Int)).drop j).take k)) = BitVec.ofNat b (t / 256 ^ j) := by
  rw [toBytes_drop, toBytes_take _ _ _ (by omega), BitVec.ofInt_ofBytes_toBytes _ _ hb]
  rw [show ((t : Int) / 256 ^ j) = ((t / 256 ^ j : Nat) : Int) by rw [Int.natCast_ediv, Int.natCast_pow]; rfl, BitVec.ofInt_natCast]

theorem ofNat_div_eq_extractLsb' {m : Nat} (v : BitVec m) (j b : Nat) :
    BitVec.ofNat b (v.toNat / 256 ^ j) = v.extractLsb' (8 * j) b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- A cell reads back from its own bytes. -/
theorem cellsOfBytes_cons_bytes (c : Cell) (cs : List Cell) (X : List UInt8) :
    cellsOfBytes (c.bytes ++ X) (c :: cs) = c :: cellsOfBytes X cs := by
  obtain ⟨w, v⟩ := c
  simp only [cellsOfBytes]
  have hl : (Cell.bytes ⟨w, v⟩).length = w.bytes := Cell.bytes_length _
  rw [List.take_left' hl, List.drop_left' hl]
  unfold Cell.bytes
  simp only [BitVec.ofInt_ofBytes_toBytes _ _ (width_bits_eq w), BitVec.ofInt_toInt]

/-- The cells of the new bytes of a store of a range of whole cells are the cells of `spanSet`. -/
theorem cellsOfBytes_span {m : Nat} (v : BitVec m) (N : Nat) :
    ∀ (cs : List Cell) (d n j : Nat) (cs' : List Cell), j + n ≤ N → spanSet v cs d n j = some cs' →
      cellsOfBytes ((cs.flatMap Cell.bytes).take d ++ ((Int.toBytes N (v.toNat : Int)).drop j).take n ++
        (cs.flatMap Cell.bytes).drop (d + n)) cs = cs'
  | [], d, n, j, cs', _, h => by
    simp only [spanSet] at h
    split at h
    · cases h; rfl
    · cases h
  | c :: cs, d, n, j, cs', hj, h => by
    have hcb := Cell.bytes_length c
    have hwp := width_bytes_pos c.w
    simp only [spanSet] at h
    split at h
    · rename_i h0
      obtain ⟨rfl, rfl⟩ := h0
      cases h
      simp only [List.take_zero, List.nil_append, Nat.add_zero, List.drop_zero]
      exact cellsOfBytes_flatMap _
    · split at h
      · rename_i _ hge
        obtain ⟨cs'', h', rfl⟩ := Option.map_eq_some_iff.mp h
        have ih := cellsOfBytes_span v N cs (d - c.w.bytes) n j cs'' hj h'
        have hT : (c.bytes ++ cs.flatMap Cell.bytes).take d =
            c.bytes ++ (cs.flatMap Cell.bytes).take (d - c.w.bytes) := by
          rw [List.take_append, List.take_of_length_le (by omega), hcb]
        have hD : (c.bytes ++ cs.flatMap Cell.bytes).drop (d + n) =
            (cs.flatMap Cell.bytes).drop (d - c.w.bytes + n) := by
          rw [List.drop_append, List.drop_eq_nil_of_le (by omega), hcb, List.nil_append,
            show d + n - c.w.bytes = d - c.w.bytes + n by omega]
        rw [List.flatMap_cons, hT, hD, List.append_assoc, List.append_assoc, cellsOfBytes_cons_bytes,
          ← List.append_assoc, ih]
      · split at h
        · rename_i h0 _ h1
          obtain ⟨rfl, hn⟩ := h1
          obtain ⟨cs'', h', rfl⟩ := Option.map_eq_some_iff.mp h
          have ih := cellsOfBytes_span v N cs 0 (n - c.w.bytes) (j + c.w.bytes) cs'' (by omega) h'
          simp only [List.take_zero, List.nil_append, Nat.zero_add] at ih ⊢
          have hB : (Int.toBytes N (v.toNat : Int)).length = N := Int.toBytes_length _ _
          have hM : (((Int.toBytes N (v.toNat : Int)).drop j).take n).length = n := by
            simp only [List.length_take, List.length_drop, hB]; omega
          have hD : (c.bytes ++ cs.flatMap Cell.bytes).drop n = (cs.flatMap Cell.bytes).drop (n - c.w.bytes) := by
            rw [List.drop_append, List.drop_eq_nil_of_le (by omega), hcb, List.nil_append]
          rw [List.flatMap_cons, hD]
          simp only [cellsOfBytes]
          rw [List.take_append_of_le_length (by omega), List.take_take, Nat.min_eq_left hn,
            List.drop_append_of_le_length (by omega), List.drop_take, List.drop_drop,
            ofInt_ofBytes_slice N j c.w.bytes c.w.bits v.toNat (width_bits_eq c.w) (by omega),
            ofNat_div_eq_extractLsb', ih]
        · cases h

/-! ### Stores -/

/-- `h'` is `h` after a store of `v` over the cells of `[a, a + w)` of a writable object of `h`, which has no cell of
width `w` at `a`. -/
inductive Heap.StoreSpanAt (a : BitVec 64) (w : Width) (v : w.type) : Heap → Heap → Prop
  | head {o : Obj} {t : Heap} {cs : List Cell} : o.writable = true → cellGet o.cells (a - o.addr).toNat w = none →
      spanSet v o.cells (a - o.addr).toNat w.bytes 0 = some cs →
      Heap.StoreSpanAt a w v (o :: t) ({ o with cells := cs } :: t)
  | tail {o : Obj} {t t' : Heap} : Heap.StoreSpanAt a w v t t' → Heap.StoreSpanAt a w v (o :: t) (o :: t')

theorem Heap.StoreSpanAt.mem {a : BitVec 64} {w : Width} {v : w.type} {h h' : Heap}
    (hs : Heap.StoreSpanAt a w v h h') :
    ∃ o ∈ h, o.writable = true ∧ cellGet o.cells (a - o.addr).toNat w = none ∧
      ∃ cs, spanSet v o.cells (a - o.addr).toNat w.bytes 0 = some cs := by
  induction hs with
  | head hw hc hs => exact ⟨_, List.mem_cons_self .., hw, hc, _, hs⟩
  | tail _ ih =>
    obtain ⟨o, ho, h1, h2, h3⟩ := ih
    exact ⟨o, List.mem_cons_of_mem _ ho, h1, h2, h3⟩

/-- A cell at an offset of the cells is the cell of `cellGet` there. -/
theorem cellGet_of_mem_offsets {w : Width} {v : w.type} :
    ∀ {cs : List Cell} {n : Nat} {x : Nat × Cell}, x ∈ offsets n cs → x.2 = ⟨w, v⟩ → cellGet cs (x.1 - n) w = some v
  | [], _, _, hx, _ => by cases hx
  | c :: cs, n, x, hx, he => by
    simp only [offsets, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [Nat.sub_self] at he ⊢
      subst he
      exact cellGet_cons_zero _ _ _ ▸ Cell.get_self w v
    · have hb := offsets_bound hx
      rw [cellGet_cons_ge w (by omega), show x.1 - n - c.w.bytes = x.1 - (n + c.w.bytes) by omega]
      exact cellGet_of_mem_offsets hx he

/-- The access of a range of whole cells is spanned by the object. -/
theorem Obj.spans_of_size {o : Obj} {a : BitVec 64} {w : Width} (hn : o.addr.toNat + o.size ≤ 2 ^ 64)
    (h : (a - o.addr).toNat + w.bytes ≤ cellsSize o.cells) :
    o.Spans a w ∧ a = o.addr + BitVec.ofNat 64 (a - o.addr).toNat ∧ (a - o.addr).toNat + w.bytes ≤ o.size :=
  have hs : (a - o.addr).toNat + w.bytes ≤ o.size := h
  ⟨(Obj.spans_of_offset (add_toNat_sub o.addr a).symm hs hn).1, (add_toNat_sub o.addr a).symm, hs⟩

/-- With no cell of width `w` at `a` in a writable object that spans the access, no object of the heap has one. -/
theorem Heap.Holds.no_get {policy : CpuPolicy} {h : Heap} {m : DataMem} (hh : h.Holds policy m) {O : Obj}
    (hO : O ∈ h) (hw : O.writable = true) {a : BitVec 64} {w : Width} (hsp : O.Spans a w)
    (hc : cellGet O.cells (a - O.addr).toNat w = none) : ∀ o ∈ h, o.get a w = none := by
  intro o ho
  cases hg : o.get a w with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨y, hy, hya, hyc⟩ := Obj.get_some hg
    have hn := hh.noWrap o ho
    have hb := offsets_bound hy
    have hwp := width_bytes_pos w
    have hwy := width_bytes_pos y.2.w
    have hyw : y.2.w = w := by rw [hyc]
    have ea : a.toNat = o.addr.toNat + y.1 := by
      rw [← hya, toNat_add_ofNat _ _ (by simp only [Nat.zero_add] at hb; unfold Obj.size at hn; omega)]
    by_cases he : o = O
    · subst he
      have : (a - o.addr).toNat = y.1 := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]; omega
      have := cellGet_of_mem_offsets hy hyc
      simp only [Nat.sub_zero] at this
      rw [‹(a - o.addr).toNat = y.1›, this] at hc
      cases hc
    · have hs' : o.Spans a w := by
        unfold Obj.Spans
        simp only [Nat.zero_add] at hb
        rw [hyw] at hb
        unfold Obj.size
        omega
      have hapart := pairwise_of_mem (R := fun o o' => (o.writable ∨ o'.writable) → o.Apart o')
        (fun h hw' => Or.symm (h (Or.symm hw'))) hh.apart hO ho (Ne.symm he) (.inl (by simp [hw]))
      exact Obj.not_apart_of_spans hsp hs' hapart

/-- The object after a store over a range of whole cells. -/
theorem Obj.setBytes_span {o : Obj} {a : BitVec 64} {w : Width} {v : w.type} {cs : List Cell}
    (hw : o.writable = true) (hn : o.addr.toNat + o.size ≤ 2 ^ 64)
    (hs : spanSet v o.cells (a - o.addr).toNat w.bytes 0 = some cs) :
    Obj.setBytes a w v o = { o with cells := cs } := by
  obtain ⟨-, ha, hk⟩ := Obj.spans_of_size hn (spanSet_size hs)
  have hc := Obj.setBytes_cells v ha hk hn hw
  have e := cellsOfBytes_span v w.bytes o.cells _ w.bytes 0 cs (by omega) hs
  simp only [List.drop_zero, List.take_of_length_le (Nat.le_of_eq (Int.toBytes_length _ _))] at e
  rw [← toBytes_toInt, ← Obj.bytes_eq] at e
  rw [e] at hc
  have e1 := Obj.setBytes_addr a w v o
  have e2 := Obj.setBytes_writable a w v o
  revert hc e1 e2
  generalize Obj.setBytes a w v o = o'
  intro hc e1 e2
  cases o'
  cases o
  simp only at hc e1 e2 ⊢
  rw [Obj.mk.injEq]
  exact ⟨e1, e2, hc⟩

/-- A store over the cells of a range of a writable object: only those cells change. -/
theorem Heap.storeB_of_storeSpanAt {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64} {w : Width}
    {v : w.type} (hh : h.Holds policy m) (hs : Heap.StoreSpanAt a w v h h') : h.storeB a w v = .ok h' := by
  obtain ⟨O, hO, hOw, hOc, cs, hOs⟩ := hs.mem
  obtain ⟨hsp, -, -⟩ := Obj.spans_of_size (hh.noWrap O hO) (spanSet_size hOs)
  have hng := hh.no_get hO hOw hsp hOc
  have h1 : (h.any fun o => (o.get a w).isSome) = false := by
    rw [List.any_eq_false]
    intro o ho
    simp [hng o ho]
  have h2 : (h.any fun o => o.writable && decide (o.Spans a w)) = true :=
    List.any_eq_true.mpr ⟨O, hO, by simp [hOw, hsp]⟩
  unfold Heap.storeB
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
  congr 1
  have key : ∀ (h₀ h₁ : Heap), h₀.Sublist h → Heap.StoreSpanAt a w v h₀ h₁ → h₀.map (Obj.setBytes a w v) = h₁ := by
    intro h₀ h₁ hsub hs₀
    induction hs₀ with
    | @head o t cs' hw hc hs₁ =>
      have hh₀ := hh.sublist hsub
      have ho : o ∈ h := hsub.subset (List.mem_cons_self ..)
      have hn := hh₀.noWrap o (List.mem_cons_self ..)
      obtain ⟨hsp₁, -, hk⟩ := Obj.spans_of_size hn (spanSet_size hs₁)
      have hno := not_mem_of_holds hh₀ hw (by have := width_bytes_pos w; omega)
      rw [List.map_cons, Obj.setBytes_span hw hn hs₁]
      congr 1
      conv => rhs; rw [← List.map_id t]
      apply List.map_congr_left
      intro p hp
      exact hh.setBytes_other ho (hsub.subset (List.mem_cons_of_mem _ hp)) (fun e => hno (e ▸ hp)) hw hsp₁
    | @tail o t t' hs₁ ih =>
      have hh₀ := hh.sublist hsub
      rw [List.map_cons, ih ((List.sublist_cons_self o t).trans hsub)]
      congr 1
      obtain ⟨O', hO', hO'w, -, cs'', hO's⟩ := hs₁.mem
      have hn' := hh₀.noWrap O' (List.mem_cons_of_mem _ hO')
      obtain ⟨hsp', -, hk'⟩ := Obj.spans_of_size hn' (spanSet_size hO's)
      have hne : o ≠ O' := by
        intro e
        subst e
        exact not_mem_of_holds hh₀ hO'w (by have := width_bytes_pos w; omega) hO'
      exact hh.setBytes_other (hsub.subset (List.mem_cons_of_mem _ hO')) (hsub.subset (List.mem_cons_self ..)) hne
        hO'w hsp'
  exact key h h' (List.Sublist.refl h) hs

end Lift.Sem
