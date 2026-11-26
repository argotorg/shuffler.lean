module

public import Lift.Tactic.LoopSimpAttr
public import Lift.Sem.Heap
public import Lift.Sem.HeapLemmas
public import Lift.Sem.Bridge
public import Lift.Sem.HeapChain
public meta import Lean.Elab.Tactic

@[expose] public section

/-! The simp sets of the goals of a loop: `uint_norm`, `heap_load`, `list_step` (declared in
`Lift/Tactic/LoopSimpAttr.lean`). Their goals and tests: `docs/research/class-r-coordinator-deepseek-20261118.md`
(section 4) and `Lift/Tactic/Test/LoopSimp.lean`. The set `heap_norm` gives the heap of a statement as a list of
`Obj.words` and the frame, so that the `heap_load` rules match it: a load from the first object, and a store to it (the
store keeps the frame, since the memory holds the heap at the entry, where the array has the same length). -/

namespace Lift.Sem

open Lift.P2.Total

/-- The membership of an object in the list of a heap, for the discharge of the side goal `o ∈ h` of a `heap_load`
rule: the object is the head of the list, or a member of its tail. The address of the object is fixed by the left side
of the rule, so the head that matches is the one with that address; the other fields come from the match. -/
syntax "heap_mem" : tactic
macro_rules
  | `(tactic| heap_mem) =>
    `(tactic| first | exact List.mem_cons_self .. | (apply List.mem_cons_of_mem; heap_mem))

/-- The load of the next word of a chain with the offset `0`: the address is the pointer `p`, with no `+`. -/
theorem Heap.load_next_of_ends_zero {h : Heap} {p : BitVec 64} (he : Heap.ends h 0 p = true)
    (hp : ¬ UInt64.ofBitVec p = 0) : h.load p .W64 = .ok (Heap.nextOf h 0 p) := by
  have e := Heap.load_next_of_ends he hp
  have h0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  rwa [h0] at e

/-- A load of the word at index `i` of an array of words, with the index on the left of `* 8`. -/
theorem Heap.load_words64_mul {policy : CpuPolicy} {h : Heap} {m : DataMem} {base : BitVec 64}
    {wr : Bool} {xs : List (BitVec 64)} {i : BitVec 64} (hh : h.Holds policy m)
    (ho : Obj.words base wr .W64 xs ∈ h) (hi : i.toNat < xs.length) :
    h.load (base + i * 8) .W64 = .ok xs[i.toNat] := by
  rw [BitVec.mul_comm]
  exact Heap.load_words64 hh ho hi

/-- A load of the word at index `i` of the first object of a heap, an array of words. -/
theorem Heap.load_words64_head {policy : CpuPolicy} {m : DataMem} {base : BitVec 64} {wr : Bool}
    {xs : List (BitVec 64)} {frame : Heap} {i : BitVec 64}
    (hh : Heap.Holds policy (Obj.words base wr .W64 xs :: frame) m) (hi : i.toNat < xs.length) :
    Heap.load (Obj.words base wr .W64 xs :: frame) (base + i * 8) .W64 = .ok xs[i.toNat] :=
  Heap.load_words64_mul hh (List.mem_cons_self ..) hi

/-- A store to the word at index `i` of a writable array of words that does not wrap. -/
theorem Obj.set_words64 {base : BitVec 64} {ys : List (BitVec 64)} {i : BitVec 64}
    (hn : base.toNat + 8 * ys.length ≤ 2 ^ 64) (hi : i.toNat < ys.length) (v : BitVec 64) :
    (Obj.words base true .W64 ys).set (base + i * 8) .W64 v = Obj.words base true .W64 (ys.set i.toNat v) := by
  have hs : (Obj.words base true .W64 ys).size = 8 * ys.length := by
    rw [Obj.size, Obj.words, words_bytes]
  have hc : i.toNat < (Obj.words base true .W64 ys).cells.length := by simpa [Obj.words] using hi
  have e := Obj.set_field (o := Obj.words base true .W64 ys) rfl (by rw [hs]; exact hn) i.toNat hc .W64
    (by simp [Obj.words]) v
  have hf : (Obj.words base true .W64 ys).fieldOff i.toNat = 8 * i.toNat :=
    words_fieldOff .W64 ys i.toNat (Nat.le_of_lt hi)
  have ea : BitVec.ofNat 64 (8 * i.toNat) = i * 8 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, Nat.mul_comm]
  rw [hf, ea, show (Obj.words base true .W64 ys).addr = base from rfl] at e
  rw [e]
  simp [Obj.words, List.map_set]

/-- A store to the word at index `i` of the first object of a heap, a writable array of words `ys`, where a memory
holds the heap with an array `xs` of the same length at the same address (the heap at the entry of a loop). The frame
does not change. -/
theorem Heap.store_words64_head {policy : CpuPolicy} {m : DataMem} {base : BitVec 64}
    {xs ys : List (BitVec 64)} {frame : Heap} {i : BitVec 64}
    (hh : Heap.Holds policy (Obj.words base true .W64 xs :: frame) m) (hl : ys.length = xs.length)
    (hi : i.toNat < ys.length) (v : BitVec 64) :
    Heap.store (Obj.words base true .W64 ys :: frame) (base + i * 8) .W64 v =
      .ok (Obj.words base true .W64 (ys.set i.toNat v) :: frame) := by
  have hix : i.toNat < xs.length := hl ▸ hi
  have ea : BitVec.ofNat 64 (Width.W64.bytes * i.toNat) = i * 8 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, Nat.mul_comm]
  have hsz : (Obj.words base true .W64 xs).size = 8 * xs.length := by
    rw [Obj.size, Obj.words, words_bytes]
  -- The store on the heap of `xs` leaves each object of the frame unchanged.
  obtain ⟨h', hs, hr⟩ := Heap.store_words (w := .W64) hh (List.mem_cons_self ..) hix v
  rw [ea] at hs
  have hn := not_mem_of_holds hh rfl (by rw [hsz]; omega)
  have hfr : frame.map (Obj.set (base + i * 8) .W64 v) = frame := by
    obtain ⟨hm, -⟩ := Heap.store_ok hs
    cases hr with
    | here hr' =>
      simp only [List.map_cons, List.cons.injEq] at hm
      rw [← hm.2]
      exact replaces_eq_of_not_mem hr' hn
    | there hne _ => exact absurd rfl hne
  -- The store on the heap of `ys`.
  have hx₀ := mem_offsets_words .W64 ys 0 i.toNat hi
  have hst := Heap.store_cell (h := Obj.words base true .W64 ys :: frame) (O := Obj.words base true .W64 ys)
    (List.mem_cons_self ..) rfl (by simpa [Obj.words] using hx₀) v
  simp only [Obj.words] at hst
  rw [show (⟨base, true, ys.map (Cell.mk .W64)⟩ : Obj) = Obj.words base true .W64 ys from rfl, ea] at hst
  have hw : base.toNat + (Obj.words base true .W64 xs).size ≤ 2 ^ 64 := hh.noWrap _ (List.mem_cons_self ..)
  rw [hst, List.map_cons, hfr, Obj.set_words64 (by rw [hsz] at hw; omega) hi]

end Lift.Sem

/-- The zero of `UInt64` as a constructor application: the value of `List.sum` of `[]` in `UInt64`. -/
theorem UInt64.ofBitVec_zero_eq : UInt64.ofBitVec 0 = 0 := rfl

/-- A sum of `UInt64` that does not wrap: its `toNat` is the sum of the `toNat`. -/
theorem UInt64.toNat_add_of_lt_size {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt h

/-- An equation of `UInt64.ofBitVec a` is an equation of `a`, so that the loaded word `a` takes the place of the register. -/
theorem UInt64.ofBitVec_eq_iff_eq_toBitVec {a : BitVec 64} {b : UInt64} : UInt64.ofBitVec a = b ↔ a = b.toBitVec := by
  constructor <;> intro h <;> subst h <;> rfl

/-- `UInt64.ofBitVec` of a number is `UInt64.ofNat` of the number. -/
theorem UInt64.ofBitVec_ofNat' (n : Nat) : UInt64.ofBitVec (BitVec.ofNat 64 n) = UInt64.ofNat n := rfl

/-- The zero of `UInt64` from a number. -/
theorem UInt64.ofNat_zero_eq : UInt64.ofNat 0 = 0 := rfl

/-- The order of three summands of `UInt64`, for the ordered rewriting of `simp` with `UInt64.add_comm`. -/
theorem UInt64.add_left_comm' (a b c : UInt64) : a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

/-- The one of `UInt64` from a number. -/
theorem UInt64.ofNat_one_eq : UInt64.ofNat 1 = 1 := rfl

/-- The `BitVec` of the number of a register is the `BitVec` of the register. -/
theorem BitVec.ofNat_toNat_uint64 (u : UInt64) : BitVec.ofNat 64 u.toNat = u.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- A store at the index `i` of a list whose part before `i` is the part of `l₁` before `i`: the element `a` at `i`
becomes `v`. -/
theorem List.set_take_append_cons {α : Type} {l₁ l₂ : List α} {i : Nat} (h : i ≤ l₁.length) (a v : α) :
    (l₁.take i ++ a :: l₂).set i v = l₁.take i ++ v :: l₂ := by
  rw [List.set_append_right _ _ (by simp; omega)]
  simp [Nat.min_eq_left h]

/-- A fold that adds each word to the accumulator, on the left: the accumulator plus the sum. -/
theorem UInt64.foldl_ofBitVec_add_left (l : List (BitVec 64)) (b : UInt64) :
    l.foldl (fun acc v => UInt64.ofBitVec v + acc) b = b + UInt64.ofBitVec l.sum := by
  induction l generalizing b with
  | nil => simp
  | cons v l ih =>
    rw [List.foldl_cons, ih, List.sum_cons, UInt64.ofBitVec_add, UInt64.add_comm (UInt64.ofBitVec v) b,
      UInt64.add_assoc]

/-- A fold that adds each word to the accumulator, on the right: the accumulator plus the sum. -/
theorem UInt64.foldl_add_ofBitVec_right (l : List (BitVec 64)) (b : UInt64) :
    l.foldl (fun acc v => acc + UInt64.ofBitVec v) b = b + UInt64.ofBitVec l.sum := by
  induction l generalizing b with
  | nil => simp
  | cons v l ih => rw [List.foldl_cons, ih, List.sum_cons, UInt64.ofBitVec_add, UInt64.add_assoc]

/-- A store at the index `i` of a list whose part before `i` is a list `l₁` of length `i`: the element `a` at `i` becomes
`v`. -/
theorem List.set_append_cons_of_length {α : Type} {l₁ l₂ : List α} {i : Nat} (h : l₁.length = i) (a v : α) :
    (l₁ ++ a :: l₂).set i v = l₁ ++ v :: l₂ := by
  subst h
  simp

attribute [bv_norm] UInt64.foldl_ofBitVec_add_left UInt64.foldl_add_ofBitVec_right List.set_append_cons_of_length
  List.range_succ List.map_append List.map_cons List.map_nil

attribute [bv_norm] UInt64.eq_iff_toBitVec_eq UInt64.toBitVec_add UInt64.toBitVec_sub UInt64.toBitVec_mul
  UInt64.toBitVec_one UInt64.toBitVec_zero UInt64.toBitVec_ofNat UInt64.toBitVec_ofNat' UInt64.toBitVec_ofBitVec
  BitVec.add_zero BitVec.zero_add Nat.sub_zero List.length_nil List.sum_append List.sum_singleton List.foldl_cons List.foldl_nil

-- The casts of `UInt` (`movzx`, and a register as 8, 16 or 32 bits) as `setWidth` of `BitVec` (task LC-RET).
attribute [bv_norm] UInt8.toBitVec_toUInt16 UInt8.toBitVec_toUInt32 UInt8.toBitVec_toUInt64 UInt16.toBitVec_toUInt8
  UInt16.toBitVec_toUInt32 UInt16.toBitVec_toUInt64 UInt32.toBitVec_toUInt8 UInt32.toBitVec_toUInt16
  UInt32.toBitVec_toUInt64 UInt64.toBitVec_toUInt8 UInt64.toBitVec_toUInt16 UInt64.toBitVec_toUInt32

/-- A step `a - b` of `UInt64` that does not wrap (a counter that goes down, `b ≤ a`): its `toNat` is the difference. -/
theorem UInt64.toNat_sub_of_toNat_le {a b : UInt64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le a b (UInt64.le_iff_toNat_le.mpr h)

/-- A sum of `BitVec w` with a number (`x + 18446744073709551615`, the step `x - 1` of the code) as a sum of numbers
modulo `2 ^ w`. -/
theorem BitVec.toNat_add_lit {w : Nat} (a : BitVec w) (n : Nat) :
    (a + (no_index (OfNat.ofNat n : BitVec w))).toNat = (a.toNat + n % 2 ^ w) % 2 ^ w := by
  rw [BitVec.toNat_add]
  rfl

/-- A sum `n + c` modulo `m` that wraps once (`c` is `m - k` with `k ≤ n`): the step `n - k`. -/
theorem Nat.add_mod_of_sub_le {n c m : Nat} (hc : c < m) (hn : n < m) (h : m - c ≤ n) : (n + c) % m = n - (m - c) := by
  have e : n + c = (n - (m - c)) + m := by omega
  rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- A sum of `UInt64` with a number at or above `2 ^ 63` (the step `x - k` of the code, `x + (2 ^ 64 - k)`) as `x - k`. With
`x + 18446744073709551615` in the goal, the type check of a goal that `simp` changes by definition (`id`) can unfold
`(x + 18446744073709551615).toNat`, and `Nat.add` peels the number one at a time (deep recursion of the kernel). -/
theorem UInt64.add_lit_eq_sub (x : UInt64) (n : Nat) (h : 2 ^ 63 ≤ n) (h' : n < 2 ^ 64) :
    x + (no_index (OfNat.ofNat n : UInt64)) = x - UInt64.ofNat (2 ^ 64 - n) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_ofNat]
  omega

-- A counter that goes down (task LC-DOWN): `x - k` and `x + (2 ^ 64 - k)` with `k ≤ x` as `x.toNat - k`.
attribute [uint_norm] UInt64.toNat_sub_of_toNat_le BitVec.toNat_add_lit Nat.add_mod_of_sub_le UInt64.toNat_ofBitVec

attribute [uint_norm] UInt64.toNat_add UInt64.toNat_one UInt64.ofBitVec_zero_eq UInt64.add_zero
  UInt64.toNat_toBitVec UInt64.toNat_zero UInt64.zero_add UInt64.toNat_ofNat'
attribute [uint_norm high] UInt64.toNat_add_of_lt_size

attribute [uint_norm] UInt64.ofBitVec_eq_iff_eq_toBitVec UInt64.ofBitVec_ofNat' BitVec.ofNat_toNat_uint64
  UInt64.ofNat_add UInt64.ofNat_zero_eq UInt64.ofNat_one_eq UInt64.toBitVec_ofBitVec UInt64.toBitVec_zero

attribute [heap_load low] Lift.Sem.Heap.load_next_of_ends_zero Lift.Sem.Heap.load_val_of_endsV_zero

attribute [heap_load] Lift.Sem.Heap.load_val_of_endsV Lift.Sem.Heap.endsV_next Lift.Sem.Heap.chainVals_next

attribute [heap_load] Lift.Sem.Heap.load_words64_mul Lift.Sem.Heap.load_words64_head Lift.Sem.Heap.store_words64_head
  Lift.Sem.Heap.load_next_of_ends Lift.Sem.Heap.load_next_of_ends' Lift.Sem.Heap.chain_next Lift.Sem.Heap.ends_next
  List.length_cons

attribute [list_step] Lift.Sem.Heap.chain_next Lift.Sem.Heap.ends_next Lift.Sem.Heap.chain_zero
  Lift.Sem.Heap.endsV_next Lift.Sem.Heap.chainVals_next Lift.Sem.Heap.chainVals_zero Lift.Sem.Heap.chainVals_ofNat_zero
  Lift.Sem.Heap.chain_ofNat_zero
  Lift.Sem.Heap.endsFuel_zero_ptr Lift.Sem.Heap.ends_zero

attribute [heap_norm] Lift.Sem.Bridge.toObj_encode_words64 List.map_cons List.map_nil List.cons_append
  List.nil_append

attribute [list_step] List.drop_eq_getElem_cons List.drop_nil List.drop_length List.drop_eq_nil_of_le
  List.drop_zero
  List.sum_cons
  List.sum_nil UInt64.ofBitVec_add UInt64.add_assoc
  List.idxOf_cons List.idxOf_nil Option.getD_some beq_self_eq_true beq_iff_eq
  List.length_append List.length_take List.length_drop List.length_map List.length_range List.length_set
  List.set_take_append_cons List.take_succ_eq_append_getElem List.getElem_map List.getElem_range
  List.append_assoc List.singleton_append List.append_cancel_left_eq List.cons.injEq List.take_of_length_le
  List.append_nil List.mem_cons_self or_true true_or

-- The search of the empty prefix (`xs.take 0` at the exit of a loop that counts down to 0, task LC-DOWN).
attribute [list_step] List.take_zero List.zipIdx_nil List.reverse_nil List.find?_nil List.getElem?_eq_getElem

/-- One step of `find?` as an `ite`, so that `condNorm` of `loop_close` takes the branch that the test of `a` gives. -/
theorem List.find?_cons_eq_ite {α : Type} (p : α → Bool) (a : α) (l : List α) :
    (a :: l).find? p = if p a = true then some a else l.find? p := by
  cases h : p a <;> simp [List.find?_cons, h]

-- One step of the search of a prefix from the top (`(xs.take (j + 1)).zipIdx.reverse.find?` of a loop that counts down, with
-- `xs` the list of a `Vector`, task LC-SPEC): the last element of the prefix is the first one of the search.
attribute [list_step] List.find?_cons_eq_ite List.zipIdx_append List.zipIdx_singleton List.reverse_append
  List.reverse_singleton List.nil_append Vector.length_toList Vector.getElem_toList
