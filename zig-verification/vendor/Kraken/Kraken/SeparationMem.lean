module

public import Kraken.Mem
import all Kraken.Mem
public import Kraken.Separation
import all Kraken.Separation

public section

/-!
# Separation-logic interface to Kraken memory-access operations
-/

open Std
open Std.ExtHashMap
open List

private theorem Std.ExtHashMap.get_union_l_disjoint {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]
    (m1 m2 : ExtHashMap key value) (k : key) (v : value) (h_disj : m1.inter m2 = ∅) (h : m1.get? k = some v) :
    (m1.union m2).get? k = some v := by
  rw [get?_eq_getElem?] at h
  rw [get?_eq_getElem?, union_comm_of_disjoint m1 m2 h_disj]
  simp only [union_eq, getElem?_union, h, Option.some_or]

private theorem Std.ExtHashMap.union_union_override {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]
    (m1 m2 m3 : ExtHashMap key value) (h_sub : ∀ k, k ∈ m1 → k ∈ m3) :
    (m1.union m2).union m3 = m2.union m3 := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [union_eq]
  rw [getElem?_union, getElem?_union, getElem?_union]
  cases h3 : m3[k]?
  · have h_not_mem3 : ¬ k ∈ m3 := by
      intro h_mem
      have h_some := getElem?_eq_some_getElem h_mem
      rw [h3] at h_some
      contradiction
    have h_not_mem1 : ¬ k ∈ m1 := fun h => h_not_mem3 (h_sub k h)
    have h1 := getElem?_eq_none h_not_mem1
    rw [h1]
    cases h2 : m2[k]?
    · rfl
    · rfl
  · rfl

private theorem List.range_get_eq_map_some {α : Type} (l : List α) :
    (List.range l.length).map (fun i => if h : i < l.length then some (l.get ⟨i, h⟩) else none) = l.map some := by
  apply List.ext_get <;> simp

private theorem mem_At_samerange {w : Nat} (_bs bs : List UInt8) (a : BitVec w) (h_len : _bs.length = bs.length) (k : BitVec w) :
    (k ∈ bs.At a) = (k ∈ _bs.At a) := by
  exact propext (by simp [mem_At_iff, h_len])

private theorem disjoint_Atsame_l_same_r {w : Nat} (_bs bs : List UInt8) (a : BitVec w) (m2 : Mem w)
    (h_disj : (_bs.At a).inter m2 = ∅) (h_len : _bs.length = bs.length) :
    (bs.At a).inter m2 = ∅ := by
  simpa [eq_empty_iff_forall_not_mem, inter_eq, mem_inter_iff,
    mem_At_samerange _bs bs a h_len] using h_disj

namespace Mem

theorem loadBytes_sep {w : Nat} (bs : List UInt8) (a : BitVec w) (n : Nat) (R : Mem w → Prop) (m : Mem w)
    (Hsep : m =⋆ Eq (bs.At a) ⋆ R)
    (Hl : bs.length = n)
    (Hlw : n ≤ 2 ^ w) :
    m.loadBytes a n = some bs := by
  have ⟨m1, m2, h_union, h_inter, hm1, hR⟩ := Hsep
  subst hm1
  rw [← h_union]
  have h_get : ∀ i (h : i < n), ((bs.At a).union m2).get? (a + BitVec.ofNat w i) = some (bs.get ⟨i, Hl ▸ h⟩) := by
    intro i hi
    apply get_union_l_disjoint
    · exact h_inter
    · rw [get?_At_idx _ _ _ (by omega) (Hl.symm ▸ Hlw)]
      exact getElem?_eq_getElem (Hl ▸ hi)
  rw [Mem.loadBytes]
  rw [show (List.range n).map (fun i => ((bs.At a).union m2).get? (a + BitVec.ofNat w i)) =
           (List.range n).map (fun i => if h : i < n then some (bs.get ⟨i, Hl ▸ h⟩) else none) by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi; rw [dif_pos hi]; exact h_get i hi]
  cases Hl
  rw [List.range_get_eq_map_some]
  rw [List.allSome_map_some]

theorem storeBytes_sep {w : Nat} (a : BitVec w) (n : Nat) (_bs bs : List UInt8)
    (R : Mem w → Prop) (m : Mem w)
    (H : (m =⋆ Eq (_bs.At a) ⋆ R) ∧ _bs.length = n ∧ bs.length = n) :
    (m.storeBytes a bs) =⋆ Eq (bs.At a) ⋆ R := by
  have ⟨Hsep, h_len1, h_len2⟩ := H
  have ⟨m1, m2, h_union, h_inter, hm1, hR⟩ := Hsep
  subst hm1
  dsimp [storeBytes]
  rw [← h_union]
  rw [union_union_override (_bs.At a) m2 (bs.At a) (by
    intro k hk; rw [mem_At_samerange _bs bs a (by omega)]; exact hk)]
  rw [sep_comm]
  exact ⟨m2, bs.At a, rfl, disjoint_symm (disjoint_Atsame_l_same_r _bs bs a m2 h_inter (by omega)), hR, rfl⟩

theorem loadInt_sep {w : Nat} (bs : List UInt8) (a : BitVec w) (n : Nat) (R : Mem w → Prop) (m : Mem w)
    (Hsep : m =⋆ Eq (bs.At a) ⋆ R)
    (Hl : bs.length = n)
    (Hlw : n ≤ 2 ^ w) :
    m.loadInt a n = some (Int.ofBytes bs) := by
  simp [loadInt, loadBytes_sep bs a n R m Hsep Hl Hlw]

theorem storeInt_sep {w : Nat} (a : BitVec w) (n : Nat) (_bs : List UInt8)
    (R : Mem w → Prop) (m : Mem w)
    (H : (m =⋆ Eq (_bs.At a) ⋆ R) ∧ _bs.length = n) (v : Int) :
    m.storeInt a n v =⋆ Eq ((Int.toBytes n v).At a) ⋆ R := by
  simpa only [storeInt] using
    storeBytes_sep a n _bs (Int.toBytes n v) R m ⟨H.1, H.2, Int.toBytes_length n v⟩

theorem At_append_sep {w : Nat} (bs1 bs2 : List UInt8) (a : BitVec w)
    (h_len : bs1.length + bs2.length ≤ 2 ^ w) :
    Eq ((bs1 ++ bs2).At a) = Eq (bs1.At a) ⋆ Eq (bs2.At (a + .ofNat _ bs1.length)) := by
  funext m
  apply propext
  constructor
  · rintro rfl
    rw [List.At_append _ _ _ h_len]
    exact ⟨bs1.At a, bs2.At (a + BitVec.ofNat w bs1.length), rfl, List.disjoint_At_append _ _ _ h_len, rfl, rfl⟩
  · rintro ⟨m1, m2, h_union, h_disj, rfl, rfl⟩
    rw [← h_union]
    rw [← List.At_append _ _ _ h_len]


/-! ## Slices of a region

An access of `n` bytes at `addr` inside a region `bs.At a` touches the bytes at
offset `(addr - a).toNat`. The region splits around them, which reduces the
access to `loadInt_sep` or `storeInt_sep` with the rest of the region in the
frame. -/

/-- A region in three parts, split with the middle part first. -/
theorem At_append3_sep {w : Nat} (pre mid post : List UInt8) (a : BitVec w)
    (hlen : pre.length + mid.length + post.length ≤ 2 ^ w) :
    Eq ((pre ++ mid ++ post).At a)
      = Eq (mid.At (a + .ofNat w pre.length))
        ⋆ (Eq (pre.At a) ⋆ Eq (post.At (a + .ofNat w (pre.length + mid.length)))) := by
  rw [At_append_sep (pre ++ mid) post a (by simp; omega),
    At_append_sep pre mid a (by omega), sep_assoc, sep_comm_l]
  simp only [List.length_append]

private theorem add_ofNat_toNat_sub {w : Nat} (a addr : BitVec w) :
    a + BitVec.ofNat w (addr - a).toNat = addr := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- A region split around the `n` bytes at `addr` inside it: those bytes first,
then the bytes before and after them. -/
theorem At_slice_sep {w : Nat} (bs : List UInt8) (a addr : BitVec w) (n : Nat)
    (hin : (addr - a).toNat + n ≤ bs.length) (hw : bs.length ≤ 2 ^ w) :
    Eq (bs.At a)
      = Eq (((bs.drop (addr - a).toNat).take n).At addr)
        ⋆ (Eq ((bs.take (addr - a).toNat).At a)
          ⋆ Eq ((bs.drop ((addr - a).toNat + n)).At (addr + .ofNat w n))) := by
  have hsplit : bs = bs.take (addr - a).toNat ++ (bs.drop (addr - a).toNat).take n
      ++ bs.drop ((addr - a).toNat + n) := by
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have h1 : (bs.take (addr - a).toNat).length = (addr - a).toNat := by
    simp only [List.length_take]; omega
  have h2 : ((bs.drop (addr - a).toNat).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  conv => lhs; rw [hsplit]
  rw [At_append3_sep _ _ _ a (by simp only [List.length_take, List.length_drop]; omega), h1, h2,
    add_ofNat_toNat_sub, BitVec.ofNat_add, ← BitVec.add_assoc, add_ofNat_toNat_sub]

/-- A load inside a region reads the region's bytes there. -/
theorem loadInt_slice {w : Nat} {bs : List UInt8} {a addr : BitVec w} {n : Nat}
    {F : Mem w → Prop} {m : Mem w}
    (h : m =⋆ Eq (bs.At a) ⋆ F) (hin : (addr - a).toNat + n ≤ bs.length)
    (hw : bs.length ≤ 2 ^ w) :
    m.loadInt addr n = some (Int.ofBytes ((bs.drop (addr - a).toNat).take n)) := by
  rw [At_slice_sep bs a addr n hin hw, sep_assoc] at h
  exact loadInt_sep _ addr n _ m h (by simp only [List.length_take, List.length_drop]; omega)
    (by omega)

/-- A store inside a region writes its bytes into the region, which keeps its
length. -/
theorem storeInt_slice {w : Nat} {bs : List UInt8} {a addr : BitVec w} {n : Nat}
    {F : Mem w → Prop} {m : Mem w}
    (h : m =⋆ Eq (bs.At a) ⋆ F) (hin : (addr - a).toNat + n ≤ bs.length)
    (hw : bs.length ≤ 2 ^ w) (v : Int) :
    m.storeInt addr n v =⋆
      Eq ((bs.take (addr - a).toNat ++ Int.toBytes n v ++ bs.drop ((addr - a).toNat + n)).At a)
        ⋆ F := by
  have h1 : (bs.take (addr - a).toNat).length = (addr - a).toNat := by
    simp only [List.length_take]; omega
  have h2 : ((bs.drop (addr - a).toNat).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  rw [At_slice_sep bs a addr n hin hw, sep_assoc] at h
  have hst := storeInt_sep addr n _ _ m ⟨h, h2⟩ v
  rw [At_append3_sep _ _ _ a
      (by simp only [List.length_take, List.length_drop, Int.toBytes_length]; omega),
    sep_assoc, h1, Int.toBytes_length, add_ofNat_toNat_sub, BitVec.ofNat_add,
    ← BitVec.add_assoc, add_ofNat_toNat_sub]
  exact hst

/-! ## Blocks: owned regions with untracked contents

A program that moves data around without inspecting it (a copy, an in-place
update) needs to know which regions it owns, not what they hold. `Block a len`
owns the `len` bytes at `a`, whatever they are, and `Blocks` lists several,
separated from each other. A load or store inside a listed block is safe and
keeps the list, so an invariant says `s.dmem =⋆ Mem.Blocks [...] ⋆ R` and needs
nothing else about memory.

The load and store lemmas fire in `grind` on such a fact and an access.
Their side condition `Blocks.Inside` has one introduction rule per usual
address shape: the block's base, the base plus an offset, and the base plus
two offsets (a pointer into the block plus an index), with the base as the
first or the second term. `grind` applies a rule only when the address is
computed from that block's base, so it never has to rule out the other blocks.
A pointer that moves through a block, as in a loop, is not computed from the
base; its rule applies when the pointer's offset from the base is among the
terms, as it is when a loop invariant bounds it. -/

/-- An owned region of `len` bytes at `a`, whose contents are not tracked. -/
def Block {w : Nat} (a : BitVec w) (len : Nat) (h : Mem w) : Prop :=
  len ≤ 2 ^ w ∧ ∃ bs : List UInt8, bs.length = len ∧ bs.At a = h

/-- A block is a region with some contents of its length. -/
theorem Block.sep_elim {w : Nat} {a : BitVec w} {len : Nat} {F : Mem w → Prop} {m : Mem w}
    (h : m =⋆ Block a len ⋆ F) :
    len ≤ 2 ^ w ∧ ∃ bs : List UInt8, bs.length = len ∧ m =⋆ Eq (bs.At a) ⋆ F := by
  obtain ⟨m1, m2, hu, hi, ⟨hw, bs, hlen, rfl⟩, hF⟩ := h
  exact ⟨hw, bs, hlen, _, m2, hu, hi, rfl, hF⟩

/-- A region is a block of its length, forgetting the contents. -/
theorem Block.sep_intro {w : Nat} {a : BitVec w} {len : Nat} {F : Mem w → Prop} {m : Mem w}
    {bs : List UInt8} (hlen : bs.length = len) (hw : len ≤ 2 ^ w)
    (h : m =⋆ Eq (bs.At a) ⋆ F) : m =⋆ Block a len ⋆ F := by
  obtain ⟨m1, m2, hu, hi, rfl, hF⟩ := h
  exact ⟨_, m2, hu, hi, ⟨hw, bs, hlen, rfl⟩, hF⟩

/-- A load inside a block succeeds. -/
theorem Block.loadInt_isSome {w : Nat} {a addr : BitVec w} {len n : Nat} {F : Mem w → Prop}
    {m : Mem w} (h : m =⋆ Block a len ⋆ F) (hin : (addr - a).toNat + n ≤ len) :
    (m.loadInt addr n).isSome = true := by
  obtain ⟨hw, bs, rfl, h'⟩ := Block.sep_elim h
  rw [loadInt_slice h' hin hw]
  rfl

/-- A store inside a block keeps the block. -/
theorem Block.storeInt {w : Nat} {a addr : BitVec w} {len n : Nat} {F : Mem w → Prop}
    {m : Mem w} (h : m =⋆ Block a len ⋆ F) (hin : (addr - a).toNat + n ≤ len) (v : Int) :
    m.storeInt addr n v =⋆ Block a len ⋆ F := by
  obtain ⟨hw, bs, rfl, h'⟩ := Block.sep_elim h
  exact Block.sep_intro
    (by simp only [List.length_append, List.length_take, List.length_drop, Int.toBytes_length]
        omega)
    hw (storeInt_slice h' hin hw v)

/-- Blocks separated from each other, as `(base, length)` pairs:
`Blocks [(a₁, l₁), (a₂, l₂)]` is `Block a₁ l₁ ⋆ Block a₂ l₂`. -/
def Blocks {w : Nat} : List (BitVec w × Nat) → Mem w → Prop
  | [] => emp
  | [(a, len)] => Block a len
  | (a, len) :: b :: bs => Block a len ⋆ Blocks (b :: bs)

/-- The `n` bytes at `addr` lie inside one of the blocks. -/
def Blocks.Inside {w : Nat} (addr : BitVec w) (n : Nat) : List (BitVec w × Nat) → Prop
  | [] => False
  | (a, len) :: bs => (addr - a).toNat + n ≤ len ∨ Blocks.Inside addr n bs

/-- An access inside a later block is inside the list. -/
theorem Blocks.Inside.tail {w : Nat} {addr : BitVec w} {n : Nat} {p q : BitVec w × Nat}
    {bs : List (BitVec w × Nat)} (h : Blocks.Inside addr n (q :: bs)) :
    Blocks.Inside addr n (p :: q :: bs) := by
  obtain ⟨a, len⟩ := p
  exact Or.inr h

/-- An access at a block's base. -/
theorem Blocks.Inside.base {w : Nat} {a : BitVec w} {n len : Nat} {bs : List (BitVec w × Nat)}
    (h : n ≤ len) : Blocks.Inside a n ((a, len) :: bs) :=
  Or.inl (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega)

/-- An access at an offset `x` from a block's base. -/
theorem Blocks.Inside.base_add {w : Nat} {a x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : x.toNat + n ≤ len) :
    Blocks.Inside (a + x) n ((a, len) :: bs) :=
  Or.inl (by rw [BitVec.add_comm, BitVec.add_sub_cancel]; exact h)

theorem Blocks.Inside.add_base {w : Nat} {a x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : x.toNat + n ≤ len) :
    Blocks.Inside (x + a) n ((a, len) :: bs) :=
  Or.inl (by rw [BitVec.add_sub_cancel]; exact h)

theorem Blocks.Inside.base_add_sub {w : Nat} {a x y : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (x - y).toNat + n ≤ len) :
    Blocks.Inside (a + x - y) n ((a, len) :: bs) :=
  Or.inl (by rw [show a + x - y - a = x - y by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_comm a,
      BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (-y), ← BitVec.add_assoc a,
      ← BitVec.sub_eq_add_neg a a, BitVec.sub_self, BitVec.zero_add]]; exact h)

/-- An access at two offsets `c` and `x` from a block's base, such as a pointer
into the block plus an index. -/
theorem Blocks.Inside.base_add_add {w : Nat} {a c x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : c.toNat + x.toNat + n ≤ len) :
    Blocks.Inside (a + c + x) n ((a, len) :: bs) :=
  Or.inl (by
    rw [BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_add]
    have := Nat.mod_le (c.toNat + x.toNat) (2 ^ w)
    omega)

/-- An access at offsets `c` and `x` around a block's base, as `c + a + x`: an
operand whose index register holds the pointer to the block, such as
`16(%rcx,%rsi,1)` for the block at `rsi`. -/
theorem Blocks.Inside.add_base_add {w : Nat} {a c x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : c.toNat + x.toNat + n ≤ len) :
    Blocks.Inside (c + a + x) n ((a, len) :: bs) :=
  Or.inl (by
    rw [BitVec.add_comm c a, BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel,
      BitVec.toNat_add]
    have := Nat.mod_le (c.toNat + x.toNat) (2 ^ w)
    omega)

theorem Blocks.Inside.base_add_add_wrap {w : Nat} {a c x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (c + x).toNat + n ≤ len) :
    Blocks.Inside (a + c + x) n ((a, len) :: bs) :=
  Or.inl (by rw [BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel]; exact h)

theorem Blocks.Inside.add_base_add_wrap {w : Nat} {a c x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (c + x).toNat + n ≤ len) :
    Blocks.Inside (c + a + x) n ((a, len) :: bs) :=
  Or.inl (by
    rw [BitVec.add_comm c a, BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel]
    exact h)

theorem Blocks.Inside.sub {w : Nat} {a p x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (hx : x.toNat ≤ (p - a).toNat) (h : (p - a).toNat - x.toNat + n ≤ len) :
    Blocks.Inside (p - x) n ((a, len) :: bs) := by
  refine Or.inl ?_
  rw [show p - x - a = (p - a) - x by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, BitVec.add_comm (-x), ← BitVec.add_assoc], BitVec.toNat_sub_of_le hx]
  exact h

theorem Blocks.Inside.sub_sub {w : Nat} {a p x y : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (hx : x.toNat + y.toNat ≤ (p - a).toNat)
    (h : (p - a).toNat - x.toNat - y.toNat + n ≤ len) :
    Blocks.Inside (p - x - y) n ((a, len) :: bs) := by
  have hpx : (p - x - a).toNat = (p - a).toNat - x.toNat := by
    rw [show p - x - a = (p - a) - x by
      rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
        BitVec.add_assoc, BitVec.add_comm (-x), ← BitVec.add_assoc],
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
  exact Blocks.Inside.sub (by omega) (by omega)

theorem Blocks.Inside.mono {w : Nat} {addr a : BitVec w} {n len len' : Nat}
    {bs : List (BitVec w × Nat)} (h : Blocks.Inside addr n ((a, len) :: bs)) (hl : len ≤ len') :
    Blocks.Inside addr n ((a, len') :: bs) :=
  h.imp (fun h => by omega) id

/-- An access at an offset `x` from a pointer `p` into a block, given the
pointer's offset `p - a` from the base: the form in which a loop invariant
tracks a moving pointer. -/
theorem Blocks.Inside.ptr_add {w : Nat} {a p x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (p - a).toNat + x.toNat + n ≤ len) :
    Blocks.Inside (p + x) n ((a, len) :: bs) := by
  refine Or.inl ?_
  have hsum : p + x - a = (p - a) + x := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm x,
      ← BitVec.add_assoc]
  rw [hsum, BitVec.toNat_add]
  have := Nat.mod_le ((p - a).toNat + x.toNat) (2 ^ w)
  omega

theorem Blocks.Inside.ptr {w : Nat} {a p : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (p - a).toNat + n ≤ len) :
    Blocks.Inside p n ((a, len) :: bs) := by
  simpa using Blocks.Inside.ptr_add (x := 0#w) (bs := bs) (by simpa using h)

/-- A load inside one of the blocks succeeds. -/
theorem Blocks.loadInt_isSome {w : Nat} {bs : List (BitVec w × Nat)} {F : Mem w → Prop}
    {m : Mem w} {addr : BitVec w} {n : Nat}
    (h : m =⋆ Blocks bs ⋆ F) (hin : Blocks.Inside addr n bs) :
    (m.loadInt addr n).isSome = true := by
  induction bs generalizing F with
  | nil => exact hin.elim
  | cons p bs ih =>
    obtain ⟨a, len⟩ := p
    cases bs with
    | nil =>
      rcases hin with hin | hin
      · exact Block.loadInt_isSome h hin
      · exact hin.elim
    | cons q bs =>
      have h' : m =⋆ Block a len ⋆ (Blocks (q :: bs) ⋆ F) := by
        rw [← sep_assoc]; exact h
      rcases hin with hin | hin
      · exact Block.loadInt_isSome h' hin
      · rw [sep_comm_l] at h'
        exact ih h' hin

/-- A store inside one of the blocks keeps all of them. -/
theorem Blocks.storeInt {w : Nat} {bs : List (BitVec w × Nat)} {F : Mem w → Prop}
    {m : Mem w} {addr : BitVec w} {n : Nat}
    (h : m =⋆ Blocks bs ⋆ F) (hin : Blocks.Inside addr n bs) (v : Int) :
    m.storeInt addr n v =⋆ Blocks bs ⋆ F := by
  induction bs generalizing F with
  | nil => exact hin.elim
  | cons p bs ih =>
    obtain ⟨a, len⟩ := p
    cases bs with
    | nil =>
      rcases hin with hin | hin
      · exact Block.storeInt h hin v
      · exact hin.elim
    | cons q bs =>
      have h' : m =⋆ Block a len ⋆ (Blocks (q :: bs) ⋆ F) := by
        rw [← sep_assoc]; exact h
      show (Block a len ⋆ Blocks (q :: bs) ⋆ F) (m.storeInt addr n v)
      rw [sep_assoc]
      rcases hin with hin | hin
      · exact Block.storeInt h' hin v
      · rw [sep_comm_l] at h' ⊢
        exact ih h' hin

grind_pattern Blocks.Inside.tail => Blocks.Inside addr n (p :: q :: bs)
grind_pattern Blocks.Inside.base => Blocks.Inside a n ((a, len) :: bs)
grind_pattern Blocks.Inside.base_add => Blocks.Inside (a + x) n ((a, len) :: bs)
grind_pattern Blocks.Inside.add_base => Blocks.Inside (x + a) n ((a, len) :: bs)
grind_pattern Blocks.Inside.base_add_sub => Blocks.Inside (a + x - y) n ((a, len) :: bs)
grind_pattern Blocks.Inside.base_add_add => Blocks.Inside (a + c + x) n ((a, len) :: bs)
grind_pattern Blocks.Inside.sub => Blocks.Inside (p - x) n ((a, len) :: bs), p - a
grind_pattern Blocks.Inside.sub_sub => Blocks.Inside (p - x - y) n ((a, len) :: bs), p - a
grind_pattern Blocks.Inside.mono => Blocks.Inside addr n ((a, len) :: bs), Blocks.Inside addr n ((a, len') :: bs) where
  len =/= len'
grind_pattern Blocks.Inside.add_base_add => Blocks.Inside (c + a + x) n ((a, len) :: bs)
grind_pattern Blocks.Inside.base_add_add_wrap => Blocks.Inside (a + c + x) n ((a, len) :: bs)
grind_pattern Blocks.Inside.add_base_add_wrap => Blocks.Inside (c + a + x) n ((a, len) :: bs)
-- The pointer rule also needs the offset `p - a` among the terms, which an
-- invariant about the pointer puts there. Otherwise any pointer into any block
-- would match, and ruling out the wrong blocks swamps the arithmetic.
grind_pattern Blocks.Inside.ptr_add => Blocks.Inside (p + x) n ((a, len) :: bs), p - a
grind_pattern Blocks.Inside.ptr => Blocks.Inside p n ((a, len) :: bs), p - a
grind_pattern Blocks.loadInt_isSome => sep (Blocks bs) F m, Mem.loadInt m addr n
grind_pattern Blocks.storeInt => sep (Blocks bs) F m, Mem.storeInt m addr n v



/-! ## Copying into a block: `Blocks` owns the destination, `loadBytes` tracks contents -/

@[grind =] theorem _root_.List.getElem!_drop' (l : List UInt8) (k i : Nat) :
    (l.drop k)[i]! = l[k + i]! := by
  simp only [getElem!_def, List.getElem?_drop]

@[grind =] theorem _root_.List.getElem!_take' (l : List UInt8) (r i : Nat) (h : i < r) :
    (l.take r)[i]! = l[i]! := by
  simp only [getElem!_def, List.getElem?_take, ite_eq_left h]

@[grind =] theorem _root_.Int.toBytes_one_byte (b : UInt8) :
    Int.toBytes 1 (BitVec.ofInt 8 (b.toNat : Int)).toInt = [b] := by
  have hb := b.toNat_lt
  have h : (BitVec.ofInt 8 (b.toNat : Int)).toInt.take 8 = b.toNat := by
    rw [Int.take, BitVec.toInt_ofInt, show ((2 : Int) ^ 8) = ((2 ^ 8 : Nat) : Int) by norm_cast,
      Int.bmod_emod]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  simp only [Int.toBytes, h, Int.toNat_natCast, List.cons.injEq, and_true]
  simp

/-- The owned bytes `bs` at `a`. -/
def Bytes {w : Nat} (a : BitVec w) (bs : List UInt8) : Mem w → Prop := Eq (bs.At a)

private theorem Blocks_cons_sep {w : Nat} (a : BitVec w) (len : Nat) (l : List (BitVec w × Nat))
    (F : Mem w → Prop) : Blocks ((a, len) :: l) ⋆ F = Block a len ⋆ (Blocks l ⋆ F) := by
  cases l with
  | nil => rw [Blocks, Blocks, emp_sep]
  | cons b l => rw [Blocks, sep_assoc]

theorem Blocks.storeInt_head {w : Nat} {a : BitVec w} {n : Nat} {l : List (BitVec w × Nat)}
    {F : Mem w → Prop} {m : Mem w} (h : m =⋆ Blocks ((a, n) :: l) ⋆ F) (v : Int) :
    m.storeInt a n v =⋆ Bytes a (Int.toBytes n v) ⋆ Blocks l ⋆ F := by
  rw [Blocks_cons_sep] at h
  obtain ⟨-, ys, hys, h⟩ := Block.sep_elim h
  rw [Bytes, sep_assoc]
  exact storeInt_sep a n ys _ m ⟨h, hys⟩ v

theorem Blocks.storeInt₂ {w : Nat} {P F : Mem w → Prop} {bs : List (BitVec w × Nat)} {m : Mem w}
    {addr : BitVec w} {n : Nat} (h : m =⋆ P ⋆ Blocks bs ⋆ F) (hin : Blocks.Inside addr n bs)
    (v : Int) : m.storeInt addr n v =⋆ P ⋆ Blocks bs ⋆ F := by
  rw [sep_assoc, sep_comm_l] at h ⊢
  exact Blocks.storeInt h hin v

theorem Blocks.loadInt_isSome₂ {w : Nat} {P F : Mem w → Prop} {bs : List (BitVec w × Nat)}
    {m : Mem w} {addr : BitVec w} {n : Nat} (h : m =⋆ P ⋆ Blocks bs ⋆ F)
    (hin : Blocks.Inside addr n bs) : (m.loadInt addr n).isSome = true := by
  rw [sep_assoc, sep_comm_l] at h
  exact Blocks.loadInt_isSome h hin

theorem Bytes.loadInt₂ {w : Nat} {a : BitVec w} {bs : List UInt8} {n : Nat} {G F : Mem w → Prop}
    {m : Mem w} (h : m =⋆ Bytes a bs ⋆ G ⋆ F) (hn : bs.length = n) (hw : n ≤ 2 ^ w) :
    m.loadInt a n = some (Int.ofBytes bs) := by
  rw [Bytes, sep_assoc] at h
  exact loadInt_sep bs a n _ m h hn hw

theorem loadBytes_eq_some_iff {w : Nat} {m : Mem w} {a : BitVec w} {n : Nat} {bs : List UInt8} :
    m.loadBytes a n = some bs ↔
      bs.length = n ∧ ∀ i (h : i < bs.length), m.get? (a + .ofNat w i) = some bs[i] := by
  refine ⟨fun h => ?_, fun ⟨hn, h⟩ => ?_⟩
  · have hl := List.allSome_eq_map_some h
    have hlen : bs.length = n := by simpa using (congrArg List.length hl).symm
    refine ⟨hlen, fun i hi => ?_⟩
    have := congrArg (·[i]?) hl
    simpa [List.getElem?_map, List.getElem?_range (hlen ▸ hi), List.getElem?_eq_getElem hi] using this
  · subst hn
    rw [Mem.loadBytes, List.map_congr_left (fun i hi => (h i (List.mem_range.mp hi)).trans
      (List.getElem?_eq_getElem (List.mem_range.mp hi)).symm), List.map_range_getElem?,
      List.allSome_map_some]

theorem length_of_loadBytes_eq_some {w : Nat} {m : Mem w} {a : BitVec w} {n : Nat}
    {bs : List UInt8} (h : m.loadBytes a n = some bs) : bs.length = n :=
  (loadBytes_eq_some_iff.mp h).1

def Contains {w : Nat} (m : Mem w) (a : BitVec w) (bs : List UInt8) : Prop :=
  m.loadBytes a bs.length = some bs

theorem Contains.iff {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8} :
    Contains m a bs ↔ ∀ i (h : i < bs.length), m.get? (a + .ofNat w i) = some bs[i] := by
  rw [Contains, loadBytes_eq_some_iff]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem Contains.of_length {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8}
    (h : bs.length = 0) : Contains m a bs := Contains.iff.mpr fun i hi => by omega

theorem Contains.loadInt {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    (h : Contains m a bs) (hi : (addr - a).toNat < bs.length) :
    m.loadInt addr 1 = some (bs[(addr - a).toNat]!.toNat : Int) := by
  have := Contains.iff.mp h _ hi
  rw [add_ofNat_toNat_sub] at this
  rw [Mem.loadInt_one, this, getElem!_pos bs _ hi]
  rfl

theorem Contains.loadInt_take {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    {r : Nat} (h : Contains m a (bs.take r)) (hi : (addr - a).toNat < r) (hr : r ≤ bs.length) :
    m.loadInt addr 1 = some (bs[(addr - a).toNat]!.toNat : Int) := by
  rw [h.loadInt (by simp only [List.length_take]; omega), List.getElem!_take' _ _ _ hi]

theorem Contains.loadInt_head {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8}
    (h : Contains m a bs) (hi : 0 < bs.length) : m.loadInt a 1 = some (bs[0]!.toNat : Int) := by
  have := h.loadInt (addr := a) (by rw [BitVec.sub_self, BitVec.toNat_zero]; exact hi)
  rwa [BitVec.sub_self, BitVec.toNat_zero] at this

theorem Contains.storeInt {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    (h : Contains m a bs) (hd : bs.length ≤ (addr - a).toNat) (v : Int) :
    Contains (m.storeInt addr 1 v) a bs := Contains.iff.mpr fun i hi => by
  rw [Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj he => ?_]
  · exact Contains.iff.mp h i hi
  · have hj0 : j = 0 := by omega
    subst hj0
    rw [BitVec.add_zero] at he
    rw [← he, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at hd
    have := Nat.mod_le i (2 ^ w)
    omega

theorem Contains.consume {w : Nat} {m : Mem w} {a a' addr : BitVec w} {bs : List UInt8}
    {k k' : Nat} (h : Contains m a (bs.drop k)) (hk : k' = k + 1) (ha : a' = a + 1)
    (hd : bs.length - k' ≤ (addr - a').toNat) (v : Int) :
    Contains (m.storeInt addr 1 v) a' (bs.drop k') := by
  refine Contains.storeInt (Contains.iff.mpr fun i hi => ?_) (by simpa using hd) v
  have hi' : i + 1 < (bs.drop k).length := by simp only [List.length_drop] at hi ⊢; omega
  have := Contains.iff.mp h (i + 1) hi'
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat w i), ← BitVec.add_assoc] at this
  subst hk ha
  have e : k + (i + 1) = k + 1 + i := by omega
  simp only [List.getElem_drop, e] at this ⊢
  exact this

theorem Contains.consume_back {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    {r r' : Nat} (h : Contains m a (bs.take r)) (hr : r' + 1 = r)
    (hd : r' ≤ (addr - a).toNat) (v : Int) :
    Contains (m.storeInt addr 1 v) a (bs.take r') := by
  refine Contains.storeInt (Contains.iff.mpr fun i hi => ?_) (by simp only [List.length_take]; omega) v
  have hi' : i < (bs.take r).length := by simp only [List.length_take] at hi ⊢; omega
  simpa only [List.getElem_take] using Contains.iff.mp h i hi'

theorem Contains.extend {w : Nat} {m : Mem w} {a p : BitVec w} {bs : List UInt8} {k k' : Nat}
    (h : Contains m a (bs.take k)) (hk : k' = k + 1) (hp : p = a + .ofNat w k)
    (hkl : k < bs.length) (hw : bs.length ≤ 2 ^ w) {v : Int} (hv : Int.toBytes 1 v = [bs[k]!]) :
    Contains (m.storeInt p 1 v) a (bs.take k') := Contains.iff.mpr fun i hi => by
  subst hk
  have hi' : i < k + 1 := by simp only [List.length_take] at hi; omega
  rw [Mem.get?_storeInt_one]
  by_cases hik : i = k
  · subst hik
    rw [ite_eq_left hp.symm]
    have h1 : ((Int.toBytes 1 v)[0]'(by rw [Int.toBytes_length]; omega)) = (v.take 8).toNat.toUInt8 := rfl
    simp only [hv, List.getElem_cons_zero, List.getElem_take] at h1 ⊢
    rw [← h1, getElem!_pos bs _ hkl]
  · have hne : a + BitVec.ofNat w i ≠ p := fun he => hik (by
      rw [hp] at he
      have h2 := congrArg (fun x => BitVec.toNat (x - a)) he
      simp only [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at h2
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2)
    rw [ite_eq_right hne]
    have := Contains.iff.mp h i (by simp only [List.length_take]; omega)
    simpa only [List.getElem_take] using this

theorem Contains.extend_back {w : Nat} {m : Mem w} {b q : BitVec w} {bs : List UInt8} {r r' : Nat}
    (h : Contains m b (bs.drop r)) (hr : r' + 1 = r) (hb : b = q + 1) (hrl : r ≤ bs.length)
    (hw : bs.length ≤ 2 ^ w) {v : Int} (hv : Int.toBytes 1 v = [bs[r']!]) :
    Contains (m.storeInt q 1 v) q (bs.drop r') := Contains.iff.mpr fun i hi => by
  subst hr hb
  rw [Mem.get?_storeInt_one]
  by_cases hi0 : i = 0
  · subst hi0
    rw [BitVec.add_zero, ite_eq_left rfl]
    have h1 : ((Int.toBytes 1 v)[0]'(by rw [Int.toBytes_length]; omega)) = (v.take 8).toNat.toUInt8 := rfl
    simp only [hv, List.getElem_cons_zero] at h1
    simp only [List.getElem_drop, Nat.add_zero]
    rw [← getElem!_pos bs r' (by omega), h1]
  · have hne : q + BitVec.ofNat w i ≠ q := fun he => hi0 (by
      have h2 := congrArg (fun x => BitVec.toNat (x - q)) he
      simp only [BitVec.add_comm q, BitVec.add_sub_cancel, BitVec.sub_self, BitVec.toNat_ofNat] at h2
      simp only [List.length_drop] at hi
      rwa [Nat.mod_eq_of_lt (by omega)] at h2)
    rw [ite_eq_right hne]
    have := Contains.iff.mp h (i - 1) (by simp only [List.length_drop] at hi ⊢; omega)
    rw [show q + 1 + BitVec.ofNat w (i - 1) = q + BitVec.ofNat w i by
      rw [BitVec.add_assoc, show (1 : BitVec w) = BitVec.ofNat w 1 from rfl, ← BitVec.ofNat_add,
        show 1 + (i - 1) = i by omega]] at this
    simpa only [List.getElem_drop, show r' + 1 + (i - 1) = r' + i by omega] using this

theorem Contains.loadBytes_eq {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8} {n : Nat}
    (h : Contains m a bs) (hn : bs.length = n) : m.loadBytes a n = some bs := hn ▸ h

theorem Contains.loadInt_eq {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8} {n : Nat}
    (h : Contains m a bs) (hn : bs.length = n) : m.loadInt a n = some (Int.ofBytes bs) := by
  rw [Mem.loadInt, h.loadBytes_eq hn]; rfl

theorem Contains.of_sep {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8} {F : Mem w → Prop}
    (h : m =⋆ Bytes a bs ⋆ F) (hw : bs.length ≤ 2 ^ w) : Contains m a bs :=
  loadBytes_sep bs a bs.length _ m h rfl hw

attribute [grind =] Int.toBytes_length

grind_pattern Blocks.storeInt_head => sep (Blocks ((a, n) :: l)) F m, Mem.storeInt m a n v
grind_pattern Blocks.loadInt_isSome₂ => sep (sep P (Blocks bs)) F m, Mem.loadInt m addr n
grind_pattern Blocks.storeInt₂ => sep (sep P (Blocks bs)) F m, Mem.storeInt m addr n v
grind_pattern Bytes.loadInt₂ => sep (sep (Bytes a bs) G) F m, Mem.loadInt m a n
grind_pattern Contains.of_length => Contains m a bs
grind_pattern Contains.loadInt_take => Contains m a (List.take r bs), Mem.loadInt m addr 1
grind_pattern Contains.loadInt_head => Contains m a bs, Mem.loadInt m a 1
grind_pattern Contains.consume => Contains m a (List.drop k bs),
  Contains (Mem.storeInt m addr 1 v) a' (List.drop k' bs)
grind_pattern Contains.consume_back => Contains m a (List.take r bs),
  Contains (Mem.storeInt m addr 1 v) a (List.take r' bs)
grind_pattern Contains.extend => Contains m a (List.take k bs),
  Contains (Mem.storeInt m p 1 v) a (List.take k' bs)
grind_pattern Contains.extend_back => Contains m b (List.drop r bs),
  Contains (Mem.storeInt m q 1 v) q (List.drop r' bs)
grind_pattern Contains.loadBytes_eq => Contains m a bs, Mem.loadBytes m a n

def UnchangedOutside {w : Nat} (bs : List (BitVec w × Nat)) (m m' : Mem w) : Prop :=
  ∀ b, ¬ Blocks.Inside b 1 bs → m'.get? b = m.get? b

theorem unchangedOutside_iff {w : Nat} (bs : List (BitVec w × Nat)) (m m' : Mem w) :
    UnchangedOutside bs m m' ↔ ∀ b, ¬ Blocks.Inside b 1 bs → m'.get? b = m.get? b := Iff.rfl

def DomainGrows {w : Nat} (m m' : Mem w) : Prop :=
  ∀ b, (m.get? b).isSome → (m'.get? b).isSome

def WritesOnly {w : Nat} (bs : List (BitVec w × Nat)) (m m' : Mem w) : Prop :=
  UnchangedOutside bs m m' ∧ DomainGrows m m'

def Mapped {w : Nat} (bs : List (BitVec w × Nat)) (m : Mem w) : Prop :=
  ∀ b, Blocks.Inside b 1 bs → (m.get? b).isSome

theorem Blocks.mapped {w : Nat} {bs : List (BitVec w × Nat)} {F : Mem w → Prop} {m : Mem w}
    (h : m =⋆ Blocks bs ⋆ F) : Mapped bs m := fun b hb => by
  have := Blocks.loadInt_isSome h hb
  rw [Mem.loadInt_one] at this
  simpa using this

theorem UnchangedOutside.loadInt_singleton {w : Nat} {m m' : Mem w} {a b : BitVec w} {n len : Nat}
    (h : UnchangedOutside [(b, len)] m m') (hl : len ≤ (a - b).toNat) (hw : (a - b).toNat + n ≤ 2 ^ w) :
    m'.loadInt a n = m.loadInt a n := by
  simp only [Mem.loadInt, Mem.loadBytes]
  rw [List.map_congr_left (fun i hi => h _ fun hin => ?_)]
  have hi := List.mem_range.mp hi
  rcases hin with hin | hin
  · rw [show a + BitVec.ofNat w i - b = (a - b) + BitVec.ofNat w i by
      rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm _ (-b),
        ← BitVec.add_assoc], BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)] at hin
    omega
  · exact hin

grind_pattern UnchangedOutside.loadInt_singleton => UnchangedOutside [(b, len)] m m', Mem.loadInt m' a n

def Blocks.Disjoint {w : Nat} (bs bs' : List (BitVec w × Nat)) : Prop :=
  ∀ b, Blocks.Inside b 1 bs → ¬ Blocks.Inside b 1 bs'

theorem Blocks.Inside.add_ofNat {w : Nat} {bs : List (BitVec w × Nat)} {addr : BitVec w}
    {n i : Nat} (hin : Blocks.Inside addr n bs) (hi : i < n) :
    Blocks.Inside (addr + BitVec.ofNat w i) 1 bs := by
  induction bs with
  | nil => exact hin.elim
  | cons p bs ih =>
    obtain ⟨a, len⟩ := p
    rcases hin with h | h
    · left
      rw [show addr + BitVec.ofNat w i - a = (addr - a) + BitVec.ofNat w i by
        rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm _ (-a),
          ← BitVec.add_assoc]]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := Nat.mod_le ((addr - a).toNat + i % 2 ^ w) (2 ^ w)
      have := Nat.mod_le i (2 ^ w)
      omega
    · exact Or.inr (ih h)

theorem Blocks.Inside.get?_storeInt {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w}
    {addr b : BitVec w} {n : Nat} (hin : Blocks.Inside addr n bs) (hb : ¬ Blocks.Inside b 1 bs)
    (v : Int) : (m.storeInt addr n v).get? b = m.get? b :=
  Mem.get?_storeInt_of_ne _ _ _ _ _ fun _ hi he => hb (he ▸ hin.add_ofNat hi)

theorem Mapped.loadBytes_isSome {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w}
    {addr : BitVec w} {n : Nat} (h : Mapped bs m) (hin : Blocks.Inside addr n bs) :
    (m.loadBytes addr n).isSome = true := by
  have hl : ∀ l : List Nat, (∀ i ∈ l, i < n) →
      ((l.map fun i => m.get? (addr + BitVec.ofNat w i)).mapM id).isSome = true := by
    intro l hl
    induction l with
    | nil => rfl
    | cons i l ih =>
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h _ (hin.add_ofNat (hl i (List.mem_cons_self ..))))
      obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp
        (ih fun j hj => hl j (List.mem_cons_of_mem _ hj))
      simp only [List.map_cons, List.mapM_cons, id, hx, hxs]
      rfl
  simpa only [Mem.loadBytes, List.allSome] using hl (List.range n) fun i hi => List.mem_range.mp hi

theorem Mapped.loadBytes_eq_some_get! {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w}
    {addr : BitVec w} {n : Nat} (h : Mapped bs m) (hin : Blocks.Inside addr n bs) :
    m.loadBytes addr n = some (m.loadBytes addr n).get! :=
  (Option.some_get! _ (h.loadBytes_isSome hin)).symm

theorem Mapped.loadInt_isSome {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w}
    {addr : BitVec w} {n : Nat} (h : Mapped bs m) (hin : Blocks.Inside addr n bs) :
    (m.loadInt addr n).isSome = true := by
  simpa only [Mem.loadInt, Option.isSome_map] using h.loadBytes_isSome hin

theorem DomainGrows.storeInt {w : Nat} (m : Mem w) (a : BitVec w) (n : Nat) (v : Int) :
    DomainGrows m (m.storeInt a n v) := fun b hm => by
  rw [Mem.storeInt, Mem.storeBytes, get?_eq_getElem?, ExtHashMap.union_eq, ExtHashMap.getElem?_union]
  rw [get?_eq_getElem?] at hm
  cases ((Int.toBytes n v).At a)[b]? <;> simp_all

theorem Mapped.storeInt {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w} (h : Mapped bs m)
    (a : BitVec w) (n : Nat) (v : Int) : Mapped bs (m.storeInt a n v) := fun b hb =>
  DomainGrows.storeInt m a n v b (h b hb)

theorem Mapped.contains_get! {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w}
    {addr : BitVec w} {n : Nat} (h : Mapped bs m) (hin : Blocks.Inside addr n bs) :
    Contains m addr (m.loadBytes addr n).get! ∧ (m.loadBytes addr n).get!.length = n := by
  have h' := h.loadBytes_eq_some_get! hin
  have hl := length_of_loadBytes_eq_some h'
  exact ⟨by rw [Contains, hl]; exact h', hl⟩

theorem Contains.storeInt_of_disjoint {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    {n : Nat} {bs₁ bs₂ : List (BitVec w × Nat)} (h : Contains m a bs)
    (hin : Blocks.Inside addr n bs₁) (hd : Blocks.Disjoint bs₁ bs₂)
    (ha : Blocks.Inside a bs.length bs₂) (v : Int) : Contains (m.storeInt addr n v) a bs :=
  Contains.iff.mpr fun i hi => by
    rw [hin.get?_storeInt (fun hb => hd _ hb (ha.add_ofNat hi)) v]
    exact Contains.iff.mp h i hi

theorem Contains.storeInt_of_disjoint' {w : Nat} {m : Mem w} {a addr : BitVec w} {bs : List UInt8}
    {n : Nat} {bs₁ bs₂ : List (BitVec w × Nat)} (h : Contains m a bs)
    (hin : Blocks.Inside addr n bs₁) (hd : Blocks.Disjoint bs₂ bs₁)
    (ha : Blocks.Inside a bs.length bs₂) (v : Int) : Contains (m.storeInt addr n v) a bs :=
  Contains.iff.mpr fun i hi => by
    rw [hin.get?_storeInt (fun hb => hd _ (ha.add_ofNat hi) hb) v]
    exact Contains.iff.mp h i hi

grind_pattern Mapped.contains_get! => Mapped bs m, Option.get! (Mem.loadBytes m addr n)
grind_pattern Contains.storeInt_of_disjoint => Contains m a bs, Mem.storeInt m addr n v, Blocks.Disjoint bs₁ bs₂ where
  guard Blocks.Disjoint bs₁ bs₂
grind_pattern Contains.storeInt_of_disjoint' => Contains m a bs, Mem.storeInt m addr n v, Blocks.Disjoint bs₂ bs₁ where
  guard Blocks.Disjoint bs₂ bs₁

grind_pattern Blocks.Inside.get?_storeInt => Std.ExtHashMap.get? (Mem.storeInt m addr n v) b, Blocks.Inside b 1 bs
grind_pattern Mapped.loadInt_isSome => Mapped bs m, Mem.loadInt m addr n
grind_pattern Mapped.storeInt => Mapped bs m, Mem.storeInt m a n v

theorem Blocks.Inside.singleton_mono {w : Nat} {x a b : BitVec w} {k len len' : Nat}
    (h : Blocks.Inside x k [(b, len')]) (hs : (b - a).toNat + len' ≤ len) :
    Blocks.Inside x k [(a, len)] := by
  refine Or.inl ?_
  rcases h with h | h
  · have hx : x - a = (x - b) + (b - a) := by
      rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        ← BitVec.add_assoc (-b), BitVec.add_comm (-b) b, ← BitVec.sub_eq_add_neg b b, BitVec.sub_self,
        BitVec.zero_add]
    rw [hx, BitVec.toNat_add]
    have := Nat.mod_le ((x - b).toNat + (b - a).toNat) (2 ^ w)
    omega
  · exact h.elim

theorem DomainGrows.refl {w : Nat} (m : Mem w) : DomainGrows m m := fun _ h => h

theorem DomainGrows.trans {w : Nat} {m₁ m₂ m₃ : Mem w} (h₁ : DomainGrows m₁ m₂) (h₂ : DomainGrows m₂ m₃) :
    DomainGrows m₁ m₃ := fun b h => h₂ b (h₁ b h)

theorem WritesOnly.refl {w : Nat} (bs : List (BitVec w × Nat)) (m : Mem w) : WritesOnly bs m m :=
  ⟨fun _ _ => rfl, DomainGrows.refl m⟩

theorem WritesOnly.trans {w : Nat} {bs : List (BitVec w × Nat)} {m₁ m₂ m₃ : Mem w}
    (h₁ : WritesOnly bs m₁ m₂) (h₂ : WritesOnly bs m₂ m₃) : WritesOnly bs m₁ m₃ :=
  ⟨fun b hb => (h₂.1 b hb).trans (h₁.1 b hb), h₁.2.trans h₂.2⟩

theorem WritesOnly.mono_singleton {w : Nat} {m m' : Mem w} {a b : BitVec w} {len len' : Nat}
    (h : WritesOnly [(b, len')] m m') (hs : (b - a).toNat + len' ≤ len) : WritesOnly [(a, len)] m m' :=
  ⟨fun x hx => h.1 x fun hin => hx (hin.singleton_mono hs), h.2⟩

theorem WritesOnly.storeInt {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w} {a : BitVec w} {n : Nat}
    (hin : Blocks.Inside a n bs) (v : Int) : WritesOnly bs m (m.storeInt a n v) :=
  ⟨fun _ hb => hin.get?_storeInt hb v, DomainGrows.storeInt m a n v⟩

theorem WritesOnly.trans_storeInt {w : Nat} {bs : List (BitVec w × Nat)} {m m' : Mem w} {a : BitVec w}
    {n : Nat} (h : WritesOnly bs m m') (hin : Blocks.Inside a n bs) (v : Int) :
    WritesOnly bs m (m'.storeInt a n v) :=
  h.trans (WritesOnly.storeInt hin v)

def Block.ofStackSlots (rsp : UInt64) (k : Nat) : BitVec 64 × Nat :=
  (rsp.toBitVec - BitVec.ofNat 64 (8 * (k + 1)), 8 * (k + 1))

theorem Blocks.Inside.ofStackSlots {rsp : UInt64} {x : BitVec 64} {n k : Nat} {bs : List (BitVec 64 × Nat)}
    (hn : n ≤ x.toNat) (hx : x.toNat ≤ 8 * (k + 1)) (hk : 8 * (k + 1) < 2 ^ 64) :
    Blocks.Inside (rsp.toBitVec - x) n (Block.ofStackSlots rsp k :: bs) := by
  unfold Block.ofStackSlots
  have hy : rsp.toBitVec - (rsp.toBitVec - BitVec.ofNat 64 (8 * (k + 1))) = BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.sub_eq_add_neg rsp.toBitVec (rsp.toBitVec - _), BitVec.neg_sub, BitVec.add_comm (-rsp.toBitVec),
      ← BitVec.sub_eq_add_neg, BitVec.add_comm, BitVec.sub_add_cancel]
  have hd : (BitVec.ofNat 64 (8 * (k + 1))).toNat = 8 * (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  exact Blocks.Inside.sub (by rw [hy, hd]; exact hx) (by rw [hy, hd]; omega)

theorem Blocks.Disjoint.ofStackSlots {a : BitVec 64} {n k : Nat} (h : 8 * (k + 1) + n ≤ 2 ^ 64) :
    Blocks.Disjoint [(a, n)] [Block.ofStackSlots (UInt64.ofBitVec a) k] := by
  unfold Block.ofStackSlots
  intro x hx hx'
  rcases hx with hx | hx
  · rcases hx' with hx' | hx'
    · have hd : (BitVec.ofNat 64 (8 * (k + 1))).toNat = 8 * (k + 1) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have he : x - ((UInt64.ofBitVec a).toBitVec - BitVec.ofNat 64 (8 * (k + 1)))
          = (x - a) + BitVec.ofNat 64 (8 * (k + 1)) := by
        rw [UInt64.toBitVec_ofBitVec]; grind
      rw [he, BitVec.toNat_add, hd, Nat.mod_eq_of_lt (by omega)] at hx'
      omega
    · exact hx'
  · exact hx

theorem WritesOnly.ofStackSlots_push64 {m m' : Mem 64} {rsp : UInt64} {k : Nat} {v : Int}
    (hk : 8 * (k + 1) < 2 ^ 64)
    (h : WritesOnly [Block.ofStackSlots rsp k] (m.storeInt (rsp.toBitVec - 8) 8 v) m') :
    WritesOnly [Block.ofStackSlots rsp k] m m' :=
  (WritesOnly.storeInt (Blocks.Inside.ofStackSlots (by decide) (by simp; omega) hk) v).trans h

private theorem Block.ofStackSlots_sub_le {rsp : UInt64} {k k' : Nat} (hs : k' + 1 ≤ k)
    (hk : 8 * (k + 1) < 2 ^ 64) :
    ((Block.ofStackSlots (UInt64.ofBitVec (rsp.toBitVec - 8)) k').1 - (Block.ofStackSlots rsp k).1).toNat
      + (Block.ofStackSlots (UInt64.ofBitVec (rsp.toBitVec - 8)) k').2 ≤ (Block.ofStackSlots rsp k).2 := by
  unfold Block.ofStackSlots
  rw [UInt64.toBitVec_ofBitVec]
  have hz : (BitVec.ofNat 64 (8 * (k + 1))).toNat = 8 * (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have hy : (BitVec.ofNat 64 (8 * (k' + 1))).toNat = 8 * (k' + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : ((8 : BitVec 64) + BitVec.ofNat 64 (8 * (k' + 1))).toNat = 8 + 8 * (k' + 1) := by
    rw [BitVec.toNat_add, hy, Nat.mod_eq_of_lt (by simp; omega)]; rfl
  have he : (rsp.toBitVec - 8 - BitVec.ofNat 64 (8 * (k' + 1)) - (rsp.toBitVec - BitVec.ofNat 64 (8 * (k + 1)))).toNat
      = 8 * (k + 1) - 8 - 8 * (k' + 1) := by
    rw [show rsp.toBitVec - 8 - BitVec.ofNat 64 (8 * (k' + 1)) - (rsp.toBitVec - BitVec.ofNat 64 (8 * (k + 1)))
        = BitVec.ofNat 64 (8 * (k + 1)) - (8 + BitVec.ofNat 64 (8 * (k' + 1))) by grind,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1, hz]; omega), h1, hz]
    omega
  simp only
  omega

theorem WritesOnly.ofStackSlots_mono {m m' : Mem 64} {rsp : UInt64} {k k' : Nat}
    (hs : k' + 1 ≤ k) (hk : 8 * (k + 1) < 2 ^ 64)
    (h : WritesOnly [Block.ofStackSlots (UInt64.ofBitVec (rsp.toBitVec - 8)) k'] m m') :
    WritesOnly [Block.ofStackSlots rsp k] m m' :=
  h.mono_singleton (Block.ofStackSlots_sub_le hs hk)

theorem Blocks.Disjoint.ofStackSlots_mono {bs : List (BitVec 64 × Nat)} {rsp : UInt64} {k k' : Nat}
    (hs : k' + 1 ≤ k) (hk : 8 * (k + 1) < 2 ^ 64) (h : Blocks.Disjoint bs [Block.ofStackSlots rsp k]) :
    Blocks.Disjoint bs [Block.ofStackSlots (UInt64.ofBitVec (rsp.toBitVec - 8)) k'] :=
  fun b hb hb' => h b hb (hb'.singleton_mono (Block.ofStackSlots_sub_le hs hk))

theorem WritesOnly.mapped {w : Nat} {bs cs : List (BitVec w × Nat)} {m m' : Mem w}
    (h : WritesOnly bs m m') (hc : Mapped cs m) : Mapped cs m' :=
  fun b hb => h.2 b (hc b hb)

theorem WritesOnly.loadInt {w : Nat} {bs : List (BitVec w × Nat)} {m m' : Mem w} {a : BitVec w} {n : Nat}
    (h : WritesOnly bs m m') (hd : Blocks.Disjoint [(a, n)] bs) : m'.loadInt a n = m.loadInt a n :=
  Mem.loadInt_congr fun _ hi => h.1 _ (hd _ ((Blocks.Inside.base (Nat.le_refl n)).add_ofNat hi))

theorem Blocks.Inside.of_singleton {w : Nat} {b x : BitVec w} {n : Nat} {bs : List (BitVec w × Nat)}
    (hb : Blocks.Inside b 1 [(x, n)]) (hx : Blocks.Inside x n bs) : Blocks.Inside b 1 bs := by
  rcases hb with hb | hb
  · have := hx.add_ofNat (i := (b - x).toNat) (by omega)
    rwa [add_ofNat_toNat_sub] at this
  · exact hb.elim

theorem Blocks.Disjoint.of_inside {w : Nat} {x d : BitVec w} {n k : Nat}
    {bs₁ bs₂ : List (BitVec w × Nat)} (hd : Blocks.Disjoint bs₁ bs₂) (hx : Blocks.Inside x n bs₁)
    (hy : Blocks.Inside d k bs₂) : Blocks.Disjoint [(x, n)] [(d, k)] :=
  fun _ hb hb' => hd _ (hb.of_singleton hx) (hb'.of_singleton hy)

theorem Blocks.Disjoint.of_inside' {w : Nat} {x d : BitVec w} {n k : Nat}
    {bs₁ bs₂ : List (BitVec w × Nat)} (hd : Blocks.Disjoint bs₁ bs₂) (hx : Blocks.Inside x n bs₂)
    (hy : Blocks.Inside d k bs₁) : Blocks.Disjoint [(x, n)] [(d, k)] :=
  fun _ hb hb' => hd _ (hb'.of_singleton hy) (hb.of_singleton hx)

theorem Blocks.Disjoint.of_inside_left {w : Nat} {x d : BitVec w} {n k : Nat}
    {bs : List (BitVec w × Nat)} (hd : Blocks.Disjoint bs [(d, k)]) (hx : Blocks.Inside x n bs) :
    Blocks.Disjoint [(x, n)] [(d, k)] :=
  hd.of_inside hx (Blocks.Inside.base (Nat.le_refl k))

theorem Blocks.Disjoint.of_inside_right' {w : Nat} {x d : BitVec w} {n k : Nat}
    {bs : List (BitVec w × Nat)} (hd : Blocks.Disjoint bs [(x, n)]) (hy : Blocks.Inside d k bs) :
    Blocks.Disjoint [(x, n)] [(d, k)] :=
  hd.of_inside' (Blocks.Inside.base (Nat.le_refl n)) hy

theorem Blocks.Disjoint.of_inside_right_pair {w : Nat} {x d d' : BitVec w} {n k k' : Nat}
    (hd : Blocks.Disjoint [(x, n)] [(d', k')]) (hy : Blocks.Inside d k [(d', k')]) :
    Blocks.Disjoint [(x, n)] [(d, k)] :=
  hd.of_inside (Blocks.Inside.base (Nat.le_refl n)) hy

theorem Mapped.of_inside {w : Nat} {bs : List (BitVec w × Nat)} {m : Mem w} {x : BitVec w} {n : Nat}
    (h : Mapped bs m) (hx : Blocks.Inside x n bs) : Mapped [(x, n)] m :=
  fun b hb => h b (hb.of_singleton hx)

theorem Mapped.of_inside_pair {w : Nat} {m : Mem w} {x d : BitVec w} {n k : Nat}
    (h : Mapped [(d, k)] m) (hx : Blocks.Inside x n [(d, k)]) : Mapped [(x, n)] m :=
  h.of_inside hx

theorem Mapped.of_inside_cons_cons {w : Nat} {m : Mem w} {x : BitVec w} {n : Nat} {p q : BitVec w × Nat}
    {bs : List (BitVec w × Nat)} (h : Mapped (p :: q :: bs) m) (hx : Blocks.Inside x n (p :: q :: bs)) :
    Mapped [(x, n)] m :=
  h.of_inside hx

grind_pattern Blocks.Inside.ofStackSlots => Blocks.Inside (UInt64.toBitVec rsp - x) n (Block.ofStackSlots rsp k :: bs)
grind_pattern Blocks.Disjoint.ofStackSlots => Blocks.Disjoint [(a, n)] [Block.ofStackSlots (UInt64.ofBitVec a) k]
grind_pattern WritesOnly.refl => WritesOnly bs m m
grind_pattern WritesOnly.storeInt => WritesOnly bs m (Mem.storeInt m a n v)
grind_pattern WritesOnly.trans_storeInt => WritesOnly bs m (Mem.storeInt m' a n v)
grind_pattern WritesOnly.ofStackSlots_push64 =>
  WritesOnly [Block.ofStackSlots rsp k] m m', Mem.storeInt m (UInt64.toBitVec rsp - 8) 8 v
grind_pattern WritesOnly.ofStackSlots_mono =>
  WritesOnly [Block.ofStackSlots (UInt64.ofBitVec (UInt64.toBitVec rsp - 8)) k'] m m',
  WritesOnly [Block.ofStackSlots rsp k] m m'
grind_pattern Blocks.Disjoint.ofStackSlots_mono =>
  Blocks.Disjoint bs [Block.ofStackSlots rsp k],
  Blocks.Disjoint bs [Block.ofStackSlots (UInt64.ofBitVec (UInt64.toBitVec rsp - 8)) k']
grind_pattern WritesOnly.mapped => WritesOnly bs m m', Mapped cs m
grind_pattern WritesOnly.loadInt => WritesOnly bs m m', Mem.loadInt m' a n
grind_pattern Blocks.Disjoint.of_inside_left =>
  Blocks.Disjoint [(x, n)] [(d, k)], Blocks.Disjoint bs [(d, k)] where
  guard Blocks.Disjoint bs [(d, k)]
  bs =/= [(x, n)]
grind_pattern Blocks.Disjoint.of_inside_right_pair =>
  Blocks.Disjoint [(x, n)] [(d, k)], Blocks.Disjoint [(x, n)] [(d', k')] where
  guard Blocks.Disjoint [(x, n)] [(d', k')]
  k' =/= k
grind_pattern Blocks.Disjoint.of_inside_right' =>
  Blocks.Disjoint [(x, n)] [(d, k)], Blocks.Disjoint bs [(x, n)] where
  guard Blocks.Disjoint bs [(x, n)]
grind_pattern Mapped.of_inside_pair => Mapped [(x, n)] m, Mapped [(d, k)] m where
  guard Mapped [(d, k)] m
  k =/= n
grind_pattern Mapped.of_inside_cons_cons => Mapped [(x, n)] m, Mapped (p :: q :: bs) m where
  guard Mapped (p :: q :: bs) m

theorem loadInt_storeInt_of_disjoint {w : Nat} {m : Mem w} {a x : BitVec w} {n k : Nat}
    (hd : Blocks.Disjoint [(x, k)] [(a, n)]) (v : Int) :
    (m.storeInt a n v).loadInt x k = m.loadInt x k :=
  Mem.loadInt_congr fun _ hi =>
    (Blocks.Inside.base (Nat.le_refl n)).get?_storeInt
      (hd _ ((Blocks.Inside.base (Nat.le_refl k)).add_ofNat hi)) v

theorem Blocks.Disjoint.of_sub {w : Nat} {x a : BitVec w} {k n : Nat}
    (h₁ : n ≤ (x - a).toNat) (h₂ : k ≤ (a - x).toNat) : Blocks.Disjoint [(x, k)] [(a, n)] := by
  intro y hy hy'
  rcases hy with hy | hy
  · rcases hy' with hy' | hy'
    · have hneg : (a - x).toNat = (2 ^ w - (x - a).toNat) % 2 ^ w := by
        rw [show a - x = -(x - a) by grind, BitVec.toNat_neg]
      have he : y - a = (y - x) + (x - a) := by grind
      have hlt := (x - a).isLt
      rw [he, BitVec.toNat_add] at hy'
      by_cases hq : (x - a).toNat = 0
      · rw [hq, Nat.sub_zero, Nat.mod_self] at hneg
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hneg
        rw [Nat.mod_eq_of_lt (by omega)] at hy'
        omega
    · exact hy'
  · exact hy

theorem loadInt_storeInt_add {w : Nat} {m : Mem w} {b c d : BitVec w} {n k : Nat}
    (h₁ : n ≤ (d - c).toNat) (h₂ : k ≤ (c - d).toNat) (v : Int) :
    (m.storeInt (b + c) n v).loadInt (b + d) k = m.loadInt (b + d) k :=
  loadInt_storeInt_of_disjoint
    (Blocks.Disjoint.of_sub (by rwa [show b + d - (b + c) = d - c by grind])
      (by rwa [show b + c - (b + d) = c - d by grind])) v

grind_pattern loadInt_storeInt_add => Mem.loadInt (Mem.storeInt m (b + c) n v) (b + d) k

grind_pattern loadInt_storeInt_of_disjoint => Mem.loadInt (Mem.storeInt m a n v) x k

theorem loadInt_storeInt_of_inside {w : Nat} {m : Mem w} {a x : BitVec w} {n k : Nat}
    {bs₁ bs₂ : List (BitVec w × Nat)} (hd : Blocks.Disjoint bs₁ bs₂) (hx : Blocks.Inside x k bs₁)
    (ha : Blocks.Inside a n bs₂) (v : Int) : (m.storeInt a n v).loadInt x k = m.loadInt x k :=
  loadInt_storeInt_of_disjoint (hd.of_inside hx ha) v

theorem loadInt_storeInt_of_inside' {w : Nat} {m : Mem w} {a x : BitVec w} {n k : Nat}
    {bs₁ bs₂ : List (BitVec w × Nat)} (hd : Blocks.Disjoint bs₁ bs₂) (hx : Blocks.Inside x k bs₂)
    (ha : Blocks.Inside a n bs₁) (v : Int) : (m.storeInt a n v).loadInt x k = m.loadInt x k :=
  loadInt_storeInt_of_disjoint (hd.of_inside' hx ha) v

grind_pattern loadInt_storeInt_of_inside => Mem.loadInt (Mem.storeInt m a n v) x k, Blocks.Disjoint bs₁ bs₂ where
  guard Blocks.Disjoint bs₁ bs₂
grind_pattern loadInt_storeInt_of_inside' => Mem.loadInt (Mem.storeInt m a n v) x k, Blocks.Disjoint bs₁ bs₂ where
  guard Blocks.Disjoint bs₁ bs₂

def Blocks.decInside {w : Nat} (a : BitVec w) (n : Nat) :
    (bs : List (BitVec w × Nat)) → Decidable (Blocks.Inside a n bs)
  | [] => isFalse id
  | (_, _) :: bs => @instDecidableOr _ _ (Nat.decLe _ _) (Blocks.decInside a n bs)

instance {w : Nat} {a : BitVec w} {n : Nat} {bs : List (BitVec w × Nat)} :
    Decidable (Blocks.Inside a n bs) :=
  Blocks.decInside a n bs

theorem Blocks.Inside.append_iff {w : Nat} {a : BitVec w} {n : Nat} {bs cs : List (BitVec w × Nat)} :
    Blocks.Inside a n (bs ++ cs) ↔ Blocks.Inside a n bs ∨ Blocks.Inside a n cs := by
  induction bs with
  | nil => simp [Blocks.Inside]
  | cons p bs ih =>
    obtain ⟨b, len⟩ := p
    simp only [List.cons_append, Blocks.Inside]
    rw [ih, or_assoc]

def restrict {w : Nat} (y : Mem w) (bs : List (BitVec w × Nat)) : Mem w :=
  y.filter fun b _ => decide (Blocks.Inside b 1 bs)

def havoc {w : Nat} (m : Mem w) (bs : List (BitVec w × Nat)) (y : Mem w) : Mem w :=
  m.union (y.restrict bs)

theorem get?_restrict {w : Nat} (y : Mem w) (bs : List (BitVec w × Nat)) (b : BitVec w) :
    (y.restrict bs).get? b = if Blocks.Inside b 1 bs then y.get? b else none := by
  simp only [restrict, ExtHashMap.get?_eq_getElem?, ExtHashMap.getElem?_filter']
  by_cases h : Blocks.Inside b 1 bs <;> cases y[b]? <;> simp [h]

theorem get?_havoc {w : Nat} (m : Mem w) (bs : List (BitVec w × Nat)) (y : Mem w) (b : BitVec w) :
    (m.havoc bs y).get? b = if Blocks.Inside b 1 bs then (y.get? b).or (m.get? b) else m.get? b := by
  simp only [havoc, ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq, ExtHashMap.getElem?_union]
  rw [← ExtHashMap.get?_eq_getElem? (m := y.restrict bs), get?_restrict]
  by_cases h : Blocks.Inside b 1 bs <;> simp [h, ExtHashMap.get?_eq_getElem?]

theorem havoc_havoc {w : Nat} (m : Mem w) (bs cs : List (BitVec w × Nat)) (y z : Mem w) :
    (m.havoc bs y).havoc cs z = m.havoc (cs ++ bs) ((y.restrict bs).havoc cs z) := by
  apply ExtHashMap.ext_getElem?
  intro b
  simp only [← ExtHashMap.get?_eq_getElem?, get?_havoc, get?_restrict, Blocks.Inside.append_iff]
  by_cases hb : Blocks.Inside b 1 bs <;> by_cases hc : Blocks.Inside b 1 cs <;>
    cases y.get? b <;> cases z.get? b <;> cases m.get? b <;> simp [hb, hc]

theorem havoc_append_self {w : Nat} (m : Mem w) (bs : List (BitVec w × Nat)) (y : Mem w) :
    m.havoc (bs ++ bs) y = m.havoc bs y := by
  apply ExtHashMap.ext_getElem?
  intro b
  simp only [← ExtHashMap.get?_eq_getElem?, get?_havoc, Blocks.Inside.append_iff, or_self]

theorem havoc_restrict_havoc {w : Nat} (m : Mem w) (bs : List (BitVec w × Nat)) (y z : Mem w) :
    m.havoc bs ((y.restrict bs).havoc bs z) = m.havoc bs (y.havoc bs z) := by
  apply ExtHashMap.ext_getElem?
  intro b
  simp only [← ExtHashMap.get?_eq_getElem?, get?_havoc, get?_restrict]
  by_cases hb : Blocks.Inside b 1 bs <;> simp [hb]

theorem get?_storeInt {w : Nat} (m : Mem w) (a b : BitVec w) (n : Nat) (v : Int) :
    (m.storeInt a n v).get? b = ((Int.toBytes n v).At a)[b]?.or (m.get? b) := by
  simp only [Mem.storeInt, Mem.storeBytes, ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq,
    ExtHashMap.getElem?_union]

theorem Blocks.Inside.mem_At {w : Nat} {a b : BitVec w} {n : Nat} {v : Int}
    (h : Blocks.Inside b 1 [(a, n)]) : b ∈ (Int.toBytes n v).At a := by
  rw [mem_At_iff, Int.toBytes_length]
  rcases h with h | h
  · refine ⟨(b - a).toNat, by omega, ?_⟩
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · exact h.elim

theorem storeInt_havoc {w : Nat} (m : Mem w) (bs : List (BitVec w × Nat)) (y : Mem w) (a : BitVec w)
    (n : Nat) (v : Int) :
    (m.havoc bs y).storeInt a n v = m.havoc ([(a, n)] ++ bs) (y.storeInt a n v) := by
  apply ExtHashMap.ext_getElem?
  intro b
  simp only [← ExtHashMap.get?_eq_getElem?, get?_storeInt, get?_havoc, Blocks.Inside.append_iff]
  by_cases hs : b ∈ (Int.toBytes n v).At a
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (ExtHashMap.isSome_getElem?_iff_mem.mpr hs)
    have hi : Blocks.Inside b 1 [(a, n)] := by
      rw [mem_At_iff, Int.toBytes_length] at hs
      obtain ⟨i, hi, rfl⟩ := hs
      exact (Blocks.Inside.base (Nat.le_refl n)).add_ofNat hi
    simp [hx, hi]
  · have hi : ¬ Blocks.Inside b 1 [(a, n)] := fun h => hs h.mem_At
    rw [ExtHashMap.get?_eq_getElem? (a := b), ExtHashMap.getElem?_eq_none hs]
    by_cases hb : Blocks.Inside b 1 bs <;> simp [hb, hi]

theorem loadBytes_congr {w : Nat} {m m' : Mem w} {a : BitVec w} {n : Nat}
    (h : ∀ i < n, m.get? (a + .ofNat w i) = m'.get? (a + .ofNat w i)) :
    m.loadBytes a n = m'.loadBytes a n := by
  simp only [Mem.loadBytes]
  rw [List.map_congr_left (fun i hi => h i (List.mem_range.mp hi))]

theorem loadBytes_havoc_of_disjoint {w : Nat} {m y : Mem w} {bs : List (BitVec w × Nat)} {a : BitVec w}
    {n : Nat} (hd : Blocks.Disjoint [(a, n)] bs) : (m.havoc bs y).loadBytes a n = m.loadBytes a n :=
  loadBytes_congr fun _ hi => by
    rw [get?_havoc, ite_eq_right (hd _ ((Blocks.Inside.base (Nat.le_refl n)).add_ofNat hi))]

theorem loadBytes_havoc_of_inside {w : Nat} {m y : Mem w} {bs : List (BitVec w × Nat)} {a : BitVec w}
    {n : Nat} (h : Blocks.Inside a n bs) (hy : (y.loadBytes a n).isSome) :
    (m.havoc bs y).loadBytes a n = y.loadBytes a n :=
  loadBytes_congr fun i hi => by
    rw [get?_havoc, ite_eq_left (h.add_ofNat hi)]
    obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp hy
    obtain ⟨hl, hg⟩ := loadBytes_eq_some_iff.mp hxs
    rw [hg i (hl ▸ hi), Option.some_or]

theorem loadBytes_restrict_of_inside {w : Nat} {y : Mem w} {bs : List (BitVec w × Nat)} {a : BitVec w}
    {n : Nat} (h : Blocks.Inside a n bs) : (y.restrict bs).loadBytes a n = y.loadBytes a n :=
  loadBytes_congr fun _ hi => by rw [get?_restrict, ite_eq_left (h.add_ofNat hi)]

theorem loadInt_havoc_of_disjoint {w : Nat} {m y : Mem w} {bs : List (BitVec w × Nat)} {a : BitVec w}
    {n : Nat} (hd : Blocks.Disjoint [(a, n)] bs) : (m.havoc bs y).loadInt a n = m.loadInt a n := by
  rw [Mem.loadInt, loadBytes_havoc_of_disjoint hd, ← Mem.loadInt]

theorem loadInt_havoc_of_inside {w : Nat} {m y : Mem w} {bs : List (BitVec w × Nat)} {a : BitVec w}
    {n : Nat} (h : Blocks.Inside a n bs) (hy : (y.loadInt a n).isSome) :
    (m.havoc bs y).loadInt a n = y.loadInt a n := by
  rw [Mem.loadInt, loadBytes_havoc_of_inside h (by simpa [Mem.loadInt] using hy), ← Mem.loadInt]

theorem loadInt_restrict_of_inside {w : Nat} {y : Mem w} {bs : List (BitVec w × Nat)} {a : BitVec w}
    {n : Nat} (h : Blocks.Inside a n bs) : (y.restrict bs).loadInt a n = y.loadInt a n := by
  rw [Mem.loadInt, loadBytes_restrict_of_inside h, ← Mem.loadInt]

theorem DomainGrows.havoc {w : Nat} (m : Mem w) (bs : List (BitVec w × Nat)) (y : Mem w) :
    DomainGrows m (m.havoc bs y) := fun b hb => by
  rw [get?_havoc]
  split
  · cases y.get? b <;> simp_all
  · exact hb

theorem Mapped.havoc {w : Nat} {cs : List (BitVec w × Nat)} {m : Mem w} (hm : Mapped cs m)
    (bs : List (BitVec w × Nat)) (y : Mem w) : Mapped cs (m.havoc bs y) :=
  fun b hb => DomainGrows.havoc m bs y b (hm b hb)

theorem WritesOnly.eq_havoc {w : Nat} {bs : List (BitVec w × Nat)} {m m' : Mem w} (h : WritesOnly bs m m') :
    m' = m.havoc bs m' := by
  apply ExtHashMap.ext_getElem?
  intro b
  simp only [← ExtHashMap.get?_eq_getElem?, get?_havoc]
  split
  · cases hm' : m'.get? b with
    | some _ => rfl
    | none =>
      cases hm : m.get? b with
      | none => rfl
      | some _ => have := h.2 b (by rw [hm]; rfl); rw [hm'] at this; exact absurd this (by decide)
  · exact h.1 b ‹_›

theorem WritesOnly.havoc {w : Nat} (bs : List (BitVec w × Nat)) (m y : Mem w) :
    WritesOnly bs m (m.havoc bs y) :=
  ⟨fun b hb => by rw [get?_havoc, ite_eq_right hb], DomainGrows.havoc m bs y⟩

theorem Blocks.Disjoint.append_right_iff {w : Nat} {xs bs cs : List (BitVec w × Nat)} :
    Blocks.Disjoint xs (bs ++ cs) ↔ Blocks.Disjoint xs bs ∧ Blocks.Disjoint xs cs := by
  simp only [Blocks.Disjoint, Blocks.Inside.append_iff, not_or]
  exact ⟨fun h => ⟨fun b hb => (h b hb).1, fun b hb => (h b hb).2⟩, fun h b hb => ⟨h.1 b hb, h.2 b hb⟩⟩

theorem Blocks.Disjoint.cons_cons_right_iff {w : Nat} {xs : List (BitVec w × Nat)}
    {b c : BitVec w × Nat} {cs : List (BitVec w × Nat)} :
    Blocks.Disjoint xs (b :: c :: cs) ↔ Blocks.Disjoint xs [b] ∧ Blocks.Disjoint xs (c :: cs) :=
  Blocks.Disjoint.append_right_iff (bs := [b]) (cs := c :: cs)

theorem WritesOnly.loadBytes {w : Nat} {bs : List (BitVec w × Nat)} {m m' : Mem w} {a : BitVec w} {n : Nat}
    (h : WritesOnly bs m m') (hd : Blocks.Disjoint [(a, n)] bs) : m'.loadBytes a n = m.loadBytes a n :=
  loadBytes_congr fun _ hi => h.1 _ (hd _ ((Blocks.Inside.base (Nat.le_refl n)).add_ofNat hi))

theorem loadBytes_storeInt_of_disjoint {w : Nat} {m : Mem w} {a x : BitVec w} {n k : Nat}
    (hd : Blocks.Disjoint [(x, k)] [(a, n)]) (v : Int) : (m.storeInt a n v).loadBytes x k = m.loadBytes x k :=
  loadBytes_congr fun _ hi =>
    (Blocks.Inside.base (Nat.le_refl n)).get?_storeInt
      (hd _ ((Blocks.Inside.base (Nat.le_refl k)).add_ofNat hi)) v

theorem loadBytes_storeInt_of_inside {w : Nat} {m : Mem w} {a x : BitVec w} {n k : Nat}
    {bs₁ bs₂ : List (BitVec w × Nat)} (hd : Blocks.Disjoint bs₁ bs₂) (hx : Blocks.Inside x k bs₁)
    (ha : Blocks.Inside a n bs₂) (v : Int) : (m.storeInt a n v).loadBytes x k = m.loadBytes x k :=
  loadBytes_congr fun _ hi =>
    (Blocks.Inside.base (Nat.le_refl n)).get?_storeInt
      (hd.of_inside hx ha _ ((Blocks.Inside.base (Nat.le_refl k)).add_ofNat hi)) v

theorem loadBytes_storeInt_of_inside' {w : Nat} {m : Mem w} {a x : BitVec w} {n k : Nat}
    {bs₁ bs₂ : List (BitVec w × Nat)} (hd : Blocks.Disjoint bs₁ bs₂) (hx : Blocks.Inside x k bs₂)
    (ha : Blocks.Inside a n bs₁) (v : Int) : (m.storeInt a n v).loadBytes x k = m.loadBytes x k :=
  loadBytes_congr fun _ hi =>
    (Blocks.Inside.base (Nat.le_refl n)).get?_storeInt
      (hd.of_inside' hx ha _ ((Blocks.Inside.base (Nat.le_refl k)).add_ofNat hi)) v

attribute [vcgen_simp] havoc_havoc havoc_append_self havoc_restrict_havoc storeInt_havoc
attribute [grind norm] Blocks.Inside.append_iff Blocks.Disjoint.append_right_iff
  Blocks.Disjoint.cons_cons_right_iff

grind_pattern loadInt_havoc_of_disjoint => Mem.loadInt (havoc m bs y) a n
grind_pattern loadInt_havoc_of_inside => Mem.loadInt (havoc m bs y) a n
grind_pattern loadInt_restrict_of_inside => Mem.loadInt (restrict y bs) a n
grind_pattern loadBytes_havoc_of_disjoint => Mem.loadBytes (havoc m bs y) a n
grind_pattern loadBytes_havoc_of_inside => Mem.loadBytes (havoc m bs y) a n
grind_pattern loadBytes_restrict_of_inside => Mem.loadBytes (restrict y bs) a n
grind_pattern WritesOnly.havoc => havoc m bs y where
  m =/= restrict _ _
grind_pattern loadBytes_storeInt_of_disjoint => Mem.loadBytes (Mem.storeInt m a n v) x k
grind_pattern WritesOnly.loadBytes => WritesOnly bs m m', Mem.loadBytes m' a n
grind_pattern loadBytes_storeInt_of_inside => Mem.loadBytes (Mem.storeInt m a n v) x k, Blocks.Disjoint bs₁ bs₂ where
  guard Blocks.Disjoint bs₁ bs₂
grind_pattern loadBytes_storeInt_of_inside' => Mem.loadBytes (Mem.storeInt m a n v) x k, Blocks.Disjoint bs₁ bs₂ where
  guard Blocks.Disjoint bs₁ bs₂

end Mem
