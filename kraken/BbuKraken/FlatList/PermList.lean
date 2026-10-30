import BbuKraken.Model

/-!
Lemmas on lists for `Bbu.normalize` of the list model. `regroup_ok` gives the result of
`Bbu.regroup` at each position (`regroupAt`), and `dedup_eq` gives `Bbu.dedup` as the
last copies. `FlatList/Regroup.lean` uses them for the flat `regroup`.
-/

namespace Bbu

/-! ## Lists of numbers -/

theorem getElem!_set_nat {l : List Nat} {i : Nat} (j x : Nat) (hi : i < l.length) :
    (l.set i x)[j]! = if j = i then x else l[j]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst h; simp [hi]
  · rw [ite_eq_right (c := i = j) (fun h' => h h'.symm), ite_eq_right h]

theorem getElem!_lt_of_mem {l : List Nat} {n : Nat} (h : ∀ x ∈ l, x < n) (h0 : 0 < n) (i : Nat) :
    l[i]! < n := by
  by_cases hi : i < l.length
  · rw [getElem!_pos l i hi]; exact h _ (List.getElem_mem hi)
  · rw [getElem!_neg l i hi]; exact h0

theorem getElem!_append_left {l1 l2 : List Nat} {i : Nat} (h : i < l1.length) :
    (l1 ++ l2)[i]! = l1[i]! := by
  rw [getElem!_pos (l1 ++ l2) i (by simp; omega), getElem!_pos l1 i h, List.getElem_append_left h]

theorem countP_range_succ (P : Nat → Bool) (n : Nat) :
    (List.range (n + 1)).countP P = (List.range n).countP P + if P n then 1 else 0 := by
  rw [List.range_succ, List.countP_append]
  by_cases h : P n <;> simp [h]

theorem countP_range_lt {P : Nat → Bool} {w n : Nat} (hw : P w) (hn : w < n) :
    (List.range w).countP P < (List.range n).countP P := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [countP_range_succ]
    by_cases h : w < n
    · have := ih h; omega
    · have : w = n := by omega
      subst this; rw [ite_eq_left hw]; omega

theorem countP_range_le (P : Nat → Bool) {w n : Nat} (hn : w ≤ n) :
    (List.range w).countP P ≤ (List.range n).countP P := by
  induction n with
  | zero => have : w = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    rw [countP_range_succ]
    by_cases h : w ≤ n
    · have := ih h; omega
    · have : w = n + 1 := by omega
      subst this; rw [countP_range_succ]; exact Nat.le_refl _

-- The point `w` of `P` is at the index of the number of points below it.
theorem filter_range_getElem {P : Nat → Bool} {w n : Nat} (hw : P w) (hn : w < n) :
    ((List.range n).filter P)[(List.range w).countP P]! = w := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    by_cases h : w < n
    · rw [getElem!_append_left (by rw [← List.countP_eq_length_filter]; exact countP_range_lt hw h)]
      exact ih h
    · have : w = n := by omega
      subst this
      rw [List.filter_cons, ite_eq_left hw, List.filter_nil, List.countP_eq_length_filter,
        getElem!_pos _ _ (by simp)]
      simp

/-! ## Sorted lists -/

theorem eq_of_sorted : ∀ {l1 l2 : List Nat}, l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (by simp)) (by simp)
  | a :: l1, b :: l2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have ha := (h a).1 (by simp)
    have hb := (h b).2 (by simp)
    have hab : a = b := by
      rcases List.mem_cons.1 ha with e | ha
      · exact e
      rcases List.mem_cons.1 hb with e | hb
      · exact e.symm
      have := h1.1 _ hb; have := h2.1 _ ha; omega
    subst hab
    rw [eq_of_sorted h1.2 h2.2 (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)]
    · have := h1.1 x hx
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · omega
      · exact e
    · have := h2.1 x hx
      rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · omega
      · exact e

theorem sorted_of_le_nodup {l : List Nat} (h1 : l.Pairwise (fun a b => decide (a ≤ b) = true))
    (h2 : l.Nodup) : l.Pairwise (· < ·) :=
  (h1.and h2).imp fun ⟨h, h'⟩ => by simp at h; omega

theorem length_filter_add {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter fun x => !p x).length = l.length
  | [] => rfl
  | a :: l => by
    have := length_filter_add p l
    by_cases h : p a <;> simp [h] <;> omega

/-! ## `setValue` -/

-- The index that `setValue` reads at `y`: `a` and `c` exchange.
def swapIdx (a c y : Nat) : Nat := if y = a then c else if y = c then a else y

theorem swapIdx_cases (a c y : Nat) :
    (y = a ∧ swapIdx a c y = c) ∨ (y ≠ a ∧ y = c ∧ swapIdx a c y = a) ∨
      (y ≠ a ∧ y ≠ c ∧ swapIdx a c y = y) := by
  unfold swapIdx
  by_cases h1 : y = a
  · exact Or.inl ⟨h1, by rw [ite_eq_left h1]⟩
  · by_cases h2 : y = c
    · exact Or.inr (Or.inl ⟨h1, h2, by rw [ite_eq_right h1, ite_eq_left h2]⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, by rw [ite_eq_right h1, ite_eq_right h2]⟩)

theorem swapIdx_lt {a c n y : Nat} (ha : a < n) (hc : c < n) (hy : y < n) : swapIdx a c y < n := by
  rcases swapIdx_cases a c y with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> omega

theorem swapIdx_inj {a c i j : Nat} (h : swapIdx a c i = swapIdx a c j) : i = j := by
  rcases swapIdx_cases a c i with ⟨_, h1⟩ | ⟨_, _, h1⟩ | ⟨_, _, h1⟩ <;>
  rcases swapIdx_cases a c j with ⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> omega

theorem swapIdx_swapIdx (a c y : Nat) : swapIdx a c (swapIdx a c y) = y := by
  rcases swapIdx_cases a c y with ⟨_, h1⟩ | ⟨_, _, h1⟩ | ⟨_, _, h1⟩ <;>
  rcases swapIdx_cases a c (swapIdx a c y) with ⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> omega

-- `q` holds a permutation of `range n` that maps the positions of `G` onto the
-- destinations of `D`.
structure SInv (n : Nat) (G D : Nat → Prop) (q : List Nat) : Prop where
  len : q.length = n
  lt : ∀ i, i < n → q[i]! < n
  inj : ∀ i j, i < n → j < n → q[i]! = q[j]! → i = j
  onto : ∀ d, D d → ∃ y, G y ∧ y < n ∧ q[y]! = d

section
variable {n : Nat} {G D : Nat → Prop} {q : List Nat}

theorem SInv.not_mem (hq : SInv n G D q) {x : Nat} (hx : ¬G x) (hxn : x < n) : ¬D q[x]! := by
  intro hd
  obtain ⟨y, hy, hyn, he⟩ := hq.onto _ hd
  exact hx (hq.inj _ _ hyn hxn he ▸ hy)

theorem SInv.isPerm (h : SInv n G D q) : IsPerm q := by
  refine ⟨fun i hi => ?_, fun i hi j hj he => ?_⟩
  · have := h.lt i (h.len ▸ hi)
    rw [getElem!_pos q i hi] at this
    rw [h.len]; exact this
  · apply h.inj i j (h.len ▸ hi) (h.len ▸ hj)
    rw [getElem!_pos q i hi, getElem!_pos q j hj]; exact he

theorem SInv.of_isPerm (hl : q.length = n) (hp : IsPerm q)
    (honto : ∀ d, D d → ∃ y, G y ∧ y < n ∧ q[y]! = d) : SInv n G D q := by
  refine ⟨hl, fun i hi => ?_, fun i j hi hj he => ?_, honto⟩
  · rw [getElem!_pos q i (by omega)]; have := hp.1 i (by omega); omega
  · rw [getElem!_pos q i (by omega), getElem!_pos q j (by omega)] at he
    exact hp.2 i _ j _ he

-- `setValue q a b` exchanges the destinations of `a` and of the position `c` that goes to `b`.
theorem setValue_getElem (hq : SInv n G D q) {a b c : Nat} (ha : a < n) (hc : c < n)
    (hcb : q[c]! = b) (y : Nat) : (setValue q a b)[y]! = q[swapIdx a c y]! := by
  have hcl : c < q.length := by rw [hq.len]; exact hc
  have hb : b ∈ q := by
    rw [← hcb, getElem!_pos q c hcl]; exact List.getElem_mem _
  have hil := List.idxOf_lt_length_of_mem hb
  have hi : q.idxOf b = c := by
    apply hq.inj _ _ (by rw [← hq.len]; exact hil) hc
    rw [hcb, getElem!_pos q _ hil, List.getElem_idxOf hil]
  unfold setValue swapIdx
  rw [hi, getElem!_set_nat _ _ (by simp [hq.len, ha]), getElem!_set_nat _ _ hcl]
  by_cases h1 : y = a
  · rw [ite_eq_left h1, ite_eq_left h1, hcb]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : y = c
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2]

theorem SInv.setValue (hq : SInv n G D q) {a b : Nat} (hG : G a) (ha : a < n) (hD : D b) :
    SInv n G D (setValue q a b) ∧ (setValue q a b)[a]! = b ∧
      ∀ y, y ≠ a → q[y]! ≠ b → (setValue q a b)[y]! = q[y]! := by
  obtain ⟨c, hcG, hc, hcb⟩ := hq.onto b hD
  have hv := setValue_getElem hq ha hc hcb
  refine ⟨⟨?_, fun i hi => ?_, fun i j hi hj h => ?_, fun d hd => ?_⟩, ?_, fun y h1 h2 => ?_⟩
  · unfold Bbu.setValue; simp [hq.len]
  · rw [hv]; exact hq.lt _ (swapIdx_lt ha hc hi)
  · rw [hv, hv] at h
    exact swapIdx_inj (hq.inj _ _ (swapIdx_lt ha hc hi) (swapIdx_lt ha hc hj) h)
  · obtain ⟨y, hy, hyn, hyd⟩ := hq.onto d hd
    refine ⟨swapIdx a c y, ?_, swapIdx_lt ha hc hyn, by rw [hv, swapIdx_swapIdx, hyd]⟩
    rcases swapIdx_cases a c y with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h2]; exact hcG
    · rw [h3]; exact hG
    · rw [h3]; exact hy
  · rw [hv]; unfold swapIdx; rw [ite_eq_left rfl, hcb]
  · rw [hv]; unfold swapIdx
    rw [ite_eq_right h1, ite_eq_right (c := y = c) (fun h => h2 (h ▸ hcb))]

-- A `foldl` of `setValue`: each `fa x` goes to `fb x`, and the other positions keep their
-- destinations.
theorem SInv.foldl {α : Type} (fa fb : α → Nat) :
    ∀ (L : List α) (q : List Nat), SInv n G D q → L.Nodup →
      (∀ x ∈ L, G (fa x) ∧ fa x < n ∧ D (fb x)) →
      (∀ x ∈ L, ∀ y ∈ L, fa x = fa y → x = y) →
      (∀ x ∈ L, ∀ y ∈ L, fb x = fb y → x = y) →
      SInv n G D (L.foldl (fun q x => Bbu.setValue q (fa x) (fb x)) q) ∧
        (∀ x ∈ L, (L.foldl (fun q x => Bbu.setValue q (fa x) (fb x)) q)[fa x]! = fb x) ∧
        ∀ y, (∀ x ∈ L, fa x ≠ y ∧ fb x ≠ q[y]!) →
          (L.foldl (fun q x => Bbu.setValue q (fa x) (fb x)) q)[y]! = q[y]!
  | [], q, hq, _, _, _, _ => ⟨hq, by simp, fun _ _ => rfl⟩
  | a :: L, q, hq, hnd, hm, hia, hib => by
    rw [List.foldl_cons]
    obtain ⟨hga, han, hdb⟩ := hm a (by simp)
    obtain ⟨h1, h2, h3⟩ := hq.setValue hga han hdb
    rw [List.nodup_cons] at hnd
    obtain ⟨r1, r2, r3⟩ := SInv.foldl fa fb L _ h1 hnd.2 (fun x hx => hm x (by simp [hx]))
      (fun x hx y hy => hia x (by simp [hx]) y (by simp [hy]))
      (fun x hx y hy => hib x (by simp [hx]) y (by simp [hy]))
    refine ⟨r1, fun x hx => ?_, fun y hy => ?_⟩
    · rcases List.mem_cons.1 hx with e | hx
      · rw [e]
        have hc : ∀ y ∈ L, fa y ≠ fa a ∧ fb y ≠ (Bbu.setValue q (fa a) (fb a))[fa a]! := by
          intro y hy
          rw [h2]
          refine ⟨fun h => hnd.1 ?_, fun h => hnd.1 ?_⟩
          · exact hia y (by simp [hy]) a (by simp) h ▸ hy
          · exact hib y (by simp [hy]) a (by simp) h ▸ hy
        rw [r3 _ hc, h2]
      · exact r2 x hx
    · obtain ⟨hay, hby⟩ := hy a (by simp)
      have he := h3 y (Ne.symm hay) (Ne.symm hby)
      rw [r3 _ (fun x hx => by rw [he]; exact hy x (by simp [hx])), he]

end

/-! ## `regroup` -/

-- The positions that hold `slot`.
def grp (vals : List StackSlot) (slot : StackSlot) : List Nat :=
  (List.range vals.length).filter (vals[·]! == slot)

-- The destinations of the positions that hold `slot`.
def grpDest (vals : List StackSlot) (p : List Nat) (slot : StackSlot) : List Nat :=
  (grp vals slot).map (p[·]!)

-- The destination of the position `x` after `regroup vals p slot`: a position of the group
-- that is a destination of the group goes to itself; the other positions of the group take
-- the other destinations of the group in order.
def regroupAt (vals : List StackSlot) (p : List Nat) (slot : StackSlot) (x : Nat) : Nat :=
  if vals[x]! == slot then
    if x ∈ grpDest vals p slot then x
    else ((List.range vals.length).filter fun w =>
        decide (w ∈ grpDest vals p slot) && !(vals[w]! == slot))[
      (List.range x).countP fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot)]!
  else p[x]!

theorem mem_grp {vals : List StackSlot} {slot : StackSlot} {x : Nat} :
    x ∈ grp vals slot ↔ x < vals.length ∧ vals[x]! = slot := by
  simp [grp]

theorem regroup_eq {vals : List StackSlot} {p : List Nat} {slot : StackSlot}
    (h : ¬(grp vals slot).length < 2) :
    regroup vals p slot =
      let desired := (grpDest vals p slot).mergeSort
      let p1 := ((grp vals slot).filter (· ∈ desired)).foldl (fun p pos => setValue p pos pos) p
      let movers := (grp vals slot).filter (· ∉ desired)
      let vacant := desired.filter (· ∉ grp vals slot)
      if movers.length ≠ vacant.length then .error .assertion
      else .ok ((List.range movers.length).foldl (fun p i => setValue p movers[i]! vacant[i]!) p1) := by
  unfold regroup; exact ite_eq_right h

theorem filter_range_two {P : Nat → Bool} {n x y : Nat} (hx : P x) (hy : P y) (hxn : x < n)
    (hyn : y < n) (hne : x ≠ y) : 2 ≤ ((List.range n).filter P).length := by
  rw [← List.countP_eq_length_filter]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := countP_range_lt hx h; have := countP_range_lt hy hyn; omega
  · have := countP_range_lt hy h; have := countP_range_lt hx hxn; omega

-- The positions of the group go to the destinations of the group, and the destinations of
-- the group are distinct and below the length.
theorem grp_sinv {vals : List StackSlot} {p : List Nat} (slot : StackSlot)
    (hl : p.length = vals.length) (hp : IsPerm p) :
    SInv vals.length (· ∈ grp vals slot) (· ∈ grpDest vals p slot) p ∧
      (grpDest vals p slot).Nodup ∧ ∀ d ∈ grpDest vals p slot, d < vals.length := by
  have hq : SInv vals.length (· ∈ grp vals slot) (· ∈ grpDest vals p slot) p :=
    SInv.of_isPerm hl hp fun d hd => by
      obtain ⟨y, hy, he⟩ := List.mem_map.1 hd
      exact ⟨y, hy, (mem_grp.1 hy).1, he⟩
  have hGn : (grp vals slot).Nodup := (List.pairwise_lt_range.filter _).imp Nat.ne_of_lt
  refine ⟨hq, List.pairwise_map.2 (List.Pairwise.imp_of_mem
    (fun ha hb hab he => hab (hq.inj _ _ (mem_grp.1 ha).1 (mem_grp.1 hb).1 he)) hGn),
    fun d hd => ?_⟩
  obtain ⟨y, hy, he⟩ := List.mem_map.1 hd
  rw [← he]; exact hq.lt y (mem_grp.1 hy).1

-- The movers and the vacant offsets of `regroup` are the positions of the group that are
-- not destinations of the group, and the destinations of the group that are not positions
-- of the group. Their numbers are equal.
theorem movers_vacant {vals : List StackSlot} {p : List Nat} {slot : StackSlot}
    (hDn : (grpDest vals p slot).Nodup) (hDlt : ∀ d ∈ grpDest vals p slot, d < vals.length) :
    (grp vals slot).filter (· ∉ (grpDest vals p slot).mergeSort) =
        (List.range vals.length).filter
          (fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot)) ∧
      ((grpDest vals p slot).mergeSort).filter (· ∉ grp vals slot) =
        (List.range vals.length).filter
          (fun w => decide (w ∈ grpDest vals p slot) && !(vals[w]! == slot)) ∧
      ((List.range vals.length).filter
          (fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot))).length =
        ((List.range vals.length).filter
          (fun w => decide (w ∈ grpDest vals p slot) && !(vals[w]! == slot))).length := by
  have hGs : (grp vals slot).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hds : ((grpDest vals p slot).mergeSort).Pairwise (· < ·) := sorted_of_le_nodup
    (List.pairwise_mergeSort (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) _)
    ((List.mergeSort_perm _ _).nodup_iff.2 hDn)
  have hmd : ∀ w, w ∈ (grpDest vals p slot).mergeSort ↔ w ∈ grpDest vals p slot :=
    fun w => List.mem_mergeSort
  have hdl : ((grpDest vals p slot).mergeSort).length = (grp vals slot).length := by
    simp [grpDest]
  generalize (grpDest vals p slot).mergeSort = desired at hds hmd hdl ⊢
  have hvac : desired.filter (· ∉ grp vals slot) =
      (List.range vals.length).filter
        fun w => decide (w ∈ grpDest vals p slot) && !(vals[w]! == slot) := by
    apply eq_of_sorted (hds.filter _) (List.pairwise_lt_range.filter _)
    intro w
    by_cases h1 : w ∈ grpDest vals p slot <;> simp [h1, hmd, mem_grp, hDlt w]
  have hmov : (grp vals slot).filter (· ∉ desired) =
      (List.range vals.length).filter
        fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot) := by
    apply eq_of_sorted (hGs.filter _) (List.pairwise_lt_range.filter _)
    intro y
    simp [hmd, mem_grp, and_assoc]
  have h14 : (grp vals slot).filter (· ∈ desired) = desired.filter (· ∈ grp vals slot) := by
    apply eq_of_sorted (hGs.filter _) (hds.filter _)
    intro y
    simp [hmd]
    exact And.comm
  refine ⟨hmov, hvac, ?_⟩
  rw [← hmov, ← hvac]
  have e1 := length_filter_add (· ∈ desired) (grp vals slot)
  have e2 := length_filter_add (· ∈ grp vals slot) desired
  have f1 : (grp vals slot).filter (· ∉ desired) =
      (grp vals slot).filter (fun x => !decide (x ∈ desired)) :=
    List.filter_congr fun x _ => by simp
  have f2 : desired.filter (· ∉ grp vals slot) =
      desired.filter (fun x => !decide (x ∈ grp vals slot)) :=
    List.filter_congr fun x _ => by simp
  rw [f1, f2]
  rw [h14] at e1
  omega

-- The number of movers of `regroup` is the number of vacant offsets.
theorem length_movers {vals : List StackSlot} {p : List Nat} (slot : StackSlot)
    (hl : p.length = vals.length) (hp : IsPerm p) :
    ((List.range vals.length).filter
        (fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot))).length =
      ((List.range vals.length).filter
        (fun w => decide (w ∈ grpDest vals p slot) && !(vals[w]! == slot))).length := by
  obtain ⟨_, hDn, hDlt⟩ := grp_sinv slot hl hp
  exact (movers_vacant hDn hDlt).2.2

-- `regroup` of the list model gives `regroupAt` at each position and keeps the permutation.
theorem regroup_ok {vals : List StackSlot} {p : List Nat} (slot : StackSlot)
    (hl : p.length = vals.length) (hp : IsPerm p) :
    ∃ r, regroup vals p slot = .ok r ∧ r.length = vals.length ∧ IsPerm r ∧
      ∀ x, x < vals.length → r[x]! = regroupAt vals p slot x := by
  obtain ⟨hq, hDn, hDlt⟩ := grp_sinv slot hl hp
  have hGn : (grp vals slot).Nodup := (List.pairwise_lt_range.filter _).imp Nat.ne_of_lt
  by_cases hlt : (grp vals slot).length < 2
  · refine ⟨p, by unfold regroup; exact ite_eq_left hlt, hl, hp, fun x hx => ?_⟩
    unfold regroupAt
    by_cases hg : (vals[x]! == slot) = true
    · rw [ite_eq_left hg]
      have hxs : vals[x]! = slot := by simpa using hg
      have hone : ∀ y, y < vals.length → vals[y]! = slot → y = x := fun y hy hys => by
        by_cases hne : y = x
        · exact hne
        · have := filter_range_two (P := (vals[·]! == slot)) (by simpa using hys) hg hy hx hne
          unfold grp at hlt; omega
      by_cases hd : x ∈ grpDest vals p slot
      · rw [ite_eq_left hd]
        obtain ⟨y, hy, hyd⟩ := List.mem_map.1 hd
        obtain ⟨hyn, hys⟩ := mem_grp.1 hy
        have := hone y hyn hys
        subst this
        exact hyd
      · rw [ite_eq_right hd]
        have hc0 : (List.range x).countP
            (fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot)) = 0 :=
          List.countP_eq_zero.2 fun y hy h => by
            have := List.mem_range.1 hy
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            have := hone y (by omega) h.1
            omega
        rw [hc0]
        have hxG : x ∈ grp vals slot := mem_grp.2 ⟨hx, hxs⟩
        have hpd : p[x]! ∈ grpDest vals p slot := List.mem_map.2 ⟨x, hxG, rfl⟩
        have hpx : p[x]! ≠ x := fun h => hd (h ▸ hpd)
        have hpn : p[x]! < vals.length := hq.lt x hx
        have hP : (decide (p[x]! ∈ grpDest vals p slot) && !(vals[p[x]!]! == slot)) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
          exact ⟨hpd, fun h => hpx (hone _ hpn h)⟩
        have hc1 : (List.range p[x]!).countP
            (fun w => decide (w ∈ grpDest vals p slot) && !(vals[w]! == slot)) = 0 :=
          List.countP_eq_zero.2 fun w hw h => by
            have := List.mem_range.1 hw
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨y, hy, hyd⟩ := List.mem_map.1 h.1
            obtain ⟨hyn, hys⟩ := mem_grp.1 hy
            have := hone y hyn hys
            subst this
            omega
        have := filter_range_getElem (P := fun w => decide (w ∈ grpDest vals p slot) && !(vals[w]! == slot)) hP hpn
        rw [hc1] at this
        exact this.symm
    · rw [ite_eq_right hg]
  · rw [regroup_eq hlt]
    dsimp only
    obtain ⟨hmov, hvac, hlen⟩ := movers_vacant (slot := slot) hDn hDlt
    rw [hmov, hvac, ite_eq_right (c := _ ≠ _) (fun h => h hlen)]
    refine ⟨_, rfl, ?_⟩
    have hmd : ∀ w, w ∈ (grpDest vals p slot).mergeSort ↔ w ∈ grpDest vals p slot :=
      fun w => List.mem_mergeSort
    generalize (grpDest vals p slot).mergeSort = desired at hmd ⊢
    have hMm : ∀ y, y ∈ (List.range vals.length).filter
        (fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot)) ↔
        y ∈ grp vals slot ∧ y ∉ grpDest vals p slot := fun y => by simp [mem_grp, and_assoc]
    have hVm : ∀ w, w ∈ (List.range vals.length).filter
        (fun w => decide (w ∈ grpDest vals p slot) && !(vals[w]! == slot)) ↔
        w ∈ grpDest vals p slot ∧ w ∉ grp vals slot := fun w => by
      by_cases h1 : w ∈ grpDest vals p slot <;> simp [h1, mem_grp, hDlt w]
    have hMn : ((List.range vals.length).filter
        (fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot))).Nodup :=
      (List.pairwise_lt_range.filter _).imp Nat.ne_of_lt
    have hVn : ((List.range vals.length).filter
        (fun w => decide (w ∈ grpDest vals p slot) && !(vals[w]! == slot))).Nodup :=
      (List.pairwise_lt_range.filter _).imp Nat.ne_of_lt
    have hAm : ∀ x, x ∈ (grp vals slot).filter (fun x => decide (x ∈ desired)) ↔
        x ∈ grp vals slot ∧ x ∈ grpDest vals p slot := fun x => by simp [hmd]
    have F1 := SInv.foldl (fun x => x) (fun x => x) ((grp vals slot).filter fun x => decide (x ∈ desired))
      p hq (hGn.filter _)
      (fun x hx => ⟨((hAm x).1 hx).1, (mem_grp.1 ((hAm x).1 hx).1).1, ((hAm x).1 hx).2⟩)
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
    generalize List.foldl (fun p pos => setValue p pos pos) p
      ((grp vals slot).filter fun x => decide (x ∈ desired)) = p1 at F1 ⊢
    obtain ⟨hq1, hA1, hA2⟩ := F1
    generalize hM : (List.range vals.length).filter
      (fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot)) = M at hMm hMn hlen ⊢
    generalize hV : (List.range vals.length).filter
      (fun w => decide (w ∈ grpDest vals p slot) && !(vals[w]! == slot)) = V at hVm hVn hlen ⊢
    have hMi : ∀ i, i < M.length → M[i]! ∈ M := fun i hi => by
      rw [getElem!_pos M i hi]; exact List.getElem_mem hi
    have hVi : ∀ i, i < M.length → V[i]! ∈ V := fun i hi => by
      rw [getElem!_pos V i (by omega)]; exact List.getElem_mem _
    have F2 := SInv.foldl (fun i => M[i]!) (fun i => V[i]!) (List.range M.length) p1 hq1
      List.nodup_range
      (fun i hi => by
        have hi := List.mem_range.1 hi
        have h1 := (hMm _).1 (hMi i hi)
        exact ⟨h1.1, (mem_grp.1 h1.1).1, ((hVm _).1 (hVi i hi)).1⟩)
      (fun i hi j hj h => by
        have hi := List.mem_range.1 hi; have hj := List.mem_range.1 hj
        rw [getElem!_pos M i hi, getElem!_pos M j hj] at h
        exact hMn.getElem_inj.1 h)
      (fun i hi j hj h => by
        have hi := List.mem_range.1 hi; have hj := List.mem_range.1 hj
        rw [getElem!_pos V i (by omega), getElem!_pos V j (by omega)] at h
        exact hVn.getElem_inj.1 h)
    obtain ⟨hq2, hB1, hB2⟩ := F2
    refine ⟨hq2.len, hq2.isPerm, fun x hx => ?_⟩
    unfold regroupAt
    rw [hV]
    by_cases hg : (vals[x]! == slot) = true
    · rw [ite_eq_left hg]
      have hxs : vals[x]! = slot := by simpa using hg
      have hxG : x ∈ grp vals slot := mem_grp.2 ⟨hx, hxs⟩
      by_cases hd : x ∈ grpDest vals p slot
      · rw [ite_eq_left hd]
        have hp1 : p1[x]! = x := hA1 x ((hAm x).2 ⟨hxG, hd⟩)
        rw [hB2 x fun i hi => by
          have hi := List.mem_range.1 hi
          refine ⟨fun h => ((hMm _).1 (hMi i hi)).2 (h ▸ hd), fun h => ?_⟩
          rw [hp1] at h
          exact ((hVm _).1 (hVi i hi)).2 (h ▸ hxG), hp1]
      · rw [ite_eq_right hd]
        have hQ : ((vals[x]! == slot) && !decide (x ∈ grpDest vals p slot)) = true := by
          simp [hxs, hd]
        have hMx := filter_range_getElem
          (P := fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot)) hQ hx
        have hlt := countP_range_lt
          (P := fun y => (vals[y]! == slot) && !decide (y ∈ grpDest vals p slot)) hQ hx
        rw [List.countP_eq_length_filter (l := List.range vals.length), hM] at hlt
        rw [hM] at hMx
        have := hB1 _ (List.mem_range.2 hlt)
        rw [hMx] at this
        exact this
    · rw [ite_eq_right hg]
      have hxG : x ∉ grp vals slot := fun h => hg (by simp [(mem_grp.1 h).2])
      have hpx : p[x]! ∉ grpDest vals p slot := hq.not_mem hxG hx
      have hp1 : p1[x]! = p[x]! := hA2 x fun a ha =>
        ⟨fun h => hxG (h ▸ ((hAm a).1 ha).1), fun h => hpx (h ▸ ((hAm a).1 ha).2)⟩
      rw [hB2 x fun i hi => by
        have hi := List.mem_range.1 hi
        refine ⟨fun h => hxG (h ▸ ((hMm _).1 (hMi i hi)).1), fun h => ?_⟩
        rw [hp1] at h
        exact hpx (h ▸ ((hVm _).1 (hVi i hi)).1), hp1]

/-! ## `dedup` -/

section
variable {α : Type} [DecidableEq α]

theorem dedup_cons (a : α) (l : List α) :
    dedup (a :: l) = if a ∈ dedup l then dedup l else a :: dedup l := rfl

theorem mem_dedup : ∀ (l : List α) (a : α), a ∈ dedup l ↔ a ∈ l
  | [], a => by simp [dedup]
  | b :: l, a => by
    rw [dedup_cons]
    by_cases h : b ∈ dedup l
    · rw [ite_eq_left h, mem_dedup l a, List.mem_cons]
      refine ⟨Or.inr, fun h' => ?_⟩
      rcases h' with e | h'
      · rw [e]; exact (mem_dedup l b).1 h
      · exact h'
    · rw [ite_eq_right h, List.mem_cons, List.mem_cons, mem_dedup l a]

variable [Inhabited α]

-- The position `k` of `l` holds the last copy of its element.
def isLast (l : List α) (k : Nat) : Bool := decide (l[k]! ∉ l.drop (k + 1))

theorem isLast_iff {l : List α} {k : Nat} :
    isLast l k = true ↔ ∀ j, k < j → j < l.length → l[j]! ≠ l[k]! := by
  unfold isLast
  rw [decide_eq_true_iff, List.mem_drop_iff_getElem]
  constructor
  · intro h j hkj hj he
    apply h
    refine ⟨j - (k + 1), by omega, ?_⟩
    rw [← getElem!_pos l _ (by omega), show k + 1 + (j - (k + 1)) = j by omega, he]
  · rintro h ⟨j, hj, he⟩
    apply h (k + 1 + j) (by omega) (by omega)
    rw [getElem!_pos l _ (by omega), he]

-- `dedup` keeps the last copy of each element, in order.
theorem dedup_eq : ∀ l : List α, dedup l = ((List.range l.length).filter (isLast l)).map (l[·]!)
  | [] => rfl
  | a :: l => by
    have h1 : (isLast (a :: l) ∘ Nat.succ) = isLast l := by
      funext k; simp [isLast]
    have h2 : (((a :: l)[·]!) ∘ Nat.succ) = (l[·]!) := by
      funext k; simp
    rw [dedup_cons, List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map, h1]
    by_cases h : a ∈ l
    · rw [ite_eq_left ((mem_dedup l a).2 h), ite_eq_right (by simp [isLast, h]), List.map_map, h2,
        ← dedup_eq l]
    · rw [ite_eq_right (fun h' => h ((mem_dedup l a).1 h')), ite_eq_left (by simp [isLast, h]),
        List.map_cons, List.map_map, h2, ← dedup_eq l]
      rfl

end

-- The last position below `n` whose value is `f k` is `k` when no position above `k` has it.
theorem find?_last {α : Type} [BEq α] [LawfulBEq α] (f : Nat → α) {k : Nat} :
    ∀ n, k < n → ((List.range n).reverse.find? (fun j => f j == f k) = some k ↔
      ∀ j, k < j → j < n → f j ≠ f k)
  | 0, h => absurd h (Nat.not_lt_zero k)
  | n + 1, h => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append]
    by_cases hn : n = k
    · rw [hn, List.find?_cons_of_pos (by simp)]
      exact ⟨fun _ j h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
    · have hkn : k < n := by omega
      by_cases he : f n = f k
      · rw [List.find?_cons_of_pos (by simp [he])]
        exact ⟨fun h' => absurd (Option.some.inj h') hn, fun h' => absurd he (h' n hkn (by omega))⟩
      · rw [List.find?_cons_of_neg (by simp [he]), find?_last f n hkn]
        constructor
        · intro h' j h1 h2
          by_cases hj : j = n
          · rw [hj]; exact he
          · exact h' j h1 (by omega)
        · intro h' j h1 h2; exact h' j h1 (by omega)

end Bbu
