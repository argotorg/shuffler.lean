import BbuKraken.FlatPop

/-!
The flat model of the stack and mapping operations (`FlatPop.lean`, `FlatModel.lean`) is an
instance of the list model (`MapModel.lean`).

`absSt` reads a list state from a flat state: the slots and the destinations below the size,
the positions below the target size, the trace and `m_pendingGenerations`. A `NONE` word is
`none`.
-/

namespace Bbu.Flat

-- An `Optional<StackOffset>` as an `Option`.
def optOf (w : Word) : Option Nat := if w = NONE then none else some w.toNat

-- The list mapping of the arrays `dest` and `pos`, for `m` slots and `n` target offsets.
def absMapping (dest pos : Vector Word MAX_N) (m n : Word) : Map.Mapping :=
  ⟨(dest.toList.take m.toNat).map optOf, (pos.toList.take n.toNat).map optOf⟩

-- The list state of the flat state `st`, with the planned mapping `planned`.
def absSt (planned : Map.Mapping) (st : St) : Map.State where
  planned
  stack := st.data.toList.take st.size.toNat
  trace := st.trace
  mapping := absMapping st.dest st.pos st.size st.targetSize
  pend := st.pend.toNat

-- The list result of a flat result.
def absRes (planned : Map.Mapping) : Status × St → M Map.State
  | (.done, st) => .ok (absSt planned st)
  | _ => .error .assertion

/-! ## Lemmas on the arrays -/

theorem toNat_ofNat_lt {p : Nat} (h : p < MAX_N) : (BitVec.ofNat 64 p).toNat = p := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (by decide))

-- A word below `MAX_N` is not `NONE`.
theorem ne_none {w : Word} (h : w.toNat < MAX_N) : w ≠ NONE := by
  rintro rfl
  exact absurd h (by decide)

theorem optOf_none : optOf NONE = none := by simp [optOf]

theorem optOf_some {w : Word} (h : w ≠ NONE) : optOf w = some w.toNat := by simp [optOf, h]

theorem optOf_eq_none {w : Word} : optOf w = none ↔ w = NONE := by
  unfold optOf; split <;> simp_all

theorem get_ofNat {α : Type} [Inhabited α] (v : Vector α MAX_N) {p : Nat} (h : p < MAX_N) :
    get v (BitVec.ofNat 64 p) = v[p] := by
  simp [get, toNat_ofNat_lt h, h]

theorem get_toNat {α : Type} [Inhabited α] (v : Vector α MAX_N) {w : Word} (h : w.toNat < MAX_N) :
    get v w = v[w.toNat] := by
  simp [get, h]

-- The list of a `put`.
theorem abs_put (v : Vector Word MAX_N) (i x : Word) (n : Nat) :
    ((put v i x).toList.take n).map optOf = ((v.toList.take n).map optOf).set i.toNat (optOf x) := by
  simp only [put, Vector.toList_setIfInBounds, List.take_set, List.map_set]

theorem getElem_put {α : Type} (v : Vector α MAX_N) {p : Nat} (hp : p < MAX_N) (x : α) {i : Nat}
    (hi : i < MAX_N) : (put v (BitVec.ofNat 64 p) x)[i] = if p = i then x else v[i] := by
  simp only [put, Vector.getElem_setIfInBounds hi, toNat_ofNat_lt hp]

-- `put` at the offsets `p < j` with `c p`.
theorem fold_put_get {α : Type} (c : Nat → Prop) [DecidablePred c] (f : Nat → α) (v : Vector α MAX_N) {j : Nat}
    (hj : j ≤ MAX_N) {i : Nat} (hi : i < MAX_N) :
    ((List.range j).foldl (fun v p => if c p then put v (BitVec.ofNat 64 p) (f p) else v) v)[i]
      = if i < j ∧ c i then f i else v[i] := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjN : j < MAX_N := by omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hc : c j
    · rw [ite_eq_left hc, getElem_put _ hjN _ hi, ih (by omega)]
      by_cases hij : i = j
      · subst hij; simp [hc]
      · simp only [show j ≠ i from fun e => hij e.symm, ite_false,
          show i < j + 1 ↔ i < j by omega]
    · rw [ite_eq_right hc, ih (by omega)]
      by_cases hij : i = j
      · subst hij; simp [hc]
      · simp only [show i < j + 1 ↔ i < j by omega]

theorem fold_put_get' {α : Type} (f : Nat → α) (v : Vector α MAX_N) {j : Nat}
    (hj : j ≤ MAX_N) {i : Nat} (hi : i < MAX_N) :
    ((List.range j).foldl (fun v p => put v (BitVec.ofNat 64 p) (f p)) v)[i]
      = if i < j then f i else v[i] := by
  have := fold_put_get (fun _ => True) f v hj hi
  simpa using this

-- Two lists of `optOf` are equal if the arrays agree below `k`.
theorem abs_ext (v v' : Vector Word MAX_N) {k : Nat} (hk : k ≤ MAX_N)
    (h : ∀ i (hi : i < k), v[i]'(by omega) = v'[i]'(by omega)) :
    (v.toList.take k).map optOf = (v'.toList.take k).map optOf := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_take, Vector.getElem_toList]
  simp only [List.length_map, List.length_take, Vector.length_toList] at h1
  rw [h i (by omega)]

-- The number of `NONE` below `k`.
theorem countP_none (v : Vector Word MAX_N) {k : Nat} (hk : k ≤ MAX_N) :
    ((List.range k).map (BitVec.ofNat 64)).countP (fun d => get v d = NONE)
      = ((v.toList.take k).map optOf).count none := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkN : k < MAX_N := by omega
    rw [List.range_succ, List.map_append, List.countP_append, ih (by omega), List.take_add_one,
      List.map_append, List.count_append]
    by_cases hv : v[k] = NONE <;> simp [get_ofNat v hkN, hkN, hv, optOf_none, optOf_some]

-- `foldl` keeps a relation.
theorem foldl_rel {α β γ : Type} (R : α → β → Prop) (f : α → γ → α) (g : β → γ → β)
    (l : List γ) (h : ∀ a b x, x ∈ l → R a b → R (f a x) (g b x)) {a : α} {b : β}
    (hab : R a b) : R (l.foldl f a) (l.foldl g b) := by
  induction l generalizing a b with
  | nil => exact hab
  | cons x l ih =>
    exact ih (fun a b y hy => h a b y (List.mem_cons_of_mem x hy)) (h a b x (by simp) hab)

/-! ## `pop` -/

theorem take_ne_nil {α : Type} (v : Vector α MAX_N) {k : Nat} (h0 : k ≠ 0) : v.toList.take k ≠ [] := by
  rw [ne_eq, List.take_eq_nil_iff]
  rintro (h | h)
  · exact h0 h
  · have := v.length_toList; rw [h] at this; simp [MAX_N] at this

theorem getLast_abs (v : Vector Word MAX_N) {k : Nat} (h0 : k ≠ 0) (h : k ≤ MAX_N) :
    ((v.toList.take k).map optOf).getLast? = some (optOf (v[k - 1]'(by omega))) := by
  rw [List.getLast?_map, List.getLast?_take, ite_eq_right h0]
  simp [show k - 1 < MAX_N by omega]

theorem dropLast_take' {α : Type} (v : Vector α MAX_N) {k : Nat} (h : k ≤ MAX_N) :
    (v.toList.take k).dropLast = v.toList.take (k - 1) :=
  List.dropLast_take (by simpa using h)

theorem dropLast_abs {α β : Type} (f : α → β) (v : Vector α MAX_N) {k : Nat} (h : k ≤ MAX_N) :
    ((v.toList.take k).map f).dropLast = (v.toList.take (k - 1)).map f := by
  rw [← List.map_dropLast, dropLast_take' v h]

theorem pop_none (st : St) (h : st.size ≠ 0) (hd : get st.dest (st.size - 1) = NONE) :
    pop st = (.done, { st with size := st.size - 1, trace := st.trace ++ [Op.pop] }) := by
  unfold pop stackPop mappingPop
  rw [ite_eq_right h]
  dsimp only
  simp only [ne_eq, not_true_eq_false, ite_false, hd]

theorem pop_some (st : St) (h : st.size ≠ 0) (hd : get st.dest (st.size - 1) ≠ NONE) :
    pop st = (.done, { st with size := st.size - 1, trace := st.trace ++ [Op.pop],
                               pos := put st.pos (get st.dest (st.size - 1)) NONE }) := by
  unfold pop stackPop mappingPop
  rw [ite_eq_right h]
  dsimp only
  simp only [ne_eq, not_true_eq_false, ite_false, hd, not_false_eq_true, ite_true]

theorem pop_size (st : St) (h : st.size.toNat ≤ MAX_N) : (pop st).2.size.toNat ≤ MAX_N := by
  by_cases h0 : st.size = 0
  · simp [pop, stackPop, h0]
  · have : (st.size - 1).toNat ≤ st.size.toNat := by bv_omega
    by_cases hn : get st.dest (st.size - 1) = NONE
    · rw [pop_none st h0 hn]; exact Nat.le_trans this h
    · rw [pop_some st h0 hn]; exact Nat.le_trans this h

theorem pop_abs (planned : Map.Mapping) (st : St) (h : st.size.toNat ≤ MAX_N) :
    (absSt planned st).pop = absRes planned (pop st) := by
  by_cases h0 : st.size = 0
  · have hs : (absSt planned st).stack = [] := by simp [absSt, h0]
    simp [Map.State.pop, hs, pop, stackPop, h0, absRes]
  · have hk : st.size.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e))
    have hs1 : (st.size - 1).toNat = st.size.toNat - 1 := by bv_omega
    have hne : (absSt planned st).stack ≠ [] := take_ne_nil st.data hk
    have hl := getLast_abs st.dest hk h
    have hg : get st.dest (st.size - 1) = st.dest[st.size.toNat - 1]'(by omega) := by
      rw [get_toNat _ (by omega)]; simp only [hs1]
    unfold Map.State.pop
    rw [ite_eq_right hne]
    by_cases hn : get st.dest (st.size - 1) = NONE
    · rw [pop_none st h0 hn]
      rw [hg] at hn
      simp only [absRes, absSt, absMapping, Map.Mapping.pop, hl, hn, optOf_none, hs1,
        dropLast_abs _ _ h, dropLast_take' _ h]
    · rw [pop_some st h0 hn]
      rw [hg] at hn ⊢
      simp only [absRes, absSt, absMapping, Map.Mapping.pop, hl, optOf_some hn, hs1,
        dropLast_abs _ _ h, dropLast_take' _ h, abs_put, optOf_none]

theorem popLoop_abs (planned : Map.Mapping) (st : St) (count : Nat)
    (h : st.size.toNat ≤ MAX_N) :
    (absSt planned st).pops count = absRes planned (popLoop st count) := by
  induction count generalizing st with
  | zero => rfl
  | succ count ih =>
    simp only [Map.State.pops, popLoop, pop_abs planned st h]
    have hsz := pop_size st h
    revert hsz
    obtain ⟨r, st'⟩ := pop st
    intro hsz
    cases r with
    | done => exact ih st' hsz
    | blocked => rfl
    | assertionFailed => rfl

/-! ## `push` and `dup`: `Mapping::bind` of the new top -/

theorem toNat_add_one {w : Word} (h : w.toNat < MAX_N) : (w + 1).toNat = w.toNat + 1 := by
  have h' : w.toNat < 1024 := h
  bv_omega

-- `Mapping::bind` of a new top at `sz` for `d`.
theorem bind_top_abs (dest pos : Vector Word MAX_N) (sz n d : Word) (hs : sz.toNat < MAX_N)
    (hd : d ≠ NONE) :
    absMapping (put dest sz d) (put pos d sz) (sz + 1) n = (absMapping dest pos sz n).push d.toNat := by
  have hk : sz.toNat ≤ MAX_N := Nat.le_of_lt hs
  unfold absMapping Map.Mapping.push
  dsimp only
  congr 1
  · rw [toNat_add_one hs, List.take_add_one, List.map_append]
    have h1 : (put dest sz d).toList.take sz.toNat = dest.toList.take sz.toNat := by
      simp only [put, Vector.toList_setIfInBounds, List.take_set]
      exact List.set_eq_of_length_le (by simp; omega)
    have h2 : (put dest sz d).toList[sz.toNat]? = some d := by simp [put, hs]
    rw [h1, h2]
    simp [optOf_some hd]
  · rw [abs_put, optOf_some (ne_none hs)]
    simp [hk]

theorem push_abs {st st' : St} {slot : StackSlot} {d : Word} (h : push st slot d = (.done, st'))
    (hs : st.size.toNat < MAX_N) (hd : d ≠ NONE) :
    absMapping st'.dest st'.pos st'.size st'.targetSize =
      (absMapping st.dest st.pos st.size st.targetSize).push d.toNat := by
  unfold push at h
  dsimp only at h
  split at h
  · simp at h
  · cases h
    simp only [bind, stackPush, BitVec.add_sub_cancel]
    exact bind_top_abs _ _ _ _ _ hs hd

theorem dup_abs {st st' : St} {copy d : Word} (h : dup st copy d = (.done, st'))
    (hs : st.size.toNat < MAX_N) (hd : d ≠ NONE) :
    absMapping st'.dest st'.pos st'.size st'.targetSize =
      (absMapping st.dest st.pos st.size st.targetSize).push d.toNat := by
  unfold dup at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · cases h
      simp only [bind, stackDup, BitVec.add_sub_cancel]
      exact bind_top_abs _ _ _ _ _ hs hd

/-! ## The constructors -/

-- `NONE` at the offsets below `k`.
theorem fill_abs (v : Vector Word MAX_N) {k : Nat} (hk : k ≤ MAX_N) :
    ((((List.range k).map (BitVec.ofNat 64)).foldl (fun v p => put v p NONE) v).toList.take k).map optOf
      = List.replicate k none := by
  rw [List.foldl_map]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_map, List.length_take, Vector.length_toList] at h1
  simp only [List.getElem_map, List.getElem_take, Vector.getElem_toList, List.getElem_replicate]
  rw [fold_put_get' (fun _ => NONE) v hk (by omega)]
  simp [show i < k by omega, optOf_none]

-- A copy of `w` at the offsets below `k`.
theorem copy_abs (v w : Vector Word MAX_N) {k : Nat} (hk : k ≤ MAX_N) :
    ((((List.range k).map (BitVec.ofNat 64)).foldl (fun v p => put v p (get w p)) v).toList.take k).map optOf
      = (w.toList.take k).map optOf := by
  rw [List.foldl_map]
  apply abs_ext _ _ hk
  intro i hi
  rw [fold_put_get' (fun p => get w (BitVec.ofNat 64 p)) v hk (by omega)]
  simp [hi, get_ofNat w (show i < MAX_N by omega)]

theorem plan_abs (u : Mapping) (m n : Word) (dests : Vector Word MAX_N)
    (hm : m.toNat ≤ MAX_N) (hn : n.toNat ≤ MAX_N) :
    absMapping (plan u m n dests).dest (plan u m n dests).pos m n =
      Map.plan m.toNat n.toNat ((dests.toList.take m.toNat).map optOf) := by
  unfold plan Map.plan
  rw [offsets, List.foldl_map]
  refine foldl_rel (fun (M : Mapping) (L : Map.Mapping) => absMapping M.dest M.pos m n = L)
    _ _ _ ?_ ?_
  · intro M L p hp hR
    rw [List.mem_range] at hp
    have hpN : p < MAX_N := by omega
    have hg : ((dests.toList.take m.toNat).map optOf).getD p none = optOf dests[p] := by
      simp [hp, hpN]
    rw [get_ofNat dests hpN, hg]
    by_cases hd : dests[p] = NONE
    · simp only [hd, ne_eq, not_true_eq_false, ite_false, optOf_none]
      exact hR
    · simp only [hd, ne_eq, not_false_eq_true, ite_true, optOf_some hd]
      rw [← hR]
      simp only [Mapping.bind, absMapping, Map.Mapping.bind, abs_put, toNat_ofNat_lt hpN,
        optOf_some hd, optOf_some (ne_none ((toNat_ofNat_lt hpN).symm ▸ hpN))]
  · simp only [Mapping.init, absMapping, Map.Mapping.empty, offsets]
    rw [fill_abs _ hm, fill_abs _ hn]

-- The loop of the constructor on `m_pendingGenerations`.
theorem pend_fold (l : List Word) (st : St) :
    l.foldl (fun st d => if get st.pos d = NONE then { st with pend := st.pend + 1 } else st) st
      = { st with pend := st.pend + BitVec.ofNat 64 (l.countP (fun d => get st.pos d = NONE)) } := by
  induction l generalizing st with
  | nil => simp
  | cons d l ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    by_cases h : get st.pos d = NONE
    · simp only [h, ite_true, decide_true]
      congr 1
      rw [BitVec.ofNat_add]
      bv_omega
    · simp only [h, ite_false, decide_false, Bool.false_eq_true, Nat.add_zero]

theorem countP_none' (v : Vector Word MAX_N) (k : Word) (hk : k.toNat ≤ MAX_N) :
    (offsets k).countP (fun d => get v d = NONE) = ((v.toList.take k.toNat).map optOf).count none :=
  countP_none v hk

theorem ctorP_abs (data : Vector StackSlot MAX_N) (m : Word) (target : Vector StackSlot MAX_N)
    (n : Word) (planned : Mapping) (spills : BitVec 32 → BitVec 8) (u : Uninit)
    (hm : m.toNat ≤ MAX_N) (hn : n.toNat ≤ MAX_N) :
    absSt (absMapping planned.dest planned.pos m n) (ctorP data m target n planned spills u) =
      Map.State.init (data.toList.take m.toNat) (absMapping planned.dest planned.pos m n) := by
  unfold ctorP
  dsimp only
  rw [pend_fold, countP_none' _ _ hn]
  simp only [absSt, Map.State.init, Map.State.mk.injEq, true_and, absMapping, Mapping.copy, offsets,
    copy_abs _ _ hm, copy_abs _ _ hn]
  have hc : ((planned.pos.toList.take n.toNat).map optOf).count none ≤ n.toNat := by
    have := List.count_le_length (a := none) (l := (planned.pos.toList.take n.toNat).map optOf)
    simp only [List.length_map, List.length_take, Vector.length_toList] at this
    omega
  have hc' : n.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hn (by decide)
  generalize ((planned.pos.toList.take n.toNat).map optOf).count none = c at hc ⊢
  have hc2 : c < 2 ^ 64 := by omega
  simp [Nat.mod_eq_of_lt hc2]

/-! ## `ctorP` of `plan` is `ctor` -/

theorem none_toNat : NONE.toNat = 2 ^ 64 - 1 := by decide

theorem none_toNat_ne {i : Nat} (hi : i < MAX_N) : NONE.toNat ≠ i := by
  have : i < 1024 := hi
  rw [none_toNat]; omega

theorem getElem_put_ne {α : Type} (v : Vector α MAX_N) (a : Word) (x : α) {i : Nat}
    (hi : i < MAX_N) (h : a.toNat ≠ i) : (put v a x)[i] = v[i] := by
  simp only [put, Vector.getElem_setIfInBounds hi, h, ite_false]

theorem getElem_put_eq {α : Type} (v : Vector α MAX_N) (a : Word) (x : α) {i : Nat}
    (hi : i < MAX_N) (h : a.toNat = i) : (put v a x)[i] = x := by
  simp only [put, Vector.getElem_setIfInBounds hi, h, ite_true]

-- `put` at `NONE` does not change the array.
theorem put_none {α : Type} (v : Vector α MAX_N) (x : α) : put v NONE x = v := by
  apply Vector.ext
  intro i hi
  exact getElem_put_ne v NONE x hi (none_toNat_ne hi)

-- Two loops of the same `put`s keep the agreement at the offsets `i` with `S i`.
theorem fold_agree {γ : Type} (S : Nat → Prop) (l : List γ) (a b : γ → Word)
    (v w : Vector Word MAX_N) (h : ∀ i (hi : i < MAX_N), S i → v[i] = w[i]) :
    ∀ i (hi : i < MAX_N), S i →
      (l.foldl (fun v x => put v (a x) (b x)) v)[i] = (l.foldl (fun v x => put v (a x) (b x)) w)[i] := by
  induction l generalizing v w with
  | nil => exact h
  | cons x l ih =>
    apply ih
    intro i hi hs
    by_cases e : (a x).toNat = i
    · rw [getElem_put_eq _ _ _ hi e, getElem_put_eq _ _ _ hi e]
    · rw [getElem_put_ne _ _ _ hi e, getElem_put_ne _ _ _ hi e, h i hi hs]

-- A loop of `put`s at offsets other than `i` does not change `v[i]`.
theorem fold_other {γ : Type} (l : List γ) (a b : γ → Word) (v : Vector Word MAX_N) {i : Nat}
    (hi : i < MAX_N) (h : ∀ x ∈ l, (a x).toNat ≠ i) :
    (l.foldl (fun v x => put v (a x) (b x)) v)[i] = v[i] := by
  induction l generalizing v with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, ih _ (fun y hy => h y (List.mem_cons_of_mem x hy)),
      getElem_put_ne _ _ _ hi (h x (by simp))]

theorem fill_get (v : Vector Word MAX_N) (k : Word) (hk : k.toNat ≤ MAX_N) {i : Nat}
    (hi : i < MAX_N) :
    ((offsets k).foldl (fun v p => put v p NONE) v)[i] = if i < k.toNat then NONE else v[i] := by
  rw [offsets, List.foldl_map]
  exact fold_put_get' (fun _ => NONE) v hk hi

theorem copy_get (v w : Vector Word MAX_N) (k : Word) (hk : k.toNat ≤ MAX_N) {i : Nat}
    (hi : i < MAX_N) :
    ((offsets k).foldl (fun v p => put v p (get w p)) v)[i] = if i < k.toNat then w[i] else v[i] := by
  rw [offsets, List.foldl_map, fold_put_get' (fun p => get w (BitVec.ofNat 64 p)) v hk hi]
  by_cases h : i < k.toNat <;> simp only [h, ite_true, ite_false, get_ofNat w hi]

-- The loop of `ctor` on `m_positionOf`.
theorem fill_fold (l : List Word) (st : St) :
    l.foldl (fun st d => { st with pos := put st.pos d NONE }) st =
      { st with pos := l.foldl (fun v d => put v d NONE) st.pos } := by
  induction l generalizing st with
  | nil => rfl
  | cons d l ih => simp only [List.foldl_cons, ih]

-- The loop of `ctor` on the bindings.
theorem bind_fold (l : List Word) (dests : Vector Word MAX_N) (st : St) :
    l.foldl (fun st p => bind st p (get dests p)) st =
      { st with dest := l.foldl (fun v p => put v p (get dests p)) st.dest,
                pos := l.foldl (fun v p => put v (get dests p) p) st.pos } := by
  induction l generalizing st with
  | nil => rfl
  | cons p l ih => rw [List.foldl_cons, ih]; rfl

-- The loop of `plan`. A `put` at `NONE` does not change `pos`.
theorem plan_fold (l : List Word) (dests : Vector Word MAX_N) (M : Mapping) :
    l.foldl (fun M p => if get dests p ≠ NONE then M.bind p (get dests p) else M) M =
      ⟨l.foldl (fun v p => if get dests p ≠ NONE then put v p (get dests p) else v) M.dest,
       l.foldl (fun v p => put v (get dests p) p) M.pos⟩ := by
  induction l generalizing M with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldl_cons, ih]
    by_cases hd : get dests p = NONE
    · simp only [hd, ne_eq, not_true_eq_false, ite_false, put_none]
    · simp only [hd, ne_eq, not_false_eq_true, ite_true, Mapping.bind]

theorem plan_dest_get (u : Mapping) (m n : Word) (dests : Vector Word MAX_N)
    (hm : m.toNat ≤ MAX_N) {i : Nat} (hi : i < m.toNat) :
    (plan u m n dests).dest[i]'(by omega) = dests[i]'(by omega) := by
  have hiN : i < MAX_N := by omega
  unfold plan
  rw [plan_fold]
  dsimp only
  rw [offsets, List.foldl_map,
    fold_put_get (fun p => get dests (BitVec.ofNat 64 p) ≠ NONE)
      (fun p => get dests (BitVec.ofNat 64 p)) _ hm hiN]
  change (if _ then _ else ((offsets m).foldl (fun v p => put v p NONE) u.dest)[i]) = _
  rw [fill_get _ _ hm hiN]
  simp only [get_ofNat dests hiN, hi, true_and, ite_true]
  by_cases hd : dests[i] = NONE <;> simp [hd]

theorem plan_pos (u : Mapping) (m n : Word) (dests : Vector Word MAX_N) :
    (plan u m n dests).pos =
      (offsets m).foldl (fun v p => put v (get dests p) p) ((offsets n).foldl (fun v d => put v d NONE) u.pos) := by
  unfold plan
  rw [plan_fold]
  rfl

-- The constructor of `FlatModel.lean` is the constructor of the C++ with `plan`, if each
-- destination is none or below `n`.
theorem ctorP_plan (data : Vector StackSlot MAX_N) (m : Word) (target : Vector StackSlot MAX_N)
    (n : Word) (dests : Vector Word MAX_N) (spills : BitVec 32 → BitVec 8) (u : Uninit)
    (up : Mapping) (hm : m.toNat ≤ MAX_N) (hn : n.toNat ≤ MAX_N)
    (hd : ∀ p < m.toNat, get dests (.ofNat 64 p) = NONE ∨ (get dests (.ofNat 64 p)).toNat < n.toNat) :
    ctorP data m target n (plan up m n dests) spills u = ctor data m target n dests spills u := by
  unfold ctorP ctor
  dsimp only
  rw [fill_fold, bind_fold]
  congr 1
  dsimp only
  congr 1
  · apply Vector.ext
    intro i hi
    simp only [Mapping.copy]
    rw [copy_get _ _ _ hm hi, copy_get _ _ _ hm hi]
    by_cases him : i < m.toNat
    · simp only [him, ite_true]
      exact plan_dest_get up m n dests hm him
    · simp only [him, ite_false]
  · apply Vector.ext
    intro i hi
    simp only [Mapping.copy]
    rw [copy_get _ _ _ hn hi]
    by_cases hin : i < n.toNat
    · rw [ite_eq_left hin, plan_pos]
      refine fold_agree (· < n.toNat) _ (fun p => get dests p) (fun p => p) _ _ ?_ i hi hin
      intro j hj hjn
      rw [fill_get _ _ hn hj, fill_get _ _ hn hj, ite_eq_left hjn, ite_eq_left hjn]
    · rw [ite_eq_right hin, fold_other _ (fun p => get dests p) (fun p => p) _ hi, fill_get _ _ hn hi,
        ite_eq_right hin]
      intro x hx
      rw [offsets, List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      rw [List.mem_range] at hq
      rcases hd q hq with h | h
      · rw [h]; exact none_toNat_ne hi
      · omega

end Bbu.Flat
