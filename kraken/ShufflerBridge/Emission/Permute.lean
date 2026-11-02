module

public import ShufflerBridge.Emission.SwapDest
import all ShufflerBridge.Emission.SwapDest
public import ShufflerBridge.Emission.SwapWith
import all ShufflerBridge.Emission.SwapWith
public import Shuffler.Permute.Normalization
import all Shuffler.Permute.Normalization

@[expose] public section

/-!
The final permutation of the model (`FlatShuffler.normalize`, then `FlatShuffler.go`) is the
original `Shuffler.Permute.permute` (`normalize`, then `permute.go`). The model
gets a permutation as the list of the destinations (`destList`).
-/

namespace ShufflerBridge.Emission

open Shuffler Shuffler.Emission

-- The model of a permutation: entry `i` is the destination of position `i`.
def destList {n : Nat} (perm : Equiv.Perm (Fin n)) : List Nat :=
  List.ofFn fun i => (perm i).val

theorem length_destList {n : Nat} (perm : Equiv.Perm (Fin n)) : (destList perm).length = n := by
  simp [destList]

theorem getElem_destList {n : Nat} (perm : Equiv.Perm (Fin n)) (i : Nat)
    (h : i < (destList perm).length) :
    (destList perm)[i] = (perm ⟨i, by simpa [length_destList] using h⟩).val := by
  simp [destList]

theorem isPerm_destList {n : Nat} (perm : Equiv.Perm (Fin n)) : FlatShuffler.IsPerm (destList perm) := by
  refine ⟨fun i h => ?_, fun i hi j hj hij => ?_⟩
  · rw [getElem_destList]; simp only [length_destList]
    exact (perm _).isLt
  · rw [getElem_destList, getElem_destList] at hij
    have := perm.injective (Fin.ext hij)
    simpa using this

theorem getElem!_destList {n : Nat} (perm : Equiv.Perm (Fin n)) (i : Fin n) :
    (destList perm)[i.val]! = (perm i).val := by
  rw [getElem!_pos (destList perm) i.val (by simp [length_destList]), getElem_destList]

theorem nodup_destList {n : Nat} (f : Equiv.Perm (Fin n)) : (destList f).Nodup :=
  List.nodup_ofFn.mpr (Fin.val_injective.comp f.injective)

-- The entry `b` of `destList f` is at `f.symm b`.
theorem idxOf_destList {n : Nat} (f : Equiv.Perm (Fin n)) (b : Fin n) :
    (destList f).idxOf b.val = (f.symm b).val := by
  have h : (f.symm b).val < (destList f).length := by simp [length_destList]
  have he : (destList f)[(f.symm b).val] = b.val := by
    rw [getElem_destList]; simp
  rw [← he]
  exact (nodup_destList f).idxOf_getElem _ h

theorem destList_setValue {n : Nat} (f : Equiv.Perm (Fin n)) (a b : Fin n) :
    destList (f.setValue a b) = FlatShuffler.setValue (destList f) a.val b.val := by
  apply List.ext_getElem
  · simp [FlatShuffler.setValue, length_destList]
  · intro k h1 h2
    have hk : k < n := by simpa [length_destList] using h1
    simp only [FlatShuffler.setValue, List.getElem_set, idxOf_destList, getElem!_destList, getElem_destList]
    simp only [Equiv.setValue, Equiv.trans_apply]
    by_cases hak : a.val = k
    · have : (⟨k, hk⟩ : Fin n) = a := Fin.ext hak.symm
      rw [ite_eq_left hak, this, Equiv.swap_apply_left, Equiv.apply_symm_apply]
    · rw [ite_eq_right hak]
      by_cases hbk : (f.symm b).val = k
      · have : (⟨k, hk⟩ : Fin n) = f.symm b := Fin.ext hbk.symm
        rw [ite_eq_left hbk, this, Equiv.swap_apply_right]
      · rw [ite_eq_right hbk, Equiv.swap_apply_of_ne_of_ne (fun h => hak (by rw [← h]))
          (fun h => hbk (by rw [← h]))]

/-! ## `normalize` -/

theorem map_val_finRange (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

theorem getElem!_map_val {n : Nat} (l : List (Fin n)) (i : Nat) (h : i < l.length) :
    (l.map Fin.val)[i]! = l[i].val := by
  rw [getElem!_pos (l.map Fin.val) i (by simpa using h), List.getElem_map]

theorem map_filter_mem {n : Nat} (l s : List (Fin n)) :
    (l.filter (· ∈ s)).map Fin.val = (l.map Fin.val).filter (· ∈ s.map Fin.val) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp_apply, List.mem_map_of_injective Fin.val_injective]

theorem map_filter_not_mem {n : Nat} (l s : List (Fin n)) :
    (l.filter (· ∉ s)).map Fin.val = (l.map Fin.val).filter (· ∉ s.map Fin.val) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp_apply, List.mem_map_of_injective Fin.val_injective]

theorem dedup_eq {α : Type} [DecidableEq α] (l : List α) : FlatShuffler.dedup l = l.dedup := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (if a ∈ FlatShuffler.dedup l then FlatShuffler.dedup l else a :: FlatShuffler.dedup l) = _
    rw [ih]
    by_cases ha : a ∈ l
    · rw [ite_eq_left (List.mem_dedup.mpr ha), List.dedup_cons_of_mem ha]
    · rw [ite_eq_right (mt List.mem_dedup.mp ha), List.dedup_cons_of_notMem ha]

-- `decodeStackSlot` is injective on canonical slots, so it keeps `dedup`.
theorem dedup_map_decode (vals : List FlatShuffler.StackSlot) (hc : ∀ v ∈ vals, StackSlotHasCanonicalEncoding v) :
    (vals.map decodeStackSlot).dedup = vals.dedup.map decodeStackSlot := by
  induction vals with
  | nil => rfl
  | cons a l ih =>
    have ha : StackSlotHasCanonicalEncoding a := hc a (by simp)
    have hl : ∀ v ∈ l, StackSlotHasCanonicalEncoding v := fun v hv => hc v (List.mem_cons_of_mem a hv)
    have hmem : decodeStackSlot a ∈ l.map decodeStackSlot ↔ a ∈ l := by
      constructor
      · intro h
        obtain ⟨b, hb, he⟩ := List.mem_map.mp h
        rwa [(decode_eq_iff (hl b hb) ha).mp he] at hb
      · exact List.mem_map_of_mem
    rw [List.map_cons]
    by_cases hal : a ∈ l
    · rw [List.dedup_cons_of_mem hal, List.dedup_cons_of_mem (hmem.mpr hal), ih hl]
    · rw [List.dedup_cons_of_notMem hal, List.dedup_cons_of_notMem (mt hmem.mp hal), ih hl,
        List.map_cons]

-- `FlatShuffler.regroup` is `Permute.reassignGroup`. Each list of the model is the list
-- of the original, mapped by `Fin.val`.
theorem regroup_corr (vals : List FlatShuffler.StackSlot) (hc : ∀ v ∈ vals, StackSlotHasCanonicalEncoding v) (slot : FlatShuffler.StackSlot)
    (hslot : StackSlotHasCanonicalEncoding slot) (perm : Permute.Permutation (vals.map decodeStackSlot)) :
    Corr (fun p s => ∃ q, s = .yield q ∧ p = destList q)
      (FlatShuffler.regroup vals (destList perm) slot)
      (Permute.reassignGroup (vals.map decodeStackSlot) (decodeStackSlot slot) perm) := by
  unfold FlatShuffler.regroup Permute.reassignGroup
  extract_lets Gm Dm Pm Mm Vm G D S P M V
  have hL : (vals.map decodeStackSlot).length = vals.length := List.length_map ..
  have hG : G.map Fin.val = Gm := by
    simp only [G, Gm]
    rw [show List.range vals.length = (List.finRange (vals.map decodeStackSlot).length).map Fin.val by
      rw [map_val_finRange, hL], List.filter_map]
    congr 1
    apply List.filter_congr
    intro pos _
    have hp : pos.val < vals.length := hL ▸ pos.isLt
    have hv := hc _ (List.getElem_mem hp)
    simp only [Function.comp_apply, Fin.getElem_fin, List.getElem_map, getElem!_pos vals pos.val hp]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, decode_eq_iff hv hslot]
  have hD : D.map Fin.val = Dm := by
    simp only [D, Dm]
    rw [List.map_mergeSort (s := fun a b => decide (a ≤ b)) (fun a _ b _ => by simp only [Fin.le_def]),
      ← hG, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x _
    exact (getElem!_destList perm x).symm
  have hP : Pm = destList P := by
    simp only [Pm, P, S]
    rw [← hG, ← hD, ← map_filter_mem, List.foldl_map]
    exact List.foldl_hom destList fun x y => (destList_setValue x y y).symm
  have hM : M.map Fin.val = Mm := by
    simp only [M, Mm]
    rw [map_filter_not_mem, hG, hD]
  have hV : V.map Fin.val = Vm := by
    simp only [V, Vm]
    rw [map_filter_not_mem, hD, hG]
  have hlenM : Mm.length = M.length := by rw [← hM, List.length_map]
  have hlenV : Vm.length = V.length := by rw [← hV, List.length_map]
  by_cases hsmall : G.length < 2
  · have hsm : Gm.length < 2 := by rw [← hG, List.length_map]; exact hsmall
    rw [ite_eq_left hsm, ite_eq_left hsmall]
    exact ⟨perm, rfl, rfl⟩
  have hsm : ¬ Gm.length < 2 := by rw [← hG, List.length_map]; exact hsmall
  rw [ite_eq_right hsm, ite_eq_right hsmall]
  by_cases hsz : M.length = V.length
  · have hne : ¬ Mm.length ≠ Vm.length := by rw [hlenM, hlenV]; exact not_not.mpr hsz
    rw [ite_eq_right hne, requires_of_true _ hsz]
    refine ⟨_, rfl, ?_⟩
    rw [hP, show List.range Mm.length = (List.finRange M.length).map Fin.val by
      rw [map_val_finRange, hlenM], List.foldl_map]
    apply List.foldl_hom destList
    intro x i
    rw [destList_setValue, ← hM, ← hV, getElem!_map_val M i i.isLt,
      getElem!_map_val V i (hsz ▸ i.isLt)]
    rfl
  · -- The sizes differ: both fail with an assertion.
    have hne : Mm.length ≠ Vm.length := by rw [hlenM, hlenV]; exact hsz
    rw [ite_eq_left hne, requires, dite_eq_right hsz]
    exact trivial

-- `FlatShuffler.normalize` is `Permute.normalize`. The slots are canonical, so equal
-- values are equal slots.
theorem normalize_corr (vals : List FlatShuffler.StackSlot) (hc : ∀ v ∈ vals, StackSlotHasCanonicalEncoding v) (stack : Stack)
    (hs : stack = vals.map decodeStackSlot) (perm : Permute.Permutation stack) :
    Corr (fun p r => p = destList r) (FlatShuffler.normalize vals (destList perm))
      (Permute.normalize stack perm) := by
  subst hs
  unfold FlatShuffler.normalize Permute.normalize
  rw [dedup_eq, dedup_map_decode vals hc]
  have hsub : ∀ v ∈ vals.dedup, StackSlotHasCanonicalEncoding v := fun v hv => hc v (List.mem_dedup.mp hv)
  generalize vals.dedup = xs at hsub ⊢
  induction xs generalizing perm with
  | nil => exact rfl
  | cons x xs ih =>
    rw [List.foldlM_cons, List.map_cons, List.forIn_cons]
    have hr := regroup_corr vals hc x (hsub x (by simp)) perm
    generalize FlatShuffler.regroup vals (destList perm) x = a at hr ⊢
    generalize Permute.reassignGroup (vals.map decodeStackSlot) (decodeStackSlot x) perm = b at hr ⊢
    rcases a with (_ | _) | p <;> rcases b with (_ | _) | s <;> simp only [Corr] at hr
    · exact trivial
    · obtain ⟨q, rfl, rfl⟩ := hr
      rw [except_ok_bind, except_ok_bind]
      exact ih q fun v hv => hsub v (List.mem_cons_of_mem _ hv)

/-! ## `permute.go` -/

theorem swapPos_len (st : FlatShuffler.St) (pos : Nat) : (FlatShuffler.swapPos st pos).len = st.len := by
  simp [FlatShuffler.swapPos, FlatShuffler.swapDestinations, FlatShuffler.St.len]

-- `destList` does not see a cast of the length.
theorem destList_heq {a b : Nat} {x : Equiv.Perm (Fin a)} {y : Equiv.Perm (Fin b)} (hab : a = b)
    (h : HEq x y) : destList x = destList y := by
  subst hab; cases h; rfl

-- A cast with `Eq.mpr` keeps the value.
theorem heq_mpr {α β : Sort _} (h : α = β) (b : β) : HEq b (Eq.mpr h b) := by
  subst h; rfl

-- `perm * Equiv.swap i j` exchanges the entries `i` and `j`.
theorem destList_mul_swap {n : Nat} (perm : Equiv.Perm (Fin n)) (i j : Fin n) :
    destList (perm * Equiv.swap i j) = FlatShuffler.Permutation.swapEntries (destList perm) i j := by
  apply List.ext_getElem
  · simp [FlatShuffler.Permutation.swapEntries, length_destList]
  · intro k h1 h2
    have hk : k < n := by simpa [length_destList] using h1
    simp only [FlatShuffler.Permutation.swapEntries, List.getElem_set, getElem!_destList, getElem_destList,
      Equiv.Perm.mul_apply]
    by_cases hkj : (j : Nat) = k
    · have : (⟨k, hk⟩ : Fin n) = j := Fin.ext hkj.symm
      rw [ite_eq_left hkj, this, Equiv.swap_apply_right]
    · rw [ite_eq_right hkj]
      by_cases hki : (i : Nat) = k
      · have : (⟨k, hk⟩ : Fin n) = i := Fin.ext hki.symm
        rw [ite_eq_left hki, this, Equiv.swap_apply_left]
      · rw [ite_eq_right hki, Equiv.swap_apply_of_ne_of_ne
          (fun h => hki (by rw [← h])) (fun h => hkj (by rw [← h]))]

-- If the top is out of place, `target` is the destination of the top.
theorem target_top {n : Nat} (perm : Equiv.Perm (Fin n)) (top : Fin n) (htop : top.val = n - 1)
    (ht : perm top ≠ top) : FlatShuffler.Permutation.target (destList perm) = some (perm top).val := by
  unfold FlatShuffler.Permutation.target
  dsimp only
  rw [length_destList, ← htop, getElem!_destList, ite_eq_left (fun h => ht (Fin.ext h))]

-- The `foldl` of `permute.go` is `FlatShuffler.Permutation.lastMisplaced`.
theorem foldl_misplaced {n : Nat} (perm : Equiv.Perm (Fin n)) (xs : List (Fin n))
    (acc : Option {i : Fin n // perm i ≠ i}) :
    (xs.foldl (fun p i => if h : perm i ≠ i then some ⟨i, h⟩ else p) acc).map (fun x => x.1.val) =
      (xs.map Fin.val).foldl (fun acc i => if (destList perm)[i]! ≠ i then some i else acc)
        (acc.map fun x => x.1.val) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, getElem!_destList]
    congr 1
    by_cases hx : perm x = x
    · simp [hx]
    · have : (perm x).val ≠ x.val := fun h => hx (Fin.ext h)
      simp [hx, this]

-- If the top is in place, `target` is the last out-of-place position.
theorem target_fixed {n : Nat} (perm : Equiv.Perm (Fin n)) (top : Fin n) (htop : top.val = n - 1)
    (ht : perm top = top) : FlatShuffler.Permutation.target (destList perm) =
      ((List.finRange n).foldl (fun p i => if h : perm i ≠ i then some ⟨i, h⟩ else p)
        (none : Option {i : Fin n // perm i ≠ i})).map
        (fun x => x.1.val) := by
  rw [foldl_misplaced, map_val_finRange]
  unfold FlatShuffler.Permutation.target FlatShuffler.Permutation.lastMisplaced
  dsimp only
  rw [length_destList, ← htop, getElem!_destList, ht, ite_eq_right (fun h => h rfl)]
  rfl

-- `FlatShuffler.go` with no position to swap.
theorem go_none {st : FlatShuffler.St} {p : FlatShuffler.Permutation.Perm} (h : FlatShuffler.Permutation.target p.toList = none) :
    FlatShuffler.go st p = .ok st := by
  rw [FlatShuffler.go]
  split
  · rfl
  · simp_all

-- One step of `FlatShuffler.go`.
theorem go_some {st : FlatShuffler.St} {p : FlatShuffler.Permutation.Perm} {pos : Nat}
    (h : FlatShuffler.Permutation.target p.toList = some pos) (hi : p.toList.length - 1 < p.toList.length)
    (hj : pos < p.toList.length) :
    FlatShuffler.go st p =
      if st.val pos = st.val (st.len - 1) then
        FlatShuffler.go (FlatShuffler.swapDestinations st pos (st.len - 1)) (p.swap _ pos hi hj)
      else if FlatShuffler.MAX_SWAP_DEPTH < st.len - 1 - pos then
        .error (.blocked pos (st.len - 1 - pos - FlatShuffler.MAX_SWAP_DEPTH) st)
      else FlatShuffler.go (FlatShuffler.swapPos st pos) (p.swap _ pos hi hj) := by
  rw [FlatShuffler.go]
  split
  · simp_all
  · rename_i pos' h'
    obtain rfl : pos' = pos := by simp_all
    rfl


theorem swapDestinations_len (st : FlatShuffler.St) (a b : Nat) : (FlatShuffler.swapDestinations st a b).len = st.len := by
  simp [FlatShuffler.swapDestinations, FlatShuffler.St.len]

-- The model and the original swap the slot at `pos` with the top in the same way.
theorem swapPos_rel {e : FlatShuffler.Env} {source : Stack} {st : FlatShuffler.St} {state : OState e source}
    (h : Rel e st state) (pos top : Fin state.stack.length) (htop : top.val = state.stack.length - 1)
    (hlt : pos.val < top.val) (idx : Nat) (hidx : idx = state.stack.length - 1 - pos.val)
    (h1 : idx < state.stack.length) (h2 : 1 ≤ idx) (h3 : idx ≤ MAX_SWAP_DEPTH) :
    Rel e (FlatShuffler.swapPos st pos)
      { state with
        stack := state.stack.swap (state.stack.length - 1) (state.stack.length - 1 - idx)
        trace := .Swap idx h1 h2 h3 state.trace
        mapping := List.length_swap.symm ▸ state.mapping.swapDestinations pos top } := by
  obtain ⟨t, htl⟩ := top
  simp only at htop hlt
  subst htop
  obtain ⟨pos, hp⟩ := pos
  simp only at hlt hidx ⊢
  have hl := h.len
  have hpl : pos < st.len := by omega
  have hsw : state.stack.length - 1 - idx = pos := by omega
  unfold FlatShuffler.swapPos
  dsimp only
  rw [swapDestinations_eta, swapWith_slots st pos _ hpl]
  refine ⟨?_, ?_, h.pendingGenerations, ?_, ?_,
    canon_set (canon_set h.canon (h.canonVal _)) (h.canonVal _), h.target⟩
  · show state.stack.swap (state.stack.length - 1) (state.stack.length - 1 - idx) = _
    rw [hsw, List.swap_comm, List.swap_eq_of_lt hp (by omega)]
    apply List.ext_getElem
    · simp only [List.length_set, List.length_map]; exact hl
    · intro i h1 h2
      have hg : ∀ k (hk : k < state.stack.length), state.stack[k] = decodeStackSlot (st.val k) :=
        fun k hk => h.get ⟨k, hk⟩
      have hi : i < st.slots.length := by simpa using h2
      simp only [List.getElem_map, List.getElem_set, hl]
      split_ifs <;> simp [hg, FlatShuffler.St.val, hi]
  · intro i
    obtain ⟨i, hi⟩ := i
    rw [mapping_cast_apply, Mapping.swapDestinations_apply, Equiv.swap_apply_def]
    have hn : st.len = st.slots.length := rfl
    have hi' : i < st.slots.length := by simp at hi; omega
    have hps : pos < st.slots.length := by omega
    have hsl : st.len - 1 < st.slots.length := by omega
    have hne : pos ≠ st.len - 1 := by omega
    split_ifs with h3 h4 <;> rw [h.dest] <;> simp only [Fin.ext_iff, Fin.val_cast, hl] at *
    · subst h3
      simp [FlatShuffler.St.dest, hps, hsl, Ne.symm hne]
    · subst h4
      simp [FlatShuffler.St.dest, hps, hsl]
    · simp [FlatShuffler.St.dest, hi', Ne.symm h3, Ne.symm h4]
  · simp [traceOperations, encodeTraceOperation, h.trace, hidx, hl]
  · refine (FlatShuffler.Pos.swapDest ?_ ?_ ?_).congr rfl ?_
    · exact h.pos.congr rfl (FlatShuffler.swapVals_dests st pos (st.len - 1))
    · simp only [FlatShuffler.St.len, List.length_set] at hpl ⊢; omega
    · simp only [FlatShuffler.St.len, List.length_set] at hpl ⊢; omega
    · unfold FlatShuffler.St.dests; rw [swapWith_slots st pos _ hpl]

-- One step of `FlatShuffler.go` at the position `pos` that `permute.go` finds.
theorem go_at {e : FlatShuffler.Env} {source : Stack} {st : FlatShuffler.St} {state : OState e source}
    (h : Rel e st state) {p : FlatShuffler.Permutation.Perm} {perm : Permute.Permutation state.stack}
    (hp : p.toList = destList perm) (top pos : Fin state.stack.length)
    (htop : top.val = state.stack.length - 1)
    (hT : FlatShuffler.Permutation.target p.toList = some pos.val) :
    ∃ p' : FlatShuffler.Permutation.Perm, p'.toList = destList (perm * Equiv.swap top pos) ∧
      FlatShuffler.go st p =
        if state.stack[pos] = state.stack[top] then FlatShuffler.go (FlatShuffler.swapDestinations st pos top) p'
        else if pos.rev.val > MAX_SWAP_DEPTH then
          .error (.blocked pos (pos.rev.val - MAX_SWAP_DEPTH) st)
        else FlatShuffler.go (FlatShuffler.swapPos st pos) p' := by
  have hl := h.len
  have hlen : p.toList.length = state.stack.length := by rw [hp, length_destList]
  have hi : p.toList.length - 1 < p.toList.length := by have := pos.isLt; omega
  have hj : pos.val < p.toList.length := by have := pos.isLt; omega
  refine ⟨p.swap _ pos hi hj, ?_, ?_⟩
  · show FlatShuffler.Permutation.swapEntries p.toList (p.toList.length - 1) pos = _
    rw [destList_mul_swap, ← hp, htop, hlen]
  · have ht : st.len - 1 = top.val := by omega
    have hr : top.val - pos.val = pos.rev.val := by rw [Fin.val_rev]; omega
    have hv : (st.val pos = st.val top) ↔ state.stack[pos] = state.stack[top] := by
      rw [h.get, h.get]; exact (decode_eq_iff (h.canonVal _) (h.canonVal _)).symm
    rw [go_some hT hi hj, ht, hr]
    simp only [hv]
    rfl

-- `FlatShuffler.go` keeps the stackSlotIdentity of slots.
theorem go_len (st : FlatShuffler.St) (p : FlatShuffler.Permutation.Perm) {st' : FlatShuffler.St} (h : FlatShuffler.go st p = .ok st') :
    st'.len = st.len := by
  revert st'
  refine FlatShuffler.go.induct_unfolding (motive := fun st _ r => ∀ {st' : FlatShuffler.St}, r = .ok st' → st'.len = st.len)
    ?none ?equal ?blocked ?swap st p
  case none =>
    intro st p _ st' h
    cases h; rfl
  case equal =>
    intro st p pos _ _ _ _ _ ih st' h
    exact (ih h).trans (swapDestinations_len _ _ _)
  case blocked =>
    intro st p pos _ _ _ _ _ st' h
    cases h
  case swap =>
    intro st p pos _ _ _ _ _ _ ih st' h
    exact (ih h).trans (swapPos_len _ _)

-- `FlatShuffler.go` is `permute.go`.
theorem go_corr {e : FlatShuffler.Env} {source : Stack} (st : FlatShuffler.St) (state : OState e source)
    (p : FlatShuffler.Permutation.Perm) (perm : Permute.Permutation state.stack) (hne : 0 < state.stack.length)
    (h : Rel e st state) (hp : p.toList = destList perm) :
    ResCorr (Rel e) (FlatShuffler.go st p) (Permute.permute.go state perm hne) := by
  revert st p
  refine Permute.permute.go.induct_unfolding
    (motive := fun state perm _ run => ∀ (st : FlatShuffler.St) (p : FlatShuffler.Permutation.Perm),
      Rel e st state → p.toList = destList perm → ResCorr (Rel e) (FlatShuffler.go st p) run)
    ?equal_top ?blocked_top ?swap_top ?equal_pos ?blocked_pos ?swap_pos ?done state perm hne
  case equal_top =>
    intro state perm hne top htop ht perm' he ih st p h hp
    obtain ⟨p', hp', hgo⟩ := go_at h hp top (perm top) htop (hp ▸ target_top perm top htop ht)
    rw [hgo, ite_eq_left he]
    exact ih _ _ (swapDest_rel h (perm top) top) hp'

  case blocked_top =>
    intro state perm hne top htop ht he idx hdepth st p h hp
    obtain ⟨p', hp', hgo⟩ := go_at h hp top (perm top) htop (hp ▸ target_top perm top htop ht)
    rw [hgo, ite_eq_right he, ite_eq_left hdepth, blockSwapUnreachable_eq state (perm top)
      (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth), depthOf_eq_rev]
    exact ⟨rfl, h⟩
  case swap_top =>
    intro state perm hne top htop ht perm' he idx hdepth stack' h1 h2 h3 trace' ih st p h hp
    obtain ⟨p', hp', hgo⟩ := go_at h hp top (perm top) htop (hp ▸ target_top perm top htop ht)
    rw [hgo, ite_eq_right he, ite_eq_right hdepth]
    have hlt : (perm top).val < top.val := by
      have : (perm top).val ≠ top.val := fun h' => ht (Fin.ext h')
      have := (perm top).isLt
      omega
    have hidx : idx = state.stack.length - 1 - (perm top).val := by
      show (perm top).rev.val = _
      rw [Fin.val_rev]; omega
    exact ih _ _ (swapPos_rel h (perm top) top htop hlt idx hidx h1 h2 h3)
      (hp'.trans (destList_heq List.length_swap.symm (heq_mpr _ _)))
  case equal_pos =>
    intro state perm hne top htop ht search pos hpos hsearch perm' he ih st p h hp
    have hT : FlatShuffler.Permutation.target p.toList = some pos.val := by
      rw [hp, target_fixed perm top htop (not_not.mp ht)]
      exact congrArg (Option.map fun x => x.1.val) hsearch
    obtain ⟨p', hp', hgo⟩ := go_at h hp top pos htop hT
    rw [hgo, ite_eq_left he]
    exact ih _ _ (swapDest_rel h pos top) hp'
  case blocked_pos =>
    intro state perm hne top htop ht search pos hpos hsearch he idx hdepth st p h hp
    have hT : FlatShuffler.Permutation.target p.toList = some pos.val := by
      rw [hp, target_fixed perm top htop (not_not.mp ht)]
      exact congrArg (Option.map fun x => x.1.val) hsearch
    obtain ⟨p', hp', hgo⟩ := go_at h hp top pos htop hT
    rw [hgo, ite_eq_right he, ite_eq_left hdepth, blockSwapUnreachable_eq state pos
      (by simpa only [State.isSwapReachable, depthOf_eq_rev, not_le] using hdepth), depthOf_eq_rev]
    exact ⟨rfl, h⟩
  case swap_pos =>
    intro state perm hne top htop ht search pos hpos hsearch perm' he idx hdepth hpos_ne hlt stack'
      h1 h2 h3 trace' ih st p h hp
    have hT : FlatShuffler.Permutation.target p.toList = some pos.val := by
      rw [hp, target_fixed perm top htop (not_not.mp ht)]
      exact congrArg (Option.map fun x => x.1.val) hsearch
    obtain ⟨p', hp', hgo⟩ := go_at h hp top pos htop hT
    rw [hgo, ite_eq_right he, ite_eq_right hdepth]
    have hidx : idx = state.stack.length - 1 - pos.val := by
      show pos.rev.val = _
      rw [Fin.val_rev]; omega
    exact ih _ _ (swapPos_rel h pos top htop hlt idx hidx h1 h2 h3)
      (hp'.trans (destList_heq List.length_swap.symm (heq_mpr _ _)))
  case done =>
    intro state perm hne top htop ht search hsearch st p h hp
    rw [go_none (by
      rw [hp, target_fixed perm top htop (not_not.mp ht)]
      exact congrArg (Option.map fun x => x.1.val) hsearch)]
    exact ⟨rfl, h⟩


end ShufflerBridge.Emission
