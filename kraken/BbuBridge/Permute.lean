import Shuffler.Permute.Theorems
import PermuteKraken.Model

/-!
The Kraken model of permute (`PermuteKraken.permute`) equals the original
`Shuffler.Permute.permute`. The model gets the permutation as the list of the
destinations (`destList`), and gives the depths of the swaps. The original gives
a trace; `traceOps` reads its ops in order of application.
-/

namespace BbuBridge

-- The model of a permutation: entry `i` is the destination of position `i`.
def destList {n : Nat} (perm : Equiv.Perm (Fin n)) : List Nat :=
  List.ofFn fun i => (perm i).val

-- One op of a trace.
inductive TraceOp where
  | swap (depth : Nat)
  | dup (depth : Nat)
  | pop
  | push (v : Value)
  | load (id : VarId)

-- The ops of a trace, in order of application.
def traceOps : Trace spills source result → List TraceOp
  | .Lit _ => []
  | .Swap idx _ _ _ t => traceOps t ++ [.swap idx]
  | .Dup idx _ _ _ t => traceOps t ++ [.dup idx]
  | .Pop _ t => traceOps t ++ [.pop]
  | .Push v _ t => traceOps t ++ [.push v]
  | .Load id _ t => traceOps t ++ [.load id]

theorem traceOps_concat (t1 : Trace spills a b) (t2 : Trace spills b c) :
    traceOps (t1.concat t2) = traceOps t1 ++ traceOps t2 := by
  induction t2 <;> simp_all [Trace.concat, traceOps]

/-! ## The model -/

namespace Model
open PermuteKraken

theorem permute_done (p : Perm) (h : step p.toList = .done) : permute p = .ok [] := by
  rw [permute]; split <;> simp_all

theorem permute_blocked (p : Perm) {b : PermuteKraken.Blocked} (h : step p.toList = .blocked b) :
    permute p = .error b := by
  rw [permute]; split <;> simp_all

theorem permute_swap (p : Perm) {idx pos : Nat} (h : step p.toList = .swap idx pos) :
    permute p = (permute p.advance).map (idx :: ·) := by
  rw [permute]; split <;> simp_all

theorem advance_toList (p : Perm) {idx pos : Nat} (h : step p.toList = .swap idx pos) :
    p.advance.toList = swapEntries p.toList (p.toList.length - 1) pos := by
  unfold Perm.advance
  split <;> simp_all [Perm.swap]

end Model

/-! ## The destination list -/

theorem length_destList {n : Nat} (perm : Equiv.Perm (Fin n)) : (destList perm).length = n := by
  simp [destList]

theorem getElem!_destList {n : Nat} (perm : Equiv.Perm (Fin n)) (i : Fin n) :
    (destList perm)[i.val]! = (perm i).val := by
  rw [getElem!_pos (destList perm) i.val (by simp [length_destList])]
  simp [destList]

-- The search of the original for the last out-of-place position.
abbrev search {n : Nat} (perm : Equiv.Perm (Fin n)) : Option {i : Fin n // perm i ≠ i} :=
  (List.finRange n).foldl (fun p i => if h : perm i ≠ i then some ⟨i, h⟩ else p) none

theorem map_foldl_search {n : Nat} (perm : Equiv.Perm (Fin n)) (xs : List (Fin n))
    (acc : Option {i : Fin n // perm i ≠ i}) :
    (xs.foldl (fun p i => if h : perm i ≠ i then some ⟨i, h⟩ else p) acc).map (·.1.val)
      = (xs.map Fin.val).foldl (fun acc i => if (destList perm)[i]! ≠ i then some i else acc)
          (acc.map (·.1.val)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, getElem!_destList]
    by_cases hx : perm x = x
    · simp [hx]
    · simp [hx, Fin.val_ne_of_ne hx]

theorem lastMisplaced_destList {n : Nat} (perm : Equiv.Perm (Fin n)) :
    PermuteKraken.lastMisplaced (destList perm) n = (search perm).map (·.1.val) := by
  rw [search, map_foldl_search, List.map_coe_finRange_eq_range]
  rfl

-- `step` when the top is out of place.
theorem step_top {n : Nat} (perm : Equiv.Perm (Fin n)) (top : Fin n) (htop : top.val = n - 1)
    (ht : perm top ≠ top) :
    PermuteKraken.step (destList perm) =
      if (perm top).rev.val > MAX_SWAP_DEPTH
      then .blocked ⟨(perm top).val, (perm top).rev.val - MAX_SWAP_DEPTH⟩
      else .swap (perm top).rev.val (perm top).val := by
  have hn : n ≠ 0 := by have := top.isLt; omega
  have htop' := getElem!_destList perm top
  rw [htop] at htop'
  have hne : (perm top).val ≠ n - 1 := by rw [← htop]; exact Fin.val_ne_of_ne ht
  simp only [PermuteKraken.step, PermuteKraken.target, length_destList, htop', hn, hne,
    ↓reduceIte, ne_eq, not_false_eq_true, Fin.val_rev]
  split_ifs <;> simp_all [MAX_SWAP_DEPTH, PermuteKraken.MAX_SWAP_DEPTH] <;> omega

-- `step` when the top is in place and the search finds `pos`.
theorem step_pos {n : Nat} (perm : Equiv.Perm (Fin n)) (top : Fin n) (htop : top.val = n - 1)
    (ht : perm top = top) (pos : Fin n) (hpos : perm pos ≠ pos)
    (hsearch : search perm = some ⟨pos, hpos⟩) :
    PermuteKraken.step (destList perm) =
      if pos.rev.val > MAX_SWAP_DEPTH
      then .blocked ⟨pos.val, pos.rev.val - MAX_SWAP_DEPTH⟩
      else .swap pos.rev.val pos.val := by
  have hn : n ≠ 0 := by have := top.isLt; omega
  have htop' := getElem!_destList perm top
  rw [htop, ht] at htop'
  have hl := lastMisplaced_destList perm
  rw [hsearch] at hl
  simp only [PermuteKraken.step, PermuteKraken.target, length_destList, htop', hn, htop, hl,
    ↓reduceIte, ne_eq, not_true_eq_false, Option.map_some, Fin.val_rev]
  split_ifs <;> simp_all [MAX_SWAP_DEPTH, PermuteKraken.MAX_SWAP_DEPTH] <;> omega

-- `step` when the top is in place and the search finds nothing.
theorem step_none {n : Nat} (perm : Equiv.Perm (Fin n)) (top : Fin n) (htop : top.val = n - 1)
    (ht : perm top = top) (hsearch : search perm = none) :
    PermuteKraken.step (destList perm) = .done := by
  have hn : n ≠ 0 := by have := top.isLt; omega
  have htop' := getElem!_destList perm top
  rw [htop, ht] at htop'
  have hl := lastMisplaced_destList perm
  rw [hsearch] at hl
  simp [PermuteKraken.step, PermuteKraken.target, length_destList, htop', hn, htop, hl]

-- A swap of the top with `pos` in the model is the product with `Equiv.swap top pos`.
theorem swapEntries_destList {n : Nat} (perm : Equiv.Perm (Fin n)) (top pos : Fin n)
    (htop : top.val = n - 1) :
    PermuteKraken.swapEntries (destList perm) (n - 1) pos.val
      = destList (perm * Equiv.swap top pos) := by
  rw [← htop]
  apply List.ext_getElem
  · simp [PermuteKraken.swapEntries, length_destList]
  intro k hk _
  simp only [PermuteKraken.swapEntries, List.length_set, length_destList] at hk
  simp only [PermuteKraken.swapEntries, getElem!_destList]
  simp only [List.getElem_set, destList, List.getElem_ofFn, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def]
  rcases eq_or_ne pos top with rfl | hpt <;> split_ifs <;> simp_all [Fin.ext_iff]

/-! ## The induction over `permute.go` -/

-- The model result `m` agrees with the original result `o`, where the trace of
-- the original starts with the ops `pre`.
def Agrees (m : Except PermuteKraken.Blocked (List Nat))
    (o : Except ShuffleErr ((res : Stack) × Trace spills source res)) (pre : List TraceOp) :
    Prop :=
  match m with
  | .ok swaps => ∃ res t, o = .ok ⟨res, t⟩ ∧ traceOps t = pre ++ swaps.map .swap
  | .error b => o = .error (.Blocked ⟨b.offset, b.excess⟩)

theorem agrees_map {m : Except PermuteKraken.Blocked (List Nat)}
    {o : Except ShuffleErr ((res : Stack) × Trace spills source res)} {pre : List TraceOp}
    {idx : Nat} (h : Agrees m o (pre ++ [.swap idx])) : Agrees (m.map (idx :: ·)) o pre := by
  cases m <;> simp_all [Agrees, Except.map]

theorem go_agrees (spills : SpillSet) (source : Stack) (hne : source.length > 0)
    (current : Stack) (perm : Shuffler.Permute.Permutation source)
    (trace : Trace spills source current) (hlen : current.length = source.length)
    (p : PermuteKraken.Perm) (hp : p.toList = destList perm) :
    Agrees (PermuteKraken.permute p)
      (Shuffler.Permute.permute.go spills source current perm trace hne hlen) (traceOps trace) := by
  refine Shuffler.Permute.permute.go.induct_unfolding spills source hne
    (motive := fun _ perm trace _ result => ∀ p : PermuteKraken.Perm,
      p.toList = destList perm → Agrees (PermuteKraken.permute p) result (traceOps trace))
    ?blocked_top ?swap_top ?blocked_pos ?swap_pos ?done current perm trace hlen p hp
  case blocked_top =>
    intro current perm trace hlen top htop ht idx hdepth p hp
    have hs : PermuteKraken.step p.toList
        = .blocked ⟨(perm top).val, idx - MAX_SWAP_DEPTH⟩ := by
      rw [hp, step_top perm top htop ht]
      exact ite_eq_left_of_eq_true _ _ (eq_true hdepth)
    rw [Model.permute_blocked p hs]
    rfl
  case swap_top =>
    intro current perm trace hlen top htop ht idx hdepth _ _ _ _ _ _ ih p hp
    have hs : PermuteKraken.step p.toList = .swap idx (perm top).val := by
      rw [hp, step_top perm top htop ht]
      exact ite_eq_right_of_eq_false _ _ (eq_false hdepth)
    rw [Model.permute_swap p hs]
    apply agrees_map
    exact ih p.advance (by
      rw [Model.advance_toList p hs, hp, length_destList, swapEntries_destList perm top _ htop])
  case blocked_pos =>
    intro current perm trace hlen top htop ht _ pos hpos hsearch idx hdepth p hp
    have hs : PermuteKraken.step p.toList = .blocked ⟨pos.val, idx - MAX_SWAP_DEPTH⟩ := by
      rw [hp, step_pos perm top htop (not_not.mp ht) pos hpos hsearch]
      exact ite_eq_left_of_eq_true _ _ (eq_true hdepth)
    rw [Model.permute_blocked p hs]
    rfl
  case swap_pos =>
    intro current perm trace hlen top htop ht _ pos hpos hsearch idx hdepth _ _ _ _ _ _ _ _ ih p hp
    have hs : PermuteKraken.step p.toList = .swap idx pos.val := by
      rw [hp, step_pos perm top htop (not_not.mp ht) pos hpos hsearch]
      exact ite_eq_right_of_eq_false _ _ (eq_false hdepth)
    rw [Model.permute_swap p hs]
    apply agrees_map
    exact ih p.advance (by
      rw [Model.advance_toList p hs, hp, length_destList, swapEntries_destList perm top _ htop])
  case done =>
    intro current perm trace hlen top htop ht _ hsearch p hp
    rw [Model.permute_done p (by rw [hp]; exact step_none perm top htop (not_not.mp ht) hsearch)]
    exact ⟨_, _, rfl, by simp⟩

theorem permute_agrees (spills : SpillSet) (source : Stack)
    (perm : Shuffler.Permute.Permutation source)
    (p : PermuteKraken.Perm) (hp : p.toList = destList perm) :
    Agrees (PermuteKraken.permute p) (Shuffler.Permute.permute spills source perm) [] := by
  rw [Shuffler.Permute.permute]
  split
  · exact go_agrees spills source _ source perm (.Lit source) rfl p hp
  · rename_i hne
    have hs : PermuteKraken.step p.toList = .done := by
      simp [PermuteKraken.step, hp, length_destList, Nat.eq_zero_of_not_pos hne]
    rw [Model.permute_done p hs]
    exact ⟨_, _, rfl, rfl⟩

/-! ## The bridge -/

-- A swap result of the model: the original gives the same swaps, and the source
-- stack permuted by `perm`.
theorem permute_ok_of_model (spills : SpillSet) (source : Stack)
    (perm : Shuffler.Permute.Permutation source)
    (p : PermuteKraken.Perm) (hp : p.toList = destList perm) {swaps : List Nat}
    (h : PermuteKraken.permute p = .ok swaps) :
    ∃ res trace, Shuffler.Permute.permute spills source perm = .ok ⟨res, trace⟩
      ∧ traceOps trace = swaps.map .swap
      ∧ res = Shuffler.Permute.apply_permutation source perm := by
  have ha := permute_agrees spills source perm p hp
  rw [h] at ha
  obtain ⟨res, trace, ho, hops⟩ := ha
  exact ⟨res, trace, ho, by simpa using hops,
    Shuffler.Permute.permute_applies_permutation_of_ok spills source perm ho⟩

-- A blocked result of the model: the original is blocked at the same offset by
-- the same excess.
theorem permute_blocked_of_model (spills : SpillSet) (source : Stack)
    (perm : Shuffler.Permute.Permutation source)
    (p : PermuteKraken.Perm) (hp : p.toList = destList perm) {b : PermuteKraken.Blocked}
    (h : PermuteKraken.permute p = .error b) :
    Shuffler.Permute.permute spills source perm = .error (.Blocked ⟨b.offset, b.excess⟩) := by
  have ha := permute_agrees spills source perm p hp
  rw [h] at ha
  exact ha

end BbuBridge
