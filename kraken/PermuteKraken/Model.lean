module

@[expose] public section

/-
A model of `Shuffler.Permute.permute` without Mathlib. A permutation is a list:
`toList[i]` is the destination of the slot at position `i`, and position
`length - 1` is the top of the stack. `permute` returns the depth of each swap in
the order of application, or the first swap that is out of reach. The result
stack is not part of the model: the swaps determine it.
-/

namespace PermuteKraken

def MAX_SWAP_DEPTH : Nat := 16

-- The slot at `offset` is out of reach by `excess` slots.
structure Blocked where
  offset : Nat
  excess : Nat
  deriving DecidableEq, Repr

structure Perm where
  toList : List Nat
  lt : ∀ i (h : i < toList.length), toList[i] < toList.length
  inj : ∀ i j (hi : i < toList.length) (hj : j < toList.length), toList[i] = toList[j] → i = j

-- The last out-of-place position, as the `foldl` in `permute.go`.
def lastMisplaced (l : List Nat) (k : Nat) : Option Nat :=
  (List.range k).foldl (fun acc i => if l[i]! ≠ i then some i else acc) none

inductive Step where
  | done
  | blocked (b : Blocked)
  | swap (idx pos : Nat)
  deriving DecidableEq, Repr

-- The position to swap with the top: the destination of the top if the top is
-- out of place, else the last out-of-place position.
def target (l : List Nat) : Option Nat :=
  let top := l.length - 1
  if l[top]! ≠ top then some l[top]! else lastMisplaced l l.length

-- One iteration of `permute.go`.
def step (l : List Nat) : Step :=
  if l.length = 0 then .done else
  match target l with
  | none => .done
  | some pos =>
    let idx := l.length - 1 - pos
    if idx > MAX_SWAP_DEPTH then .blocked ⟨pos, idx - MAX_SWAP_DEPTH⟩ else .swap idx pos

-- `perm * Equiv.swap top pos`
def swapEntries (l : List Nat) (i j : Nat) : List Nat :=
  (l.set i l[j]!).set j l[i]!

-- The out-of-place positions below the top, then 1 if the top is in place.
-- This is `Permutation.measure` as one number.
def measure (l : List Nat) : Nat :=
  2 * (List.range (l.length - 1)).countP (fun i => l[i]! ≠ i)
    + if l[l.length - 1]! = l.length - 1 then 1 else 0

/-! ## Lemmas for termination -/

theorem lastMisplaced_spec (l : List Nat) (k : Nat) :
    ∀ pos, lastMisplaced l k = some pos → pos < k ∧ l[pos]! ≠ pos := by
  unfold lastMisplaced
  induction k with
  | zero => simp
  | succ k ih =>
    intro pos h
    rw [List.range_succ, List.foldl_append] at h
    simp only [List.foldl_cons, List.foldl_nil] at h
    split at h
    · grind
    · have := ih pos h; omega

theorem lastMisplaced_none (l : List Nat) (k : Nat) (h : lastMisplaced l k = none) :
    ∀ i < k, l[i]! = i := by
  unfold lastMisplaced at h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append] at h
    simp only [List.foldl_cons, List.foldl_nil] at h
    split at h
    · simp at h
    · intro i hi
      by_cases hik : i = k
      · grind
      · exact ih h i (by omega)


theorem step_swap {l : List Nat} {idx pos : Nat} (h : step l = .swap idx pos) :
    idx = l.length - 1 - pos ∧ idx ≤ MAX_SWAP_DEPTH
      ∧ ((l[l.length - 1]! ≠ l.length - 1 ∧ pos = l[l.length - 1]!)
        ∨ (l[l.length - 1]! = l.length - 1 ∧ pos < l.length ∧ l[pos]! ≠ pos)) := by
  unfold step at h
  split at h
  · simp at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i pos' hpos
    split at h
    · simp at h
    · simp only [Step.swap.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [target] at hpos
      split at hpos
      · grind
      · have := lastMisplaced_spec l l.length _ hpos
        grind

theorem step_done {l : List Nat} (h : step l = .done) : ∀ i < l.length, l[i]! = i := by
  unfold step at h
  split at h
  · intro i hi; omega
  dsimp only at h
  split at h
  · rename_i hpos
    simp only [target] at hpos
    split at hpos
    · simp at hpos
    · exact lastMisplaced_none l l.length hpos
  · split at h <;> simp at h

-- `target` gives the destination of an out-of-place top, or an out-of-place
-- position if the top is in place.
theorem target_spec {l : List Nat} {pos : Nat} (h : target l = some pos) :
    (l[l.length - 1]! ≠ l.length - 1 ∧ pos = l[l.length - 1]!)
      ∨ (l[l.length - 1]! = l.length - 1 ∧ pos < l.length ∧ l[pos]! ≠ pos) := by
  simp only [target] at h
  split at h
  · grind
  · have := lastMisplaced_spec l l.length _ h
    grind

theorem step_target {l : List Nat} {idx pos : Nat} (h : step l = .swap idx pos) :
    target l = some pos := by
  unfold step at h
  split at h
  · simp at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i pos' hpos
    split at h
    · simp at h
    · simp only [Step.swap.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hpos

namespace Perm

theorem getElem!_lt (p : Perm) {i : Nat} (hi : i < p.toList.length) :
    p.toList[i]! < p.toList.length := by
  rw [getElem!_pos p.toList i hi]
  exact p.lt i hi

theorem getElem!_inj (p : Perm) {i j : Nat} (hi : i < p.toList.length) (hj : j < p.toList.length)
    (h : p.toList[i]! = p.toList[j]!) : i = j := by
  rw [getElem!_pos p.toList i hi, getElem!_pos p.toList j hj] at h
  exact p.inj i j hi hj h

-- In a permutation, the destination of an out-of-place top is out of place too:
-- `target` gives an out-of-place position below the top.
theorem target_lt (p : Perm) {pos : Nat} (h : target p.toList = some pos) :
    pos < p.toList.length - 1 ∧ p.toList[pos]! ≠ pos := by
  rcases target_spec h with ⟨htop, rfl⟩ | ⟨htop, hlt, hmis⟩
  · have hne : 0 < p.toList.length := by
      cases hl : p.toList with
      | nil => simp [hl] at htop
      | cons _ _ => simp
    have hlt := p.getElem!_lt (i := p.toList.length - 1) (by omega)
    refine ⟨by omega, fun hfix => htop ?_⟩
    have := p.getElem!_inj (by omega) (by omega : p.toList.length - 1 < p.toList.length) hfix
    omega
  · have hpos : pos ≠ p.toList.length - 1 := fun h => hmis (h ▸ htop)
    exact ⟨by omega, hmis⟩

theorem step_swap (p : Perm) {idx pos : Nat} (h : step p.toList = .swap idx pos) :
    idx = p.toList.length - 1 - pos ∧ 1 ≤ idx ∧ idx ≤ MAX_SWAP_DEPTH
      ∧ pos < p.toList.length - 1 ∧ p.toList[pos]! ≠ pos := by
  obtain ⟨hidx, hmax, -⟩ := PermuteKraken.step_swap h
  obtain ⟨hlt, hmis⟩ := p.target_lt (step_target h)
  exact ⟨hidx, by omega, hmax, hlt, hmis⟩

def swap (p : Perm) (i j : Nat) (hi : i < p.toList.length) (hj : j < p.toList.length) : Perm where
  toList := swapEntries p.toList i j
  lt := by
    intro k hk
    simp only [swapEntries, List.length_set] at hk ⊢
    have := p.lt i hi
    have := p.lt j hj
    have := p.lt k hk
    grind
  inj := by
    intro a b ha hb h
    simp only [swapEntries, List.length_set] at ha hb
    simp only [swapEntries, List.getElem_set, getElem!_pos p.toList i hi,
      getElem!_pos p.toList j hj] at h
    have := p.inj a b ha hb
    have := p.inj a i ha hi
    have := p.inj a j ha hj
    have := p.inj b i hb hi
    have := p.inj b j hb hj
    have := p.inj i j hi hj
    grind

theorem length_swap (p : Perm) (i j : Nat) (hi hj) :
    (p.swap i j hi hj).toList.length = p.toList.length := by
  simp [swap, swapEntries]

theorem getElem!_swap (p : Perm) (i j : Nat) (hi hj) (k : Nat) :
    (p.swap i j hi hj).toList[k]! =
      if k = j then p.toList[i]! else if k = i then p.toList[j]! else p.toList[k]! := by
  simp only [swap, swapEntries]
  grind

theorem countP_lt {n : Nat} {f g : Nat → Bool} (hle : ∀ i < n, f i → g i)
    (hlt : ∃ j < n, ¬ f j ∧ g j) :
    (List.range n).countP f < (List.range n).countP g := by
  induction n with
  | zero => obtain ⟨j, hj, -⟩ := hlt; omega
  | succ n ih =>
    simp only [List.range_succ, List.countP_append, List.countP_singleton]
    have hle' : ∀ i < n, f i → g i := fun i hi => hle i (by omega)
    have hmono : (List.range n).countP f ≤ (List.range n).countP g :=
      List.countP_mono_left (fun i hi hf => hle' i (List.mem_range.mp hi) hf)
    obtain ⟨j, hj, hfj, hgj⟩ := hlt
    by_cases hjn : j = n
    · subst hjn
      have := hle j (by omega)
      grind
    · have := ih hle' ⟨j, by omega, hfj, hgj⟩
      have := hle n (by omega)
      grind

theorem countP_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    (List.range n).countP f = (List.range n).countP g :=
  List.countP_congr (fun i hi => by rw [h i (List.mem_range.mp hi)])

theorem measure_target_lt (p : Perm) {pos : Nat} (h : target p.toList = some pos) (hi hj) :
    measure (p.swap (p.toList.length - 1) pos hi hj).toList < measure p.toList := by
  obtain ⟨hpos, hmis⟩ := p.target_lt h
  have hgs := p.getElem!_swap (p.toList.length - 1) pos hi hj
  unfold measure
  rw [p.length_swap]
  generalize htop : p.toList.length - 1 = top at *
  by_cases ht : p.toList[top]! = top
  · -- the top is in place: the swap keeps the count below the top and moves the top out
    have hne : p.toList[pos]! ≠ top := fun he =>
      hmis (by have := p.getElem!_inj (by omega) (by omega) (he.trans ht.symm); omega)
    have hc := countP_congr (n := top)
      (f := fun i => (p.swap top pos hi hj).toList[i]! ≠ i) (g := fun i => p.toList[i]! ≠ i)
      (fun i hi' => by rw [hgs i]; grind)
    simp only [hgs, ht]
    grind
  · -- the top is out of place: `pos` is its destination, and the swap puts `pos` in place
    rcases target_spec h with h1 | h2
    · obtain ⟨-, hp⟩ := h1
      rw [htop] at hp
      have hlt := countP_lt (n := top)
        (f := fun i => (p.swap top pos hi hj).toList[i]! ≠ i) (g := fun i => p.toList[i]! ≠ i)
        (fun i hi' => by rw [hgs i]; grind) ⟨pos, hpos, by rw [hgs pos]; grind, by simpa using hmis⟩
      grind
    · grind

theorem measure_swap_lt (p : Perm) {idx pos : Nat} (h : step p.toList = .swap idx pos) (hi hj) :
    measure (p.swap (p.toList.length - 1) pos hi hj).toList < measure p.toList :=
  p.measure_target_lt (step_target h) hi hj

-- The permutation after one swap, or `p` if `step` gives no swap.
def advance (p : Perm) : Perm :=
  match h : step p.toList with
  | .swap _ pos =>
    have hs := p.step_swap h
    p.swap (p.toList.length - 1) pos (by omega) (by omega)
  | _ => p

theorem measure_advance (p : Perm) {idx pos : Nat} (h : step p.toList = .swap idx pos) :
    measure p.advance.toList < measure p.toList := by
  unfold advance
  split
  · rename_i h'
    rw [h] at h'
    cases h'
    exact p.measure_swap_lt h _ _
  · rename_i hn
    exact absurd h (hn _ _)

end Perm

-- `permute.go`
def permute (p : Perm) : Except Blocked (List Nat) :=
  match _h : step p.toList with
  | .done => .ok []
  | .blocked b => .error b
  | .swap idx _ => (permute p.advance).map (idx :: ·)
termination_by measure p.toList
decreasing_by exact p.measure_advance _h

-- The number of swaps before `permute` stops.
def steps (p : Perm) : Nat :=
  match h : step p.toList with
  | .swap _ _ => steps p.advance + 1
  | _ => 0
termination_by measure p.toList
decreasing_by exact p.measure_advance h

end PermuteKraken
