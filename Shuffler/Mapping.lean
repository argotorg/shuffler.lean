import Mathlib.Data.PEquiv
import Mathlib.Logic.Equiv.Basic

namespace Shuffler

abbrev Mapping := ℕ ≃. ℕ

namespace Mapping

/-- `destinationOf`: the target offset the slot at `p` is bound for, `none` for a surplus slot. -/
abbrev destinationOf (f : Mapping) (p : ℕ) : Option ℕ := f p

/-- `positionOf`: the slot bound for `d`, `none` if `d` is generated. -/
abbrev positionOf (f : Mapping) (d : ℕ) : Option ℕ := f.symm d

/-- The constructor: every slot surplus, every offset generated. -/
def empty : Mapping := ⊥

/-- `bind`: the two `yulAssert`s become hypotheses. -/
def bind (f : Mapping) (p d : ℕ) (hp : f p = none) (hd : f.symm d = none) : Mapping where
  toFun := Function.update f p (some d)
  invFun := Function.update f.symm d (some p)
  inv a b := by
    simp only [Function.update_apply]
    split_ifs with ha hb hb
    · subst ha hb; simp
    · subst ha; simp [← PEquiv.eq_some_iff, hd, Ne.symm hb]
    · subst hb; simp [PEquiv.eq_some_iff, hp, Ne.symm ha]
    · exact PEquiv.mem_iff_mem f

/-- `swapDestinations`: swap the positions first, then look up. -/
def swapDestinations (f : Mapping) (a b : ℕ) : Mapping :=
  (Equiv.swap a b).toPEquiv.trans f

/-- `pop`: forget the destination of slot `n` and nothing else. -/
def pop (f : Mapping) (n : ℕ) : Mapping :=
  (PEquiv.ofSet {p | p ≠ n}).trans f

/-- `push`: slot `n` is the fresh top, bound for `d`. -/
def push (f : Mapping) (n d : ℕ) (hn : f n = none) (hd : f.symm d = none) : Mapping :=
  bind f n d hn hd

/-- `release`: the destination-indexed side. -/
abbrev release (f : Mapping) : ℕ → Option ℕ := f.symm

/-- A mapping kept for a stack of height `n` against a target of size `m`: bound slots exist, and
destinations are real target offsets. Nothing else about the stack is known here. -/
structure Bounded (f : Mapping) (n m : ℕ) : Prop where
  pos_lt : ∀ {p d}, f p = some d → p < n
  dest_lt : ∀ {p d}, f p = some d → d < m

/-! ## Lemmas -/

/-- The invariant the C++ comment states, "no destination ever occurs twice". -/
theorem destinationOf_injective (f : Mapping) {p q d : ℕ} (hp : f p = some d) (hq : f q = some d) :
    p = q :=
  f.inj hp hq

/-! ### `bind` -/

@[simp] theorem bind_apply (f : Mapping) {p d : ℕ} (hp hd) (q : ℕ) :
    f.bind p d hp hd q = if q = p then some d else f q := by
  change Function.update f p (some d) q = _
  rw [Function.update_apply]

@[simp] theorem bind_symm_apply (f : Mapping) {p d : ℕ} (hp hd) (e : ℕ) :
    (f.bind p d hp hd).symm e = if e = d then some p else f.symm e := by
  change Function.update f.symm d (some p) e = _
  rw [Function.update_apply]

/-! ### `swapDestinations` -/

@[simp] theorem swapDestinations_apply (f : Mapping) (a b p : ℕ) :
    f.swapDestinations a b p = f (Equiv.swap a b p) := by
  simp [swapDestinations, PEquiv.trans, Equiv.toPEquiv]

theorem swapDestinations_apply_left (f : Mapping) (a b : ℕ) : f.swapDestinations a b a = f b := by
  simp

theorem swapDestinations_apply_right (f : Mapping) (a b : ℕ) : f.swapDestinations a b b = f a := by
  simp

theorem swapDestinations_apply_of_ne (f : Mapping) {a b p : ℕ} (ha : p ≠ a) (hb : p ≠ b) :
    f.swapDestinations a b p = f p := by
  simp [Equiv.swap_apply_of_ne_of_ne ha hb]

@[simp] theorem swapDestinations_symm_apply (f : Mapping) (a b d : ℕ) :
    (f.swapDestinations a b).symm d = (f.symm d).map (Equiv.swap a b) := by
  rcases hd : f.symm d with _ | p
  · refine Option.eq_none_iff_forall_ne_some.2 fun q hq => ?_
    rw [PEquiv.eq_some_iff, swapDestinations_apply, ← PEquiv.eq_some_iff, hd] at hq
    cases hq
  · rw [Option.map_some, PEquiv.eq_some_iff, swapDestinations_apply, Equiv.swap_apply_self,
      ← PEquiv.eq_some_iff, hd]

@[simp] theorem swapDestinations_swapDestinations (f : Mapping) (a b : ℕ) :
    (f.swapDestinations a b).swapDestinations a b = f := by
  simp [swapDestinations, ← PEquiv.trans_assoc, ← Equiv.toPEquiv_trans]

theorem swapDestinations_self (f : Mapping) (a : ℕ) : f.swapDestinations a a = f := by
  simp [swapDestinations]

/-! ### `pop` -/

@[simp] theorem pop_apply (f : Mapping) (n p : ℕ) : f.pop n p = if p = n then none else f p := by
  simp only [pop, PEquiv.trans, PEquiv.ofSet, PEquiv.coe_mk_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp_all

@[simp] theorem pop_symm_apply (f : Mapping) (n d : ℕ) :
    (f.pop n).symm d = (f.symm d).filter (· ≠ n) := by
  rcases hd : f.symm d with _ | p
  · refine Option.eq_none_iff_forall_ne_some.2 fun p hp => ?_
    rw [PEquiv.eq_some_iff, pop_apply] at hp
    split_ifs at hp
    rw [← PEquiv.eq_some_iff, hd] at hp
    cases hp
  · simp only [Option.filter_some, decide_eq_true_eq]
    split_ifs with hpn
    · rw [PEquiv.eq_some_iff, pop_apply, ite_eq_right hpn, ← PEquiv.eq_some_iff, hd]
    · refine Option.eq_none_iff_forall_ne_some.2 fun q hq => ?_
      rw [PEquiv.eq_some_iff, pop_apply] at hq
      split_ifs at hq with hqn
      rw [← PEquiv.eq_some_iff, hd] at hq
      cases hq
      exact hpn hqn

theorem pop_apply_of_ne (f : Mapping) {n p : ℕ} (h : p ≠ n) : f.pop n p = f p := by simp [h]

theorem pop_symm_of_ne (f : Mapping) {n d p : ℕ} (h : f.symm d = some p) (hp : p ≠ n) :
    (f.pop n).symm d = some p := by simp [h, hp]

theorem pop_symm_top (f : Mapping) {n d : ℕ} (h : f.symm d = some n) : (f.pop n).symm d = none := by
  simp [h]

/-- Popping a surplus slot is the identity. -/
theorem pop_of_none (f : Mapping) {n : ℕ} (hn : f n = none) : f.pop n = f := by
  ext p d
  by_cases h : p = n <;> simp [h, hn]

/-- `pop` undoes `push`. -/
theorem pop_push (f : Mapping) {n d : ℕ} (hn hd) : (f.push n d hn hd).pop n = f := by
  ext p e
  by_cases h : p = n
  · subst h; simp [hn]
  · simp [push, h]

/-! ### `Bounded` -/

namespace Bounded
variable {f : Mapping} {n m : ℕ}

theorem empty : (empty : Mapping).Bounded n m where
  pos_lt h := by simp [Mapping.empty] at h
  dest_lt h := by simp [Mapping.empty] at h

/-- The C++ precondition on the position side of `push` is a consequence of the bound. -/
theorem top_none (h : f.Bounded n m) : f n = none := by
  rcases hf : f n with _ | d
  · rfl
  · exact absurd (h.pos_lt hf) (lt_irrefl _)

theorem mono (h : f.Bounded n m) {n' m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') : f.Bounded n' m' where
  pos_lt hp := lt_of_lt_of_le (h.pos_lt hp) hn
  dest_lt hp := lt_of_lt_of_le (h.dest_lt hp) hm

theorem bind (h : f.Bounded n m) {p d : ℕ} (hp hd) (hpn : p < n) (hdm : d < m) :
    (f.bind p d hp hd).Bounded n m where
  pos_lt {q e} hq := by
    rw [bind_apply] at hq
    split_ifs at hq with hqp
    · subst hqp; exact hpn
    · exact h.pos_lt hq
  dest_lt {q e} hq := by
    rw [bind_apply] at hq
    split_ifs at hq with hqp
    · cases hq; exact hdm
    · exact h.dest_lt hq

theorem push (h : f.Bounded n m) {d : ℕ} (hd : f.symm d = none) (hdm : d < m) :
    (f.push n d h.top_none hd).Bounded (n + 1) m :=
  (h.mono (Nat.le_succ n) le_rfl).bind _ _ (Nat.lt_succ_self n) hdm

theorem pop (h : f.Bounded (n + 1) m) : (f.pop n).Bounded n m where
  pos_lt {p d} hp := by
    rw [pop_apply] at hp
    split_ifs at hp with hpn
    have := h.pos_lt hp
    omega
  dest_lt {p d} hp := by
    rw [pop_apply] at hp
    split_ifs at hp
    exact h.dest_lt hp

theorem swapDestinations (h : f.Bounded n m) {a b : ℕ} (ha : a < n) (hb : b < n) :
    (f.swapDestinations a b).Bounded n m where
  pos_lt {p d} hp := by
    rw [swapDestinations_apply] at hp
    have := h.pos_lt hp
    by_cases hpa : p = a <;> by_cases hpb : p = b <;> simp_all [Equiv.swap_apply_def]
  dest_lt {p d} hp := by
    rw [swapDestinations_apply] at hp
    exact h.dest_lt hp

end Bounded

/-! ### The bounded view -/

/-- A bounded mapping, seen as the partial bijection between the two index sets. -/
def toPEquiv (f : Mapping) {n m : ℕ} (h : f.Bounded n m) : Fin n ≃. Fin m where
  toFun p := (f p).pmap (fun d h => ⟨d, h⟩) fun _ hd => h.dest_lt hd
  invFun d := (f.symm d).pmap (fun p h => ⟨p, h⟩) fun _ hp => h.pos_lt (PEquiv.eq_some_iff _ |>.1 hp)
  inv p d := by
    simp only [Option.pmap_eq_some_iff, Fin.ext_iff]
    constructor
    · rintro ⟨q, hq, hpq, rfl⟩
      exact ⟨d, h.dest_lt ((PEquiv.eq_some_iff _).1 hpq), (PEquiv.eq_some_iff _).1 hpq, rfl⟩
    · rintro ⟨e, he, hpe, rfl⟩
      exact ⟨p, h.pos_lt hpe, (PEquiv.eq_some_iff _).2 hpe, rfl⟩

@[simp] theorem toPEquiv_eq_some_iff (f : Mapping) {n m : ℕ} (h : f.Bounded n m) (p : Fin n) (d : Fin m) :
    f.toPEquiv h p = some d ↔ f p = some d := by
  simp only [toPEquiv, PEquiv.coe_mk_apply, Option.pmap_eq_some_iff, Fin.ext_iff]
  constructor
  · rintro ⟨e, _, he, rfl⟩; exact he
  · intro hp; exact ⟨d, h.dest_lt hp, hp, rfl⟩

@[simp] theorem toPEquiv_eq_none_iff (f : Mapping) {n m : ℕ} (h : f.Bounded n m) (p : Fin n) :
    f.toPEquiv h p = none ↔ f p = none := by
  simp [toPEquiv]

end Mapping
end Shuffler
