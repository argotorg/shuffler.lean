module

public import Lift.P2.Total.Ranked
public import Lift.P2.Total.Pure

@[expose] public section

namespace Lift.P2.Total

/-- A finite proof expansion can expose an unresolved state. This type is used
only to check certificates. It is not an outcome of the L2 model. -/
inductive Frontier (S O : Type) where
  | pending (state : S)
  | finished (outcome : O)

/-- Expand at most `depth` internal steps for a local proof. A certificate must
exclude every pending state before it can remove this expansion bound. -/
def unroll {S O : Type} (m : System S O) : Nat → S → Frontier S O → Prop
  | 0, s, result => result = .pending s
  | depth + 1, s, result =>
      (∃ out, m.stop s out ∧ result = .finished out) ∨
      ∃ t, m.step s t ∧ unroll m depth t result

theorem unroll_pending_iff {S O : Type} (m : System S O) (n : Nat) (s t : S) :
    unroll m n s (.pending t) ↔ m.Steps n s t := by
  induction n generalizing s t with
  | zero =>
    constructor
    · intro h
      have e : t = s := Frontier.pending.inj h
      subst t
      exact .zero _
    · intro h
      cases h
      rfl
  | succ n ih =>
    simp only [unroll]
    constructor
    · rintro (⟨out, _, impossible⟩ | ⟨u, edge, rest⟩)
      · cases impossible
      · exact .succ edge ((ih u t).mp rest)
    · intro path
      cases path with
      | succ edge rest => exact Or.inr ⟨_, edge, (ih _ _).mpr rest⟩

theorem unroll_finished_sound {S O : Type} (m : System S O) (n : Nat) (s : S) (out : O) :
    unroll m n s (.finished out) → m.Behaves s (.finish out) := by
  induction n generalizing s with
  | zero => intro h; cases h
  | succ n ih =>
    rintro (⟨value, stop, equality⟩ | ⟨t, edge, rest⟩)
    · cases equality
      exact ⟨s, .refl _, stop⟩
    · obtain ⟨u, path, stop⟩ := ih t rest
      exact ⟨u, (System.Reaches.tail (.refl _) edge).trans path, stop⟩

theorem unroll_finished_complete {S O : Type} (m : System S O) (n : Nat) (s : S)
    (closed : ∀ t, ¬ unroll m n s (.pending t)) (out : O) :
    m.Behaves s (.finish out) → unroll m n s (.finished out) := by
  induction n generalizing s with
  | zero => exact (closed s rfl).elim
  | succ n ih =>
    rintro ⟨t, path, stop⟩
    rcases path.head with equality | ⟨u, edge, rest⟩
    · subst t
      exact Or.inl ⟨out, stop, rfl⟩
    · have nextClosed : ∀ v, ¬ unroll m n u (.pending v) :=
        fun v h => closed v (Or.inr ⟨u, edge, h⟩)
      exact Or.inr ⟨u, edge, ih u nextClosed ⟨t, rest, stop⟩⟩

theorem unroll_no_divergence {S O : Type} (m : System S O) (n : Nat) (s : S)
    (closed : ∀ t, ¬ unroll m n s (.pending t)) : ¬ m.Diverges s := by
  rintro ⟨trace, start, edge⟩
  have finiteTrace : ∀ k i, m.Steps k (trace i) (trace (i + k)) := by
    intro k
    induction k with
    | zero => intro i; exact .zero _
    | succ k ih =>
      intro i
      have rest := ih (i + 1)
      have path := System.Steps.succ (edge i) rest
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using path
  have path : m.Steps n s (trace n) := by
    simpa only [Nat.zero_add, start] using finiteTrace n 0
  exact closed (trace n) ((unroll_pending_iff m n s (trace n)).mpr path)

/-- The states visited in a finite proof expansion, including its start. -/
def visits {S O : Type} (m : System S O) : Nat → S → S → Prop
  | 0, _, _ => False
  | depth + 1, s, t => s = t ∨ ∃ u, m.step s u ∧ visits m depth u t

theorem reaches_visits {S O : Type} (m : System S O) (n : Nat) (s : S)
    (closed : ∀ t, ¬ unroll m n s (.pending t)) {t : S}
    (path : m.Reaches s t) : visits m n s t := by
  induction n generalizing s with
  | zero => exact (closed s rfl).elim
  | succ n ih =>
    rcases path.head with equality | ⟨u, edge, rest⟩
    · exact Or.inl equality
    · exact Or.inr ⟨u, edge, ih u
        (fun v h => closed v (Or.inr ⟨u, edge, h⟩)) rest⟩

/-- Local expansion proves equivalence only after every pending case has been
excluded. The two sides can use different finite bounds. -/
theorem equivalent_of_unroll {A B O : Type} (x : System A O) (y : System B O)
    (n k : Nat) (a : A) (b : B)
    (leftClosed : ∀ t, ¬ unroll x n a (.pending t))
    (rightClosed : ∀ t, ¬ unroll y k b (.pending t))
    (summary : ∀ out, unroll x n a (.finished out) ↔ unroll y k b (.finished out)) :
    Equivalent x y a b := by
  intro behavior
  cases behavior with
  | finish out =>
    exact ⟨fun h => unroll_finished_sound y k b out
        ((summary out).mp (unroll_finished_complete x n a leftClosed out h)),
      fun h => unroll_finished_sound x n a out
        ((summary out).mpr (unroll_finished_complete y k b rightClosed out h))⟩
  | diverge =>
    exact ⟨fun h => (unroll_no_divergence x n a leftClosed h).elim,
      fun h => (unroll_no_divergence y k b rightClosed h).elim⟩

end Lift.P2.Total
