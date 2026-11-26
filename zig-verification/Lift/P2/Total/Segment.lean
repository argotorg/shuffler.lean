module

public import Lift.P2.Total.Ranked

@[expose] public section

namespace Lift.P2.Total

/-- A finite path whose destinations are between the selected cut points. -/
inductive InteriorPath {S O : Type} (m : System S O) (cut : S → Prop) : S → S → Prop
  | refl (s : S) : InteriorPath m cut s s
  | tail {s t u : S} (path : InteriorPath m cut s t) (edge : m.step t u)
      (interior : ¬ cut u) : InteriorPath m cut s u

def segments {S O : Type} (m : System S O) (cut : S → Prop) : System S O where
  step s t := cut s ∧ cut t ∧ ∃ u, InteriorPath m cut s u ∧ m.step u t
  stop s out := cut s ∧ ∃ u, InteriorPath m cut s u ∧ m.stop u out

theorem System.Steps.tail {S O : Type} {m : System S O} {n : Nat} {s t u : S}
    (path : m.Steps n s t) (edge : m.step t u) : m.Steps (n + 1) s u := by
  induction path with
  | zero => exact .succ edge (.zero _)
  | succ first rest ih => exact .succ first (ih edge)

theorem InteriorPath.steps {S O : Type} {m : System S O} {cut : S → Prop} {s t : S}
    (path : InteriorPath m cut s t) : ∃ n, m.Steps n s t := by
  induction path with
  | refl => exact ⟨0, .zero _⟩
  | tail _ edge _ ih =>
    obtain ⟨n, path⟩ := ih
    exact ⟨n + 1, path.tail edge⟩

theorem segments_forward {S O : Type} (m : System S O) (cut : S → Prop)
    (rank : S → Nat)
    (decreases : ∀ s t, m.step s t → ¬ cut t → rank t < rank s) :
    RankedSimulation m (segments m cut)
      (fun s root => cut root ∧ InteriorPath m cut root s) (fun s _ => rank s) := by
  classical
  refine ⟨?_, ?_⟩
  · intro s root out related stop
    exact ⟨root, .refl _, related.1, s, related.2, stop⟩
  · intro s t root related edge
    by_cases target : cut t
    · exact ⟨1, t, .succ ⟨related.1, target, s, related.2, edge⟩ (.zero _),
        ⟨target, .refl _⟩, Or.inl (Nat.zero_lt_succ 0)⟩
    · exact ⟨0, root, .zero _, ⟨related.1, .tail related.2 edge target⟩,
        Or.inr (decreases s t edge target)⟩

theorem segments_backward {S O : Type} (m : System S O) (cut : S → Prop) :
    RankedSimulation (segments m cut) m (fun s t => s = t) (fun _ _ => 0) := by
  refine ⟨?_, ?_⟩
  · intro s t out related stop
    subst t
    obtain ⟨_, u, path, terminal⟩ := stop
    obtain ⟨n, steps⟩ := path.steps
    exact ⟨u, steps.reaches, terminal⟩
  · intro s u t related edge
    subst t
    obtain ⟨_, _, mid, path, last⟩ := edge
    obtain ⟨n, steps⟩ := path.steps
    exact ⟨n + 1, u, steps.tail last, rfl, Or.inl (Nat.zero_lt_succ n)⟩

/-- Finite instruction paths can be compressed only with a proof that each
omitted step decreases a rank. Terminal outcomes inside a path are retained. -/
theorem segments_equivalent {S O : Type} (m : System S O) (cut : S → Prop)
    (rank : S → Nat)
    (decreases : ∀ s t, m.step s t → ¬ cut t → rank t < rank s)
    {s : S} (entry : cut s) : Equivalent m (segments m cut) s s := by
  intro behavior
  exact ⟨(segments_forward m cut rank decreases).behaves ⟨entry, .refl s⟩ behavior,
    (segments_backward m cut).behaves rfl behavior⟩

end Lift.P2.Total
