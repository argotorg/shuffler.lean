module

public import Lift.P2.Total.Simulation

@[expose] public section

namespace Lift.P2.Total

/-- A Lean value with no internal transitions. -/
def pureSystem {A O : Type} (value : A → O) : System A O :=
  ⟨fun _ _ => False, fun a out => out = value a⟩

/-- A proof that all executions in the invariant finish at this value.
The rank must decrease on every actual transition. Totality supplies a next
transition or an observed outcome at every invariant state. -/
structure ReturnCertificate {S O : Type} (m : System S O) (value : O) where
  invariant : S → Prop
  rank : S → Nat
  step : ∀ {s t}, invariant s → m.step s t → invariant t ∧ rank t < rank s
  stop : ∀ {s out}, invariant s → m.stop s out → out = value
  total : ∀ s, invariant s → (∃ t, m.step s t) ∨ ∃ out, m.stop s out

theorem ReturnCertificate.path {S O : Type} {m : System S O} {value : O}
    (certificate : ReturnCertificate m value) {s : S} (entry : certificate.invariant s) :
    ∃ t, m.Reaches s t ∧ m.stop t value := by
  have finish : ∀ n s, certificate.rank s = n → certificate.invariant s →
      ∃ t, m.Reaches s t ∧ m.stop t value := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro s rank entry
      rcases certificate.total s entry with ⟨t, edge⟩ | ⟨out, stop⟩
      · obtain ⟨related, decrease⟩ := certificate.step entry edge
        obtain ⟨u, path, terminal⟩ := ih (certificate.rank t) (rank ▸ decrease) t rfl related
        exact ⟨u, (System.Reaches.tail (.refl s) edge).trans path, terminal⟩
      · exact ⟨s, .refl s, (certificate.stop entry stop) ▸ stop⟩
  exact finish (certificate.rank s) s rfl entry

def ReturnCertificate.coupling {S A O : Type} {m : System S O} {value : O}
    (certificate : ReturnCertificate m value) (observe : A → O) (a : A)
    (result : observe a = value) : Coupling m (pureSystem observe) where
  relation s t := certificate.invariant s ∧ t = a
  forwardRank s _ := certificate.rank s
  backwardRank _ _ := 0
  forward := {
    stop := by
      intro s t out related terminal
      obtain ⟨entry, rfl⟩ := related
      exact ⟨t, .refl t, (certificate.stop entry terminal).trans result.symm⟩
    step := by
      intro s s' t related edge
      obtain ⟨next, decrease⟩ := certificate.step related.1 edge
      exact ⟨0, t, .zero t, ⟨next, related.2⟩, Or.inr decrease⟩ }
  backward := {
    stop := by
      intro t s out related terminal
      obtain ⟨entry, rfl⟩ := related
      obtain ⟨u, path, stop⟩ := certificate.path entry
      have equality : out = value := terminal.trans result
      exact ⟨u, path, equality.symm ▸ stop⟩
    step := by
      intro s s' t _ edge
      exact edge.elim }

end Lift.P2.Total
