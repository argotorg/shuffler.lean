module

public import Lift.P2.Total.System

@[expose] public section

namespace Lift.P2.Total

namespace System

inductive Steps {S O : Type} (m : System S O) : Nat → S → S → Prop
  | zero (s : S) : Steps m 0 s s
  | succ {n : Nat} {s t u : S} (edge : m.step s t) (rest : Steps m n t u) :
      Steps m (n + 1) s u

theorem Reaches.trans {S O : Type} {m : System S O} {s t u : S}
    (first : m.Reaches s t) (second : m.Reaches t u) : m.Reaches s u := by
  induction second with
  | refl => exact first
  | tail _ edge ih => exact .tail ih edge

theorem Steps.reaches {S O : Type} {m : System S O} {n : Nat} {s t : S}
    (path : m.Steps n s t) : m.Reaches s t := by
  induction path with
  | zero => exact .refl _
  | succ edge _ ih => exact (Reaches.tail (Reaches.refl _) edge).trans ih

theorem Steps.pos_head {S O : Type} {m : System S O} {n : Nat} {s t : S}
    (path : Steps m n s t) (hn : 0 < n) :
    ∃ u, m.step s u ∧ Steps m (n - 1) u t := by
  cases path with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ edge rest => exact ⟨_, edge, by simpa using rest⟩

theorem Reaches.head {S O : Type} {m : System S O} {s t : S}
    (path : m.Reaches s t) : s = t ∨ ∃ u, m.step s u ∧ m.Reaches u t := by
  induction path with
  | refl => exact Or.inl rfl
  | tail _ edge ih =>
    rcases ih with heq | ⟨v, hstep, hreach⟩
    · refine Or.inr ⟨_, ?_, .refl _⟩
      rw [heq]
      exact edge
    · exact Or.inr ⟨v, hstep, .tail hreach edge⟩

end System

/-- A source step can be omitted only when its natural-number rank decreases.
Matching terminal outcomes can also take a finite number of target steps. -/
structure RankedSimulation {A B O : Type} (x : System A O) (y : System B O)
    (r : A → B → Prop) (rank : A → B → Nat) : Prop where
  stop : ∀ {a b out}, r a b → x.stop a out → ∃ b', y.Reaches b b' ∧ y.stop b' out
  step : ∀ {a a' b}, r a b → x.step a a' →
    ∃ n b', y.Steps n b b' ∧ r a' b' ∧ (0 < n ∨ rank a' b' < rank a b)

theorem RankedSimulation.reaches {A B O : Type} {x : System A O} {y : System B O}
    {r : A → B → Prop} {rank : A → B → Nat} (sim : RankedSimulation x y r rank)
    {a a' : A} {b : B} (hr : r a b) (path : x.Reaches a a') :
    ∃ b', y.Reaches b b' ∧ r a' b' := by
  induction path with
  | refl => exact ⟨b, .refl b, hr⟩
  | tail _ edge ih =>
    obtain ⟨t, ht, hrt⟩ := ih
    obtain ⟨_, u, hu, hru, _⟩ := sim.step hrt edge
    exact ⟨u, ht.trans hu.reaches, hru⟩

/-- From a related source-trace position and target state, some finite
positive-length target path reaches a state related to another source-trace
position. The rank strictly decreases only along omitted (zero-length) source
steps, so well-founded induction on the rank terminates. -/
theorem RankedSimulation.exists_positive_path
    {A B O : Type} {x : System A O} {y : System B O}
    {r : A → B → Prop} {rank : A → B → Nat} (sim : RankedSimulation x y r rank)
    (trace : Nat → A) (htrace : ∀ n, x.step (trace n) (trace (n + 1)))
    (i : Nat) (b : B) (hr : r (trace i) b) :
    ∃ n c, 0 < n ∧ y.Steps n b c ∧ ∃ j, i ≤ j ∧ r (trace j) c := by
  classical
  let Q : Nat → Prop := fun N =>
    ∀ (i : Nat) (b : B), rank (trace i) b = N → r (trace i) b →
      ∃ n c, 0 < n ∧ y.Steps n b c ∧ ∃ j, i ≤ j ∧ r (trace j) c
  have hQ : ∀ N, Q N := by
    intro N
    refine WellFounded.induction Nat.lt_wfRel.wf N (fun n ih => ?_)
    intro i b hrank hr
    obtain ⟨m, b', hpath, hrb', hdisj⟩ := sim.step hr (htrace i)
    cases m with
    | zero =>
      cases hpath with
      | zero =>
        have hlt : rank (trace (i + 1)) b < rank (trace i) b := by
          rcases hdisj with h | h
          · exact absurd h (Nat.lt_irrefl 0)
          · exact h
        have hltN : rank (trace (i + 1)) b < n := by
          rw [← hrank]
          exact hlt
        obtain ⟨k, c, hk, hpath2, j, hj, hrc⟩ :=
          ih (rank (trace (i + 1)) b) hltN (i + 1) b rfl hrb'
        exact ⟨k, c, hk, hpath2, j, Nat.le_trans (Nat.le_succ i) hj, hrc⟩
    | succ k =>
      exact ⟨k + 1, b', Nat.succ_pos k, hpath, i + 1, Nat.le_succ i, hrb'⟩
  exact hQ (rank (trace i) b) i b rfl hr

/-- Preserve a real infinite trace even when the match uses finite stuttering.

Proof plan for the residual obligation: from a related source-trace index and
target state, use well-founded induction on rank to find a target path of
positive length. A zero-length match advances the source index and decreases
rank. Then use the invariant "a finite target path leads to a state related to
some source-trace index" to construct an infinite target trace. This avoids
assuming finite branching, fairness, determinism, or source termination.
-/
theorem RankedSimulation.diverges {A B O : Type} {x : System A O} {y : System B O}
    {r : A → B → Prop} {rank : A → B → Nat} (sim : RankedSimulation x y r rank)
    {a : A} {b : B} (hr : r a b) (div : x.Diverges a) : y.Diverges b := by
  classical
  obtain ⟨trace, hstart, hnext⟩ := div
  have hinit : r (trace 0) b := hstart ▸ hr
  let P : B → Prop := fun b => ∃ i c, y.Reaches b c ∧ r (trace i) c
  have hPstep : ∀ b, P b → ∃ b', y.step b b' ∧ P b' := by
    intro b hb
    obtain ⟨i, c, hreach, hrc⟩ := hb
    obtain ⟨n, c', hn, hpath, j, hij, hrc'⟩ :=
      RankedSimulation.exists_positive_path sim trace hnext i c hrc
    rcases System.Reaches.head hreach with heq | ⟨u, hstep, hreach'⟩
    · cases heq
      obtain ⟨b1, edge, rest⟩ := System.Steps.pos_head hpath hn
      exact ⟨b1, edge, ⟨j, c', rest.reaches, hrc'⟩⟩
    · exact ⟨u, hstep, ⟨i, c, hreach', hrc⟩⟩
  let matched : (n : Nat) → { t : B // P t } :=
    Nat.rec ⟨b, ⟨0, b, .refl b, hinit⟩⟩
      (fun _ prev =>
        ⟨Classical.choose (hPstep prev.val prev.property),
         (Classical.choose_spec (hPstep prev.val prev.property)).2⟩)
  refine ⟨fun n => (matched n).val, rfl, fun n => ?_⟩
  exact (Classical.choose_spec (hPstep (matched n).val (matched n).property)).1

theorem RankedSimulation.behaves {A B O : Type} {x : System A O} {y : System B O}
    {r : A → B → Prop} {rank : A → B → Nat} (sim : RankedSimulation x y r rank)
    {a : A} {b : B} (hr : r a b) (behavior : Behavior O) :
    x.Behaves a behavior → y.Behaves b behavior := by
  cases behavior with
  | finish out =>
    rintro ⟨t, path, stop⟩
    obtain ⟨u, target, related⟩ := sim.reaches hr path
    obtain ⟨v, rest, terminal⟩ := sim.stop related stop
    exact ⟨v, target.trans rest, terminal⟩
  | diverge => exact sim.diverges hr

end Lift.P2.Total
