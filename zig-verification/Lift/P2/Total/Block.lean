module

public import Lift.P2.Total.Segment
public import Lift.P2.Total.Unroll

@[expose] public section

namespace Lift.P2.Total

/-- A local block ends at the next cut, or at an actual terminal outcome. -/
inductive BlockExit (S O : Type) where
  | next (state : S)
  | finished (outcome : O)

/-- This system is only proof machinery. Crossing a cut is a local outcome;
the original system still executes that transition. -/
def blockSystem {S O : Type} (m : System S O) (cut : S → Prop) :
    System S (BlockExit S O) where
  step s t := m.step s t ∧ ¬ cut t
  stop s out := match out with
    | .next t => m.step s t ∧ cut t
    | .finished out => m.stop s out

def BlockClosed {S O : Type} (m : System S O) (cut : S → Prop)
    (depth : Nat) (s : S) : Prop :=
  ∀ t, ¬ unroll (blockSystem m cut) depth s (.pending t)

theorem BlockClosed.step {S O : Type} {m : System S O} {cut : S → Prop}
    {depth : Nat} {s t : S} (closed : BlockClosed m cut (depth + 1) s)
    (edge : m.step s t) (interior : ¬ cut t) : BlockClosed m cut depth t := by
  intro u h
  exact closed u (Or.inr ⟨t, ⟨edge, interior⟩, h⟩)

theorem BlockClosed.exists_step {S O : Type} {m : System S O} {cut : S → Prop}
    {s t : S} (closed : ∃ depth, BlockClosed m cut depth s)
    (edge : m.step s t) (interior : ¬ cut t) :
    ∃ depth, BlockClosed m cut depth t := by
  obtain ⟨depth, closed⟩ := closed
  cases depth with
  | zero => exact (closed s rfl).elim
  | succ depth => exact ⟨depth, closed.step edge interior⟩

theorem InteriorPath.blockClosed {S O : Type} {m : System S O} {cut : S → Prop}
    {s t : S} (path : InteriorPath m cut s t)
    (closed : ∃ depth, BlockClosed m cut depth s) :
    ∃ depth, BlockClosed m cut depth t := by
  induction path with
  | refl => exact closed
  | tail _ edge interior ih => exact BlockClosed.exists_step ih edge interior

theorem InteriorPath.blockReaches {S O : Type} {m : System S O} {cut : S → Prop}
    {s t : S} (path : InteriorPath m cut s t) : (blockSystem m cut).Reaches s t := by
  induction path with
  | refl => exact .refl _
  | tail _ edge interior ih => exact .tail ih ⟨edge, interior⟩

theorem blockReaches_interiorPath {S O : Type} {m : System S O} {cut : S → Prop}
    {s t : S} (path : (blockSystem m cut).Reaches s t) : InteriorPath m cut s t := by
  induction path with
  | refl => exact .refl _
  | tail _ edge ih => exact .tail ih edge.1 edge.2

theorem block_next_iff {S O : Type} (m : System S O) (cut : S → Prop) (s t : S) :
    (blockSystem m cut).Behaves s (.finish (.next t)) ↔
      cut t ∧ ∃ u, InteriorPath m cut s u ∧ m.step u t := by
  constructor
  · rintro ⟨u, path, edge, target⟩
    exact ⟨target, u, blockReaches_interiorPath path, edge⟩
  · rintro ⟨target, u, path, edge⟩
    exact ⟨u, path.blockReaches, edge, target⟩

theorem block_finished_iff {S O : Type} (m : System S O) (cut : S → Prop)
    (s : S) (out : O) :
    (blockSystem m cut).Behaves s (.finish (.finished out)) ↔
      ∃ u, InteriorPath m cut s u ∧ m.stop u out := by
  constructor
  · rintro ⟨u, path, terminal⟩
    exact ⟨u, blockReaches_interiorPath path, terminal⟩
  · rintro ⟨u, path, terminal⟩
    exact ⟨u, path.blockReaches, terminal⟩

namespace Block

theorem exists_least (P : Nat → Prop) (has : ∃ n, P n) :
    ∃ n, P n ∧ ∀ k, k < n → ¬ P k := by
  classical
  obtain ⟨n, hn⟩ := has
  let Q : Nat → Prop := fun n => P n → ∃ n, P n ∧ ∀ k, k < n → ¬ P k
  have aux : ∀ n, Q n := by
    intro n
    refine WellFounded.induction Nat.lt_wfRel.wf n (fun n ih => ?_)
    intro hn
    by_cases smaller : ∃ k, k < n ∧ P k
    · obtain ⟨k, hk, hp⟩ := smaller
      exact ih k hk hp
    · exact ⟨n, hn, fun k hk hp => smaller ⟨k, hk, hp⟩⟩
  exact aux n hn

noncomputable def least (P : Nat → Prop) (has : ∃ n, P n) : Nat :=
  Classical.choose (exists_least P has)

theorem least_spec (P : Nat → Prop) (has : ∃ n, P n) : P (least P has) :=
  (Classical.choose_spec (exists_least P has)).1

theorem least_le (P : Nat → Prop) (has : ∃ n, P n) {n : Nat} (hn : P n) :
    least P has ≤ n := by
  have minimal := (Classical.choose_spec (exists_least P has)).2
  exact Nat.le_of_not_gt (fun h => minimal n h hn)

noncomputable def remaining {S O : Type} (m : System S O) (cut : S → Prop)
    (s : S) : Nat :=
  by
    classical
    exact if has : ∃ n, BlockClosed m cut n s then
      least (fun n => BlockClosed m cut n s) has else 0

theorem remaining_spec {S O : Type} (m : System S O) (cut : S → Prop) (s : S)
    (has : ∃ n, BlockClosed m cut n s) : BlockClosed m cut (remaining m cut s) s := by
  classical
  simp only [remaining, dite_eq_left has]
  exact least_spec _ has

theorem remaining_le {S O : Type} (m : System S O) (cut : S → Prop) (s : S)
    {n : Nat} (closed : BlockClosed m cut n s) : remaining m cut s ≤ n := by
  classical
  have has : ∃ n, BlockClosed m cut n s := ⟨n, closed⟩
  simp only [remaining, dite_eq_left has]
  exact least_le _ has closed

theorem remaining_decreases {S O : Type} {m : System S O} {cut : S → Prop}
    {s t : S} (has : ∃ n, BlockClosed m cut n s)
    (edge : m.step s t) (interior : ¬ cut t) : remaining m cut t < remaining m cut s := by
  have closed := remaining_spec m cut s has
  cases rank : remaining m cut s with
  | zero => exact (closed s (by simp only [rank, unroll])).elim
  | succ n =>
    rw [rank] at closed
    exact Nat.lt_succ_of_le (remaining_le m cut t (closed.step edge interior))

end Block

/-- The generator supplies closed local expansions and matching next cuts in
both directions. The relation is checked only at cuts; register schedules may
differ inside each block. -/
structure BlockMatch {A B O : Type} (x : System A O) (y : System B O)
    (cutX : A → Prop) (cutY : B → Prop) (relation : A → B → Prop) : Prop where
  cuts : ∀ {a b}, relation a b → cutX a ∧ cutY b
  leftClosed : ∀ {a b}, relation a b → ∃ n, BlockClosed x cutX n a
  rightClosed : ∀ {a b}, relation a b → ∃ n, BlockClosed y cutY n b
  forward : ∀ {a b a'}, relation a b →
    (blockSystem x cutX).Behaves a (.finish (.next a')) →
    ∃ b', (blockSystem y cutY).Behaves b (.finish (.next b')) ∧ relation a' b'
  backward : ∀ {a b b'}, relation a b →
    (blockSystem y cutY).Behaves b (.finish (.next b')) →
    ∃ a', (blockSystem x cutX).Behaves a (.finish (.next a')) ∧ relation a' b'
  terminal : ∀ {a b out}, relation a b →
    ((blockSystem x cutX).Behaves a (.finish (.finished out)) ↔
      (blockSystem y cutY).Behaves b (.finish (.finished out)))

def BlockMatch.leftRelation {A B O : Type} {x : System A O} {y : System B O}
    {cutX : A → Prop} {cutY : B → Prop} {relation : A → B → Prop}
    (_match : BlockMatch x y cutX cutY relation) (a : A) (b : B) : Prop :=
  ∃ root, relation root b ∧ InteriorPath x cutX root a

theorem BlockMatch.forward_simulation {A B O : Type} {x : System A O} {y : System B O}
    {cutX : A → Prop} {cutY : B → Prop} {relation : A → B → Prop}
    (certificate : BlockMatch x y cutX cutY relation) :
    RankedSimulation x y certificate.leftRelation (fun a _ => Block.remaining x cutX a) := by
  refine ⟨?_, ?_⟩
  · intro a b out related terminal
    obtain ⟨root, relation, path⟩ := related
    have summary := (block_finished_iff x cutX root out).mpr ⟨a, path, terminal⟩
    have target := (certificate.terminal relation).mp summary
    obtain ⟨last, targetPath, targetStop⟩ := (block_finished_iff y cutY b out).mp target
    obtain ⟨n, steps⟩ := targetPath.steps
    exact ⟨last, steps.reaches, targetStop⟩
  · intro a next b related edge
    obtain ⟨root, relation, path⟩ := related
    by_cases targetCut : cutX next
    · have summary := (block_next_iff x cutX root next).mpr ⟨targetCut, a, path, edge⟩
      obtain ⟨target, matched, relatedTarget⟩ := certificate.forward relation summary
      obtain ⟨_, last, targetPath, targetEdge⟩ := (block_next_iff y cutY b target).mp matched
      obtain ⟨n, steps⟩ := targetPath.steps
      exact ⟨n + 1, target, steps.tail targetEdge, ⟨next, relatedTarget, .refl _⟩,
        Or.inl (Nat.zero_lt_succ n)⟩
    · exact ⟨0, b, .zero _, ⟨root, relation, .tail path edge targetCut⟩,
        Or.inr (Block.remaining_decreases
          (path.blockClosed (certificate.leftClosed relation)) edge targetCut)⟩

theorem BlockMatch.swap {A B O : Type} {x : System A O} {y : System B O}
    {cutX : A → Prop} {cutY : B → Prop} {relation : A → B → Prop}
    (certificate : BlockMatch x y cutX cutY relation) :
    BlockMatch y x cutY cutX (fun b a => relation a b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b a related
    exact (certificate.cuts related).symm
  · intro b a related
    exact certificate.rightClosed related
  · intro b a related
    exact certificate.leftClosed related
  · intro b a next related path
    exact certificate.backward related path
  · intro b a next related path
    exact certificate.forward related path
  · intro b a out related
    exact (certificate.terminal related).symm

theorem BlockMatch.equivalent {A B O : Type} {x : System A O} {y : System B O}
    {cutX : A → Prop} {cutY : B → Prop} {relation : A → B → Prop}
    (certificate : BlockMatch x y cutX cutY relation) {a : A} {b : B} (entry : relation a b) :
    Equivalent x y a b := by
  intro behavior
  exact ⟨certificate.forward_simulation.behaves ⟨a, entry, .refl _⟩ behavior,
    certificate.swap.forward_simulation.behaves ⟨b, entry, .refl _⟩ behavior⟩

end Lift.P2.Total
