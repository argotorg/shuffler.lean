module

public import Lift.Sem.Blocks

@[expose] public section

/-! The loop rule in path form: the step of a loop is a `Visits` predicate, one pass of the loop
body, so that a proof of the step has no induction hypothesis. -/

namespace Lift.Sem

/-- The paths from `l`, `s` that end at a return (with `Q r`), at a jump to `head` (with
`P s'`), or at a label whose result `r` a lemma gives (`exit`, with `Q r`): the head of a later
loop, or the outer head for an inner loop (L2-LOOPS). -/
inductive Visits {L σ R : Type} (b : Leaf L σ R) (head : L) (P : σ → Prop) (Q : R → Prop) :
    L → σ → Prop
  | ret {l s r} : b.step l s = .ok (.ret r) → Q r → Visits b head P Q l s
  | back {l s s'} : b.step l s = .ok (.goto head s') → P s' → Visits b head P Q l s
  | goto {l l' s s'} : b.step l s = .ok (.goto l' s') → Visits b head P Q l' s' →
      Visits b head P Q l s
  | exit {l s r} : b.Returns noCall l s r → Q r → Visits b head P Q l s

/-- The paths of `Visits` return `o`, if each return gives `o` and each jump to `head` gives a
state that returns `o`. -/
theorem Visits.returns {L σ R : Type} {b : Leaf L σ R} {head : L} {P : σ → Prop} {Q : R → Prop}
    {o : R} (hP : ∀ y, P y → b.Returns noCall head y o) (hQ : ∀ r, Q r → r = o) {l : L} {s : σ}
    (h : Visits b head P Q l s) : b.Returns noCall l s o := by
  induction h with
  | ret hs hq => exact (hQ _ hq) ▸ .ret hs
  | back hs hp => exact .goto hs (hP _ hp)
  | goto hs _ ih => exact .goto hs ih
  | exit hr hq => exact (hQ _ hq) ▸ hr

/-- A path through one step: the step from `l`, `s` goes to `l'`, `s'`, and the paths from there
are paths from `l`, `s`. With `apply`, the equation of the step is the first new goal. -/
theorem Visits.of_next {L σ R : Type} {b : Leaf L σ R} {head : L} {P : σ → Prop} {Q : R → Prop}
    {l l' : L} {s s' : σ} (hs : b.step l s = .ok (.goto l' s')) (h : Visits b head P Q l' s') :
    Visits b head P Q l s :=
  .goto hs h

/-- The loop rule in path form: from each `x` in `I` at `head`, each path returns `out x` or
comes back to `head` at a `y` in `I` with a smaller measure and the same result. -/
theorem loop_vc {L σ R : Type} {b : Leaf L σ R} {head : L} (I : σ → Prop) (μ : σ → Nat)
    (out : σ → R)
    (step : ∀ x, I x → Visits b head (fun y => I y ∧ μ y < μ x ∧ out y = out x)
      (fun r => r = out x) head x) :
    ∀ x, I x → b.Returns noCall head x (out x) :=
  Blocks.Returns.loop I μ out fun x hx ih =>
    (step x hx).returns (fun y ⟨hy, hlt, he⟩ => he ▸ ih y hy hlt) (fun _ h => h)

/-- The loop rule in path form with the induction hypothesis: the step from `x` may use the result of
each `y` in `I` with a smaller measure. A nested loop needs it: the lemma of the inner loop ends its
paths at `head` with the hypothesis (`Visits.exit`). -/
theorem loop_vc_ih {L σ R : Type} {b : Leaf L σ R} {head : L} (I : σ → Prop) (μ : σ → Nat)
    (out : σ → R)
    (step : ∀ x, I x → (∀ y, I y → μ y < μ x → b.Returns noCall head y (out y)) →
      Visits b head (fun y => I y ∧ μ y < μ x ∧ out y = out x) (fun r => r = out x) head x) :
    ∀ x, I x → b.Returns noCall head x (out x) :=
  Blocks.Returns.loop I μ out fun x hx ih =>
    (step x hx ih).returns (fun y ⟨hy, hlt, he⟩ => he ▸ ih y hy hlt) (fun _ h => h)

end Lift.Sem
