module

public import Lift.Sem.Model

@[expose] public section

namespace Lift.Sem

open Lift.P2.Total

/-- The exit of a block: a jump, a return, or a call of `f` on `x` that goes on at `k y` with the result `y`. -/
inductive Next (L σ R F : Type) (X Y : F → Type) where
  | goto (l : L) (s : σ)
  | ret (r : R)
  | call (f : F) (x : X f) (k : Y f → L × σ)

/-- A model as a step function on labelled blocks; the callee `f` takes an `X f` and returns a `Y f`. -/
structure Blocks (L σ R F : Type) (X Y : F → Type) where
  step : L → σ → Res (Next L σ R F X Y)

/-- Blocks with no call. -/
abbrev Leaf (L σ R : Type) : Type := Blocks L σ R Empty Empty.elim Empty.elim

/-- The callee models of blocks with no call. -/
def noCallee (f : Empty) : Model (Empty.elim f) (Empty.elim f) := f.elim

/-- The callee relations of blocks with no call. -/
def noCall (f : Empty) : Empty.elim f → Empty.elim f → Prop := (noCallee f).returns

/-- The blocks return `r` from label `l` and state `s`; `callee f x y` is the meaning of a call. -/
inductive Blocks.Returns {L σ R F : Type} {X Y : F → Type} (b : Blocks L σ R F X Y)
    (callee : ∀ f, X f → Y f → Prop) : L → σ → R → Prop
  | ret {l : L} {s : σ} {r : R} : b.step l s = .ok (.ret r) → Returns b callee l s r
  | goto {l l' : L} {s s' : σ} {r : R} : b.step l s = .ok (.goto l' s') →
      Returns b callee l' s' r → Returns b callee l s r
  | call {l : L} {s : σ} {f : F} {x : X f} {k : Y f → L × σ} {y : Y f} {r : R} :
      b.step l s = .ok (.call f x k) → callee f x y → Returns b callee (k y).1 (k y).2 r →
      Returns b callee l s r

/-- Run the blocks for at most `fuel` blocks; `callee f` runs the callee `f` (for tests). -/
def Blocks.run {L σ R F : Type} {X Y : F → Type} (b : Blocks L σ R F X Y)
    (callee : ∀ f, X f → Res (Y f)) : Nat → L → σ → Res R
  | 0, _, _ => .noFuel
  | fuel + 1, l, s => match b.step l s with
    | .ok (.goto l' s') => b.run callee fuel l' s'
    | .ok (.ret r) => .ok r
    | .ok (.call f x k) => match callee f x with
      | .ok y => b.run callee fuel (k y).1 (k y).2
      | .stuck why => .stuck why
      | .noFuel => .noFuel
    | .stuck why => .stuck why
    | .noFuel => .noFuel

/-- A result of `run` is a result of `Returns` when each callee run is sound for `callee`. -/
theorem Blocks.run_sound {L σ R F : Type} {X Y : F → Type} (b : Blocks L σ R F X Y)
    {run : ∀ f, X f → Res (Y f)} {callee : ∀ f, X f → Y f → Prop}
    (hc : ∀ f x y, run f x = .ok y → callee f x y) {fuel : Nat} {l : L} {s : σ} {r : R}
    (h : b.run run fuel l s = .ok r) : b.Returns callee l s r := by
  induction fuel generalizing l s with
  | zero => cases h
  | succ fuel ih =>
    simp only [Blocks.run] at h
    split at h
    · rename_i hstep
      exact .goto hstep (ih h)
    · rename_i hstep
      cases h
      exact .ret hstep
    · rename_i hstep
      split at h
      · rename_i hy
        exact .call hstep (hc _ _ _ hy) (ih h)
      · cases h
      · cases h
    · cases h
    · cases h

/-- `Returns` gives at most one result when each callee relation does. -/
theorem Blocks.Returns.unique {L σ R F : Type} {X Y : F → Type} {b : Blocks L σ R F X Y}
    {callee : ∀ f, X f → Y f → Prop} (hc : ∀ f x y y', callee f x y → callee f x y' → y = y')
    {l : L} {s : σ} {r r' : R} (h : b.Returns callee l s r) (h' : b.Returns callee l s r') :
    r = r' := by
  induction h generalizing r' with
  | ret hs =>
    cases h' with
    | ret hs' => rw [hs] at hs'; cases hs'; rfl
    | goto hs' _ => rw [hs] at hs'; cases hs'
    | call hs' _ _ => rw [hs] at hs'; cases hs'
  | goto hs _ ih =>
    cases h' with
    | ret hs' => rw [hs] at hs'; cases hs'
    | goto hs' h'' => rw [hs] at hs'; cases hs'; exact ih h''
    | call hs' _ _ => rw [hs] at hs'; cases hs'
  | call hs hy _ ih =>
    cases h' with
    | ret hs' => rw [hs] at hs'; cases hs'
    | goto hs' _ => rw [hs] at hs'; cases hs'
    | call hs' hy' h'' =>
      rw [hs] at hs'
      cases hs'
      obtain rfl := hc _ _ _ _ hy hy'
      exact ih h''

/-- A jump: the blocks return from the target. -/
theorem Blocks.Returns.of_goto {L σ R F : Type} {X Y : F → Type} {b : Blocks L σ R F X Y}
    {callee : ∀ f, X f → Y f → Prop} {l l' : L} {x x' : σ} {r : R}
    (h : b.Returns callee l x r) (hs : b.step l x = .ok (.goto l' x')) :
    b.Returns callee l' x' r := by
  cases h with
  | ret h' => rw [hs] at h'; cases h'
  | goto h' h'' => rw [hs] at h'; cases h'; exact h''
  | call h' => rw [hs] at h'; cases h'

/-- A block that is `stuck` does not return. -/
theorem Blocks.Returns.not_stuck {L σ R F : Type} {X Y : F → Type} {b : Blocks L σ R F X Y}
    {callee : ∀ f, X f → Y f → Prop} {l : L} {x : σ} {r : R} {why : String}
    (hs : b.step l x = .stuck why) : ¬ b.Returns callee l x r := by
  intro h
  cases h with
  | ret h' | goto h' _ | call h' => rw [hs] at h'; cases h'

/-- A loop rule: the blocks return `out x` from `head` for each `x` in `I`, if they return it on
the hypothesis that they return `out y` for each `y` in `I` with a smaller measure `μ`. -/
theorem Blocks.Returns.loop {L σ R F : Type} {X Y : F → Type} {b : Blocks L σ R F X Y}
    {callee : ∀ f, X f → Y f → Prop} {head : L} (I : σ → Prop) (μ : σ → Nat) (out : σ → R)
    (step : ∀ x, I x → (∀ y, I y → μ y < μ x → b.Returns callee head y (out y)) →
      b.Returns callee head x (out x)) :
    ∀ x, I x → b.Returns callee head x (out x) := by
  intro x hx
  induction h : μ x using Nat.strongRecOn generalizing x with
  | ind k ih => exact step x hx fun y hy hlt => ih (μ y) (h ▸ hlt) y hy rfl

/-- If the code follows each block of `b` from `at_` to the exit of the block, and each callee
decompiles, then the code decompiles to each model whose returns are returns of `b` from `entry`.
At a call the code reaches the `rep` of the callee, and goes on from each state of its `post`. -/
theorem Decompiles.ofBlocks {L σ A R F : Type} {X Y : F → Type} {step : MachineState → Effects}
    {M : Model A R} (b : Blocks L σ R F X Y) (callee : ∀ f, Model (X f) (Y f))
    (hcallee : ∀ f, Decompiles step (callee f)) (entry : L) (init : A → σ)
    (at_ : CpuPolicy → A → MachineState → L → σ → MachineState → Prop)
    (hret : ∀ a r, M.returns a r → b.Returns (fun f => (callee f).returns) entry (init a) r)
    (start : ∀ policy a s, M.rep policy a s → at_ policy a s entry (init a) s)
    (block : ∀ policy a s₀ l x s, at_ policy a s₀ l x s → ∀ n, b.step l x = .ok n →
      Reaches step policy (fun t => match n with
        | .goto l' x' => at_ policy a s₀ l' x' t
        | .ret r => M.post a r s₀ t
        | .call f y k => (callee f).rep policy y t ∧
            ∀ z u, (callee f).post y z t u → at_ policy a s₀ (k z).1 (k z).2 u) s) :
    Decompiles step M := by
  intro policy a r s hrep hr
  suffices key : ∀ l x t, b.Returns (fun f => (callee f).returns) l x r →
      at_ policy a s l x t → Reaches step policy (M.post a r s) t from
    key entry (init a) s (hret a r hr) (start policy a s hrep)
  intro l x t h
  clear hr
  induction h generalizing t with
  | ret hs => exact fun hat => block policy a s _ _ t hat _ hs
  | goto hs _ ih => exact fun hat => (block policy a s _ _ t hat _ hs).seq fun u hu => ih u hu
  | call hs hy _ ih =>
    exact fun hat => (block policy a s _ _ t hat _ hs).seq fun u hu =>
      (hcallee _ policy _ _ u hu.1 hy).seq fun v hv => ih v (hu.2 _ v hv)

/-- A call: `Decompiles` of the callee gives its `post`, from which the caller goes on. -/
theorem Decompiles.call {A R : Type} {step : MachineState → Effects} {callee : Model A R}
    {policy : CpuPolicy} {Q : MachineState → Prop} {a : A} {r : R} {s : MachineState}
    (h : Decompiles step callee) (hrep : callee.rep policy a s) (hret : callee.returns a r)
    (k : ∀ t, callee.post a r s t → Reaches step policy Q t) : Reaches step policy Q s := by
  exact (h policy a r s hrep hret).seq k

end Lift.Sem
