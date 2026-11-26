module

public import Lift.Sem.Blocks

@[expose] public section

namespace Lift.Sem

/-- A region executes block labels and stops on a cut label. -/
inductive CutLabel (L : Type) where
  | block (label : L)
  | stop (label : L)
  deriving DecidableEq, Repr

/-- The exit of a region retains the state at a cut, or the return value. -/
inductive CutExit (L σ R : Type) where
  | next (label : L) (state : σ)
  | ret (result : R)
  deriving DecidableEq, Repr

/-- Execute a block once before cutting any later arrival at a selected label.
Calls keep their original input and output types. Their continuation also goes through the cut. -/
def Blocks.cut {L σ R F : Type} {X Y : F → Type} (b : Blocks L σ R F X Y)
    (heads : L → Bool) : Blocks (CutLabel L) σ (CutExit L σ R) F X Y where
  step label s := match label with
    | .stop l => .ok (.ret (.next l s))
    | .block l => match b.step l s with
      | .ok (.goto k t) => .ok (.goto (if heads k then .stop k else .block k) t)
      | .ok (.ret r) => .ok (.ret (.ret r))
      | .ok (.call f x k) => .ok (.call f x fun y =>
          (if heads (k y).1 then .stop (k y).1 else .block (k y).1, (k y).2))
      | .stuck why => .stuck why
      | .noFuel => .noFuel

/-- A region exit is sufficient to finish with `r`: continue at its cut or check its return. -/
def CutExit.Finishes {L σ R F : Type} {X Y : F → Type} (b : Blocks L σ R F X Y)
    (callee : ∀ f, X f → Y f → Prop) (r : R) : CutExit L σ R → Prop
  | .next l s => b.Returns callee l s r
  | .ret v => v = r

/-- Compose a finite region run with the return at its boundary. -/
theorem Blocks.cut_sound {L σ R F : Type} {X Y : F → Type} (b : Blocks L σ R F X Y)
    (heads : L → Bool) (callee : ∀ f, X f → Y f → Prop)
    {l : L} {s : σ} {out : CutExit L σ R} {r : R}
    (h : (b.cut heads).Returns callee (.block l) s out)
    (finish : out.Finishes b callee r) : b.Returns callee l s r := by
  let source : CutLabel L → L := fun q => match q with | .block l | .stop l => l
  have key : ∀ {q : CutLabel L} {x : σ} {e : CutExit L σ R},
      (b.cut heads).Returns callee q x e → e.Finishes b callee r → b.Returns callee (source q) x r := by
    intro q x e hr
    induction hr with
    | @ret q x e hs =>
      cases q with
      | stop k => cases hs; exact fun ht => ht
      | block k =>
        cases he : b.step k x with
        | ok n =>
          cases n with
          | ret v =>
            simp only [Blocks.cut, he, Res.ok.injEq, Next.ret.injEq] at hs
            subst e
            intro ht
            exact ht ▸ Blocks.Returns.ret he
          | goto k' t => simp [Blocks.cut, he] at hs
          | call f a k' => simp [Blocks.cut, he] at hs
        | stuck why => simp [Blocks.cut, he] at hs
        | noFuel => simp [Blocks.cut, he] at hs
    | @goto q q' x x' e hs _ ih =>
      cases q with
      | stop k => simp [Blocks.cut] at hs
      | block k =>
        cases he : b.step k x with
        | ok n =>
          cases n with
          | goto k' t =>
            simp only [Blocks.cut, he, Res.ok.injEq, Next.goto.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            intro ht
            have hk := ih ht
            split at hk <;> exact Blocks.Returns.goto he hk
          | ret v => simp [Blocks.cut, he] at hs
          | call f a k' => simp [Blocks.cut, he] at hs
        | stuck why => simp [Blocks.cut, he] at hs
        | noFuel => simp [Blocks.cut, he] at hs
    | @call q x f a k' v e hs hy _ ih =>
      cases q with
      | stop k => simp [Blocks.cut] at hs
      | block k =>
        cases he : b.step k x with
        | ok n =>
          cases n with
          | call f a k' =>
            simp only [Blocks.cut, he, Res.ok.injEq, Next.call.injEq] at hs
            rcases hs with ⟨hf, ha, hk⟩
            cases hf
            cases ha
            cases hk
            intro ht
            have hk := ih ht
            dsimp only at hk
            split at hk <;> exact Blocks.Returns.call he hy hk
          | ret v => simp [Blocks.cut, he] at hs
          | goto k' t => simp [Blocks.cut, he] at hs
        | stuck why => simp [Blocks.cut, he] at hs
        | noFuel => simp [Blocks.cut, he] at hs
  exact key h finish

/-- The invariant, rank, and output conditions on one region exit. -/
def CutExit.Progress {L σ R : Type} (I : L → σ → Prop) (rank : L → σ → Nat)
    (out : L → σ → R) (l : L) (s : σ) : CutExit L σ R → Prop
  | .next k t => I k t ∧ rank k t < rank l s ∧ out k t = out l s
  | .ret r => r = out l s

/-- Local region proofs compose across any number of loop heads.
A rank decrease is required at every cut, including transitions into or out of nested loops. -/
theorem Blocks.cut_loop {L σ R F : Type} {X Y : F → Type} (b : Blocks L σ R F X Y)
    (heads : L → Bool) (callee : ∀ f, X f → Y f → Prop)
    (I : L → σ → Prop) (rank : L → σ → Nat) (out : L → σ → R)
    (step : ∀ l s, I l s → ∃ e, (b.cut heads).Returns callee (.block l) s e ∧
      e.Progress I rank out l s) :
    ∀ l s, I l s → b.Returns callee l s (out l s) := by
  intro l s hs
  induction h : rank l s using Nat.strongRecOn generalizing l s with
  | ind n ih =>
    obtain ⟨e, he, hp⟩ := step l s hs
    apply b.cut_sound heads callee he
    cases e with
    | ret r => exact hp
    | next k t =>
      obtain ⟨ht, hlt, hout⟩ := hp
      have hk := ih (rank k t) (h ▸ hlt) k t ht rfl
      exact hout ▸ hk

end Lift.Sem
