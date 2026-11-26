module

public import Lift.Sem.Sim

@[expose] public section

/-! The simulation of blocks with one relation for each label (PIL-CALL4).

`Blocks.Returns.sim` has one relation of the states for all labels. A relation for each label can
hold the facts that are true only at some labels: for example the words that the entry block saved
on the stack, which a later block pops (`Skel/Gen/UpperProof.lean`). `Blocks.Returns.simAt` is the
same rule with `sim : L → σ → τ → Prop`; a jump to `l` and the continuation of a call at `l`
give the relation of `l`. -/

namespace Lift.Sem

open Lift.P2.Total

/-- `Next.Sim` with the relation of the target label. -/
def Next.SimAt {L σ τ R S F : Type} {Xh Yh Xl Yl : F → Type}
    (simX : ∀ f, Xh f → Xl f → Prop) (simY : ∀ f, Xh f → Xl f → Yh f → Yl f → Prop)
    (sim : L → σ → τ → Prop) (simR : R → S → Prop) :
    Next L σ R F Xh Yh → Res (Next L τ S F Xl Yl) → Prop
  | .goto l x, n => ∃ y, n = .ok (.goto l y) ∧ sim l x y
  | .ret r, n => ∃ r', n = .ok (.ret r') ∧ simR r r'
  | .call f x k, n => ∃ x' k', n = .ok (.call f x' k') ∧ simX f x x' ∧
      ∀ y y', simY f x x' y y' → (k y).1 = (k' y').1 ∧ sim (k y).1 (k y).2 (k' y').2

/-- `Blocks.Returns.sim` with one relation for each label. -/
theorem Blocks.Returns.simAt {L σ τ R S F : Type} {Xh Yh Xl Yl : F → Type}
    {hi : Blocks L σ R F Xh Yh} {lo : Blocks L τ S F Xl Yl}
    {calleeHi : ∀ f, Xh f → Yh f → Prop} {calleeLo : ∀ f, Xl f → Yl f → Prop}
    (simX : ∀ f, Xh f → Xl f → Prop) (simY : ∀ f, Xh f → Xl f → Yh f → Yl f → Prop)
    (sim : L → σ → τ → Prop) (simR : R → S → Prop)
    (callee : ∀ f, Refines (simX f) (simY f) (calleeHi f) (calleeLo f))
    (block : ∀ l x y n, sim l x y → hi.step l x = .ok n →
      Next.SimAt simX simY sim simR n (lo.step l y))
    {l : L} {x : σ} {y : τ} {r : R} (h : hi.Returns calleeHi l x r) (hs : sim l x y) :
    ∃ r', lo.Returns calleeLo l y r' ∧ simR r r' := by
  induction h generalizing y with
  | ret hstep =>
    obtain ⟨r', hlo, hr⟩ := block _ _ y _ hs hstep
    exact ⟨r', .ret hlo, hr⟩
  | goto hstep _ ih =>
    obtain ⟨y', hlo, hs'⟩ := block _ _ y _ hs hstep
    obtain ⟨r', h', hr⟩ := ih hs'
    exact ⟨r', .goto hlo h', hr⟩
  | call hstep hc _ ih =>
    obtain ⟨xl, kl, hlo, hx, hk⟩ := block _ _ y _ hs hstep
    obtain ⟨yl, hcl, hy⟩ := callee _ _ xl _ hx hc
    obtain ⟨hl, hs'⟩ := hk _ yl hy
    obtain ⟨r', h', hr⟩ := ih hs'
    rw [hl] at h'
    exact ⟨r', .call hlo hcl h', hr⟩

/-- `Next.Sim` of a uniform relation is `Next.SimAt` of the same relation at each label. -/
theorem Next.SimAt.of_sim {L σ τ R S F : Type} {Xh Yh Xl Yl : F → Type}
    {simX : ∀ f, Xh f → Xl f → Prop} {simY : ∀ f, Xh f → Xl f → Yh f → Yl f → Prop}
    {sim : σ → τ → Prop} {simR : R → S → Prop} {n : Next L σ R F Xh Yh}
    {m : Res (Next L τ S F Xl Yl)} (h : Next.Sim simX simY sim simR n m) :
    Next.SimAt simX simY (fun _ => sim) simR n m := by
  cases n <;> exact h

end Lift.Sem
