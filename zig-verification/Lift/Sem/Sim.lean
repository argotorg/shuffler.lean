module

public import Lift.Sem.Blocks

@[expose] public section

namespace Lift.Sem

open Lift.P2.Total

/-- If the high relation returns, the low relation returns a related result. -/
def Refines {Xh Xl Yh Yl : Type} (simX : Xh → Xl → Prop) (simY : Xh → Xl → Yh → Yl → Prop)
    (hi : Xh → Yh → Prop) (lo : Xl → Yl → Prop) : Prop :=
  ∀ xh xl yh, simX xh xl → hi xh yh → ∃ yl, lo xl yl ∧ simY xh xl yh yl

/-- A high block exit and a low block result are related: the same exit kind and label with
related states, results or arguments; a call has the same callee and related continuations. -/
def Next.Sim {L σ τ R S F : Type} {Xh Yh Xl Yl : F → Type}
    (simX : ∀ f, Xh f → Xl f → Prop) (simY : ∀ f, Xh f → Xl f → Yh f → Yl f → Prop)
    (sim : σ → τ → Prop) (simR : R → S → Prop) :
    Next L σ R F Xh Yh → Res (Next L τ S F Xl Yl) → Prop
  | .goto l x, n => ∃ y, n = .ok (.goto l y) ∧ sim x y
  | .ret r, n => ∃ r', n = .ok (.ret r') ∧ simR r r'
  | .call f x k, n => ∃ x' k', n = .ok (.call f x' k') ∧ simX f x x' ∧
      ∀ y y', simY f x x' y y' → (k y).1 = (k' y').1 ∧ sim (k y).2 (k' y').2

/-- If each high block from related states has a related low block, and each callee refines,
then each return of `hi` has a return of `lo` with a related result. -/
theorem Blocks.Returns.sim {L σ τ R S F : Type} {Xh Yh Xl Yl : F → Type}
    {hi : Blocks L σ R F Xh Yh} {lo : Blocks L τ S F Xl Yl}
    {calleeHi : ∀ f, Xh f → Yh f → Prop} {calleeLo : ∀ f, Xl f → Yl f → Prop}
    (simX : ∀ f, Xh f → Xl f → Prop) (simY : ∀ f, Xh f → Xl f → Yh f → Yl f → Prop)
    (sim : σ → τ → Prop) (simR : R → S → Prop)
    (callee : ∀ f, Refines (simX f) (simY f) (calleeHi f) (calleeLo f))
    (block : ∀ l x y n, sim x y → hi.step l x = .ok n →
      Next.Sim simX simY sim simR n (lo.step l y))
    {l : L} {x : σ} {y : τ} {r : R} (h : hi.Returns calleeHi l x r) (hs : sim x y) :
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

/-- `Above lo hi` from a `Refines` fact of the two `returns` relations. `simX` and `simY` can use
the policy and the entry state (for example for a frame). -/
theorem Above.ofRefines {A B R S : Type} {lo : Model B S} {hi : Model A R}
    (simX : CpuPolicy → MachineState → A → B → Prop)
    (simY : CpuPolicy → MachineState → A → B → R → S → Prop)
    (ref : ∀ policy s, Refines (simX policy s) (simY policy s) hi.returns lo.returns)
    (start : ∀ policy a s, hi.rep policy a s → ∃ b, lo.rep policy b s ∧ simX policy s a b)
    (post : ∀ policy a b s r r' t, hi.rep policy a s → lo.rep policy b s →
      simY policy s a b r r' → lo.post b r' s t → hi.post a r s t) :
    Above lo hi := by
  intro policy a r s hrep hret
  obtain ⟨b, hrep', hs⟩ := start policy a s hrep
  obtain ⟨r', hret', hr⟩ := ref policy s a b r hs hret
  exact ⟨b, r', hrep', hret', fun t ht => post policy a b s r r' t hrep hrep' hr ht⟩

end Lift.Sem
