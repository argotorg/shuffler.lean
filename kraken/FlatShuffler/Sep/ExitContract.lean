module

public import FlatShuffler.Sep.Contract
import all FlatShuffler.Sep.Contract
public import ProofKit.ExternalCall
import all ProofKit.ExternalCall

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace FlatShuffler.Sep

/-- The first of two free words is the return slot for an external call
after `subq $8, %rsp`. -/
theorem Stk.two (sp : Addr) (x y v : Word) (P F : MProp 64) :
    P ∗ Stk sp [x, y] v ∗ F =
      Wd (sp - 24#64) x ∗ (P ∗ Wd (sp - 16#64) y ∗ Wd (sp - 8#64) v ∗ F) := by
  unfold Stk
  simp only [List.length_cons, List.length_nil, Arr, MProp.sep_emp]
  have ha : sp - 8#64 - BitVec.ofNat 64 (8 * (0 + 1 + 1)) = sp - 24#64 := by bv_omega
  have hb : sp - 24#64 + 8#64 = sp - 16#64 := by bv_omega
  rw [ha, hb]
  ac_rfl

/-- A body returns to its caller or reaches the external `exit(1)` boundary.
The failure relation can refer to the initial state and the memory at exit. -/
abbrev BodyWithExit [Host] [FunDecls] (prog : Program) (pre : MachineData → Prop)
    (post exits : MachineData → MachineData → Prop) : Prop :=
  ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ pre s ⦄ prog
    ⦃ (fun _ _ => False); fun a t =>
      (a = ra ∧ post s t ∧ mod.Agree s t) ∨
      (a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧ exits s t) ⦄

/-- A caller handles normal returns and assertion exits separately. -/
abbrev SpecWithExit [Host] [FunDecls] (f : Label) (A : G → MachineData → Prop) (d : Nat)
    (Q X : G → G → MachineData → MachineData → Prop) : Prop :=
  ∀ asz osz (K : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => ∃ S g F, Pre S g F A d s
        ∧ (∀ t, Post S F d (fun g' t => Q g g' s t) s t → mod.Agree s t → K () t)
        ∧ (∀ t, Post S F d (fun g' t => X g g' s t) s t →
          t.regs.get64 .rdi = 1#64 → E (label "exit") t) ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ K; E ⦄

theorem specWithExit_of_body [Host] [FunDecls] {f : Label} {g₀ : Fragment}
    (hg : FunDecls.at (label f) = some g₀)
    (hr : ProofKit.ReturnAddressDistinct f "exit")
    {A : G → MachineData → Prop} {d : Nat}
    {Q X : G → G → MachineData → MachineData → Prop}
    (hb : ∀ S g F, BodyWithExit g₀.prog (Pre S g F A d)
      (fun s t => Post S F d (fun g' t => Q g g' s t) s t)
      (fun s t => Post S F d (fun g' t => X g g' s t) s t)) :
    SpecWithExit f A d Q X := by
  intro asz osz K E
  refine ⟨fun s ⟨S, g, F, hp, hn, hx⟩ => ?_⟩
  exact (ProofKit.callSpecWithExit_of_triple hg hr (hb S g F) asz osz K E).1 s
    ⟨hp.isSome, hp, hn, fun t ⟨harg, hpost⟩ => hx t hpost harg⟩

abbrev SpecWWithExit [Host] [FunDecls] (f : Label) (W : MachineData → MProp 64)
    (A : G → MachineData → Prop) (d : Nat)
    (Q X : G → G → MachineData → MachineData → Prop) : Prop :=
  ∀ asz osz (K : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => ∃ S g F, Pre S g (W s ∗ F) A d s
        ∧ (∀ t, Post S (W s ∗ F) d (fun g' t => Q g g' s t) s t → mod.Agree s t → K () t)
        ∧ (∀ t, Post S (W s ∗ F) d (fun g' t => X g g' s t) s t →
          t.regs.get64 .rdi = 1#64 → E (label "exit") t) ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ K; E ⦄

theorem specWithExit_of_bodyW [Host] [FunDecls] {f : Label} {g₀ : Fragment}
    (hg : FunDecls.at (label f) = some g₀)
    (hr : ProofKit.ReturnAddressDistinct f "exit")
    {W : MachineData → MProp 64} {A : G → MachineData → Prop} {d : Nat}
    {Q X : G → G → MachineData → MachineData → Prop}
    (hb : ∀ S g F, BodyWithExit g₀.prog (fun s => Pre S g (W s ∗ F) A d s)
      (fun s t => Post S (W s ∗ F) d (fun g' t => Q g g' s t) s t)
      (fun s t => Post S (W s ∗ F) d (fun g' t => X g g' s t) s t)) :
    SpecWWithExit f W A d Q X := by
  intro asz osz K E
  refine ⟨fun s ⟨S, g, F, hp, hn, hx⟩ => ?_⟩
  exact (ProofKit.callSpecWithExit_of_triple hg hr (hb S g F) asz osz K E).1 s
    ⟨hp.isSome, hp, hn, fun t ⟨harg, hpost⟩ => hx t hpost harg⟩

end FlatShuffler.Sep
