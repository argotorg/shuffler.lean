module

public import BbuKraken.Unit.Plan.Defs
import all BbuKraken.Unit.Plan.Defs
public import BbuKraken.Sep.ExitContract
import all BbuKraken.Sep.ExitContract

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit

open Bbu.Sep

section
variable {α : Type} (V : Addr → α → MProp 64) (ok : α → Prop)

abbrev VThmWithExit [Host] [FunDecls] (prog : Program)
    (A : α → MachineData → Prop) (d : Nat)
    (Q X : α → α → MachineData → MachineData → Prop) : Prop :=
  ∀ S a F, BodyWithExit prog (VPre V ok S a F A d)
    (fun s t => VPost V ok S F d (fun a' t => Q a a' s t) s t)
    (fun s t => VPost V ok S F d (fun a' t => X a a' s t) s t)

abbrev VSpecWithExit [Host] [FunDecls] (f : Label)
    (A : α → MachineData → Prop) (d : Nat)
    (Q X : α → α → MachineData → MachineData → Prop) : Prop :=
  ∀ asz osz (K : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => ∃ S a F, VPre V ok S a F A d s
        ∧ (∀ t, VPost V ok S F d (fun a' t => Q a a' s t) s t → Sep.mod.Agree s t → K () t)
        ∧ (∀ t, VPost V ok S F d (fun a' t => X a a' s t) s t →
          t.regs.get64 .rdi = 1#64 → E (label "exit") t) ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ K; E ⦄
end

theorem vspecWithExit_of_body [Host] [FunDecls]
    {α : Type} {V : Addr → α → MProp 64} {ok : α → Prop} {f : Label} {g₀ : Fragment}
    (hg : FunDecls.at (label f) = some g₀)
    (hr : ProofKit.ReturnAddressDistinct f "exit")
    {A : α → MachineData → Prop} {d : Nat}
    {Q X : α → α → MachineData → MachineData → Prop}
    (hb : VThmWithExit V ok g₀.prog A d Q X) :
    VSpecWithExit V ok f A d Q X := by
  intro asz osz K E
  refine ⟨fun s ⟨S, a, F, hp, hn, hx⟩ => ?_⟩
  exact (ProofKit.callSpecWithExit_of_triple hg hr (hb S a F) asz osz K E).1 s
    ⟨hp.mem.isSome, hp, hn, fun t ⟨harg, hpost⟩ => hx t hpost harg⟩

abbrev BThmWithExit [Host] [FunDecls] (prog : Program) (A : BG → MachineData → Prop)
    (d : Nat) (Q X : BG → BG → MachineData → MachineData → Prop) : Prop :=
  VThmWithExit BView BG.Ok prog A d Q X

abbrev BSpecWithExit [Host] [FunDecls] (f : Label) (A : BG → MachineData → Prop)
    (d : Nat) (Q X : BG → BG → MachineData → MachineData → Prop) : Prop :=
  VSpecWithExit BView BG.Ok f A d Q X

end Bbu.Unit
