module

public import Kraken.StateCfg
import all Kraken.StateCfg

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace ProofKit

/-- Change only the external continuation of a control-flow block. -/
theorem intercept_mono_exit [Host] {ls : List Label} {s₀ t : MachineData}
    {I : CfgLabel → Nat → Unit → MachineData → Prop}
    {E E' : Int64 → MachineData → Prop} {a : Int64}
    (h : Program.Intercept ls s₀ I E a t) (he : E a t → E' a t) :
    Program.Intercept ls s₀ I E' a t :=
  h.imp id (fun ⟨hx, hs⟩ => ⟨he hx, hs⟩)

/-- Stop at the call boundary of a symbol without a function declaration.
The external implementation is outside this contract. -/
theorem external_call_spec [Host] [FunDecls] (f : Label)
    (hf : FunDecls.at (label f) = none) (asz osz : Width)
    (K : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true
        ∧ ∀ ra, E (label f) (s.pushRa ra) ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ K; E ⦄ := by
  refine ⟨fun s ⟨hmapped, hpost⟩ => Program.wp_single fun h _ _ _ _ hj => ?_⟩
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, hload, Effects.All]
  rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
  refine hj (label f) (s.pushRa h.embedding.endAddr) ?_
  simpa only [Executable.StepOut, hf, Option.map_none] using hpost h.embedding.endAddr

/-- Calls to `f` return to an address distinct from the external exit symbol. -/
def ReturnAddressDistinct [Host] (f exit : Label) : Prop :=
  ∀ i asz osz, Host.prog[i]? = some (.instr (.regular asz osz
    (.call (.rel (.sub (.label f) .after_current_instruction))))) →
    label exit ≠ Host.addrOf (i + 1)

/-- A call contract with a normal return and an external exit. -/
abbrev CallSpecWithExit [Host] [FunDecls] (f exit : Label)
    (Pre : MachineData → Prop) (Post : MachineData → MachineData → Prop)
    (Exits : MachineData → MachineData → Prop) (m : MachineData → Modifies) : Prop :=
  ∀ asz osz (K : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true ∧ Pre s
        ∧ (∀ t, Post s t → (m s).Agree s t → K () t)
        ∧ (∀ t, Exits s t → E (label exit) t) ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ K; E ⦄

/-- Pass an external exit through a function call. -/
theorem callSpecWithExit_of_triple [Host] [FunDecls] {f exit : Label} {g : Fragment}
    (hg : FunDecls.at (label f) = some g) (hreturn : ReturnAddressDistinct f exit)
    {Pre : MachineData → Prop} {Post : MachineData → MachineData → Prop}
    {Exits : MachineData → MachineData → Prop} {m : MachineData → Modifies}
    (hbody : ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ Pre s ⦄ g.prog
      ⦃ (fun _ _ => False);
        fun a t => (a = ra ∧ Post s t ∧ (m s).Agree s t) ∨ (a = label exit ∧ Exits s t) ⦄) :
    CallSpecWithExit f exit Pre Post Exits m := by
  intro asz osz K E
  refine ⟨fun s ⟨hmapped, hpre, hnormal, hexit⟩ => Program.wp_single fun h _ _ _ _ hj => ?_⟩
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, hload, Effects.All]
  rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
  refine hj (label f) (s.pushRa h.embedding.endAddr) ?_
  unfold Executable.StepOut
  simp only [hg, Option.map_some, Program.WP.MachineData.stackBelow_pushRa, ite_true]
  have hk := h.embedding.isInfixAt
  have hd := Host.exe_getElem? h.embedding.start
  rw [hk.cons.1, Option.map_some] at hd
  have hz : 0 < Kraken.Layout.size Directive h.embedding.start :=
    Host.instr_size_pos _ _ hk.cons.1 (by rintro ⟨⟩)
  have hft : Host.exe.fallthrough h.embedding.startAddr = h.embedding.endAddr :=
    Host.fallthrough_addrOf hd hz
  rw [hft]
  have hne : label exit ≠ h.embedding.endAddr := hreturn _ asz osz hk.cons.1
  refine Program.wp_mono (fun _ h => h) ?_ ((hbody s h.embedding.endAddr).1 _ ⟨rfl, hpre⟩)
  rintro u (⟨hpc, hpost, hagree⟩ | ⟨hpc, habort⟩)
  · simp only [hpc, ite_true]
    exact ⟨by trivial, hnormal _ hpost hagree⟩
  · simp only [hpc, hne, ite_false]
    exact hexit _ habort

end ProofKit
