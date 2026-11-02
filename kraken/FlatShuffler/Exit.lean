module

public import FlatShuffler.Asm
import all FlatShuffler.Asm
public import FlatShuffler.Specs
import all FlatShuffler.Specs
public import ProofKit.ExternalCall
import all ProofKit.ExternalCall
public import ProofKit.Cfg
import all ProofKit.Cfg
public import ProofKit.SymExec
import all ProofKit.SymExec

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace FlatShuffler

/-- The boundary of the C library call `exit(1)`. -/
def AssertionExit [Host] (a : Int64) (t : MachineData) : Prop :=
  a = label "exit" ∧ t.regs.get64 .rdi = 1#64

/-- An empty `Emission::pop` reaches `exit(1)`.
The external symbol is not one of this function's labels and has no Kraken body. -/
theorem pop_empty_exit [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels popAsm, label l ≠ label "exit")
    (s : MachineData)
    (hsize : Mem.loadInt s.dmem (s.regs.get64 .rdi + 32#64) 8 = some 0)
    (hstack : (Mem.loadInt s.dmem (s.regs.get64 .rsp - 16#64) 8).isSome = true) :
    ⦃ fun t => t = s ⦄ popAsm ⦃ (fun _ _ => False); AssertionExit ⦄ := by
  refine ⟨fun t ht => ?_⟩
  subst t
  refine Program.WP.cfg (fun
      | .entry, t => t = s
      | .label "_ZN12_GLOBAL__N_18Emission3popEv", t => t = s
      | .label ".LB.Emission.pop.1", t => t.dmem = s.dmem ∧ t.regs.rsp = s.regs.rsp
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht => subst ht; kvcgen64
  case «_ZN12_GLOBAL__N_18Emission3popEv» t ht =>
    subst t
    kvcgen64
    all_goals symexec_norm
    all_goals simp [hsize] at *
    all_goals try contradiction
    all_goals try decide
    all_goals try (simp only [hsize]; rfl)
    all_goals try
      cfg_goto
      · exact MachineData.stackAtOrBelow_of_rsp_eq rfl
      · exact ⟨rfl, rfl⟩
      · simp
  case «.LB.Emission.pop.1» t ht =>
    obtain ⟨hm, hsp⟩ := ht
    have he := ProofKit.external_call_spec "exit" hexit
    kvcgen64 [he]
    all_goals symexec_norm
    · simpa [hm, hsp, show ∀ x : BitVec 64, x - 8#64 - 8#64 = x - 16#64 by
        intro x; bv_omega] using hstack
    · refine Or.inr ⟨⟨rfl, rfl⟩, ?_⟩
      intro l hl ha
      exact False.elim (hout l hl ha)

end FlatShuffler
