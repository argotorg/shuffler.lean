module

public import BbuKraken.Unit.Plan.EntryInvoke
import all BbuKraken.Unit.Plan.EntryInvoke

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

theorem RunQ.al {g g' : EG} {s t u : MachineData} (h : RunQ g g' s t)
    (ha : al u = al t) : RunQ g g' s u := by
  refine ⟨?_, h.2⟩
  obtain ⟨us, hal, hstate, hp, hd, ho, hsrc, hc, hi, hcount⟩ := h.1
  exact ⟨us, ha.trans hal, hstate, hp, hd, ho, hsrc, hc, hi, hcount⟩

set_option maxRecDepth 8192 in
theorem entry_tail [Host] [FunDecls] (g g' : EG) (F : MProp 64)
    (s t : MachineData) (ra : Int64) (lo locals : List Word)
    (hb : Bd g' F s ra lo locals t) (hq : RunQ g g' s t)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hblocked : ∀ u, Bd g' F s ra lo locals u → RunQ g g' s u → al u = 1#8 →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.11") u)
    (hdone : ∀ u, Bd g' F s ra lo locals u → RunQ g g' s u →
      al u ≠ 1#8 → al u ≠ 2#8 →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.10") u)
    (hfail : ∀ u, Bd g' F s ra lo locals u → RunQ g g' s u →
      al u = 2#8 → rdx u = -2#64 → K () u) :
    WP.wp entryTail K (Program.Intercept planAsm.labels (s.pushRa ra) I' E) t := by
  unfold entryTail
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.plan.11" =>
    rename_i hz
    symexec_norm at hz
    simp only [BitVec.zero_eq, Idioms.sub_beq_zero, beq_iff_eq] at hz
    apply hblocked
    · apply hb.next <;> rfl
    · exact hq.al rfl
    · exact hz
  | goto ".LB.plan.10" =>
    rename_i h1 h2
    symexec_norm at h1 h2
    simp only [BitVec.zero_eq, Idioms.sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne] at h1 h2
    apply hdone
    · apply hb.next <;> rfl
    · exact hq.al rfl
    · exact h1
    · exact h2
  | other =>
    rename_i h1 h2
    symexec_norm at h1 h2
    simp only [BitVec.zero_eq, Idioms.sub_beq_zero, Bool.not_eq_false', beq_iff_eq] at h2
    apply hfail
    · apply hb.next <;> rfl
    · exact hq.al rfl
    · exact h2
    · rfl

end Bbu.Unit.EntryValidU
