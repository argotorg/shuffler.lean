import BbuKraken.Unit.Plan.Call

/-! The view contracts and the `Emission` contracts describe the same owned memory.
These lemmas let an `Emission` unit use the frame and call rules of the planner units. -/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit

open Bbu.Sep

theorem emissionPre_iff {S : Addr} {g : G} {F : MProp 64}
    {A : G → MachineData → Prop} {d : Nat} {s : MachineData} :
    VPre View G.Ok S g F A d s ↔ Sep.Pre S g F A d s := by
  constructor
  · rintro ⟨hdi, hok, hA, fr, v, hl, hm⟩
    exact ⟨hdi, hok, ⟨fr, v, hl, (sep_lc _ _ _).symm ▸ hm⟩, hA⟩
  · rintro ⟨hdi, hok, ⟨fr, v, hl, hm⟩, hA⟩
    exact ⟨hdi, hok, hA, fr, v, hl, sep_lc _ _ _ ▸ hm⟩

theorem emissionPost_iff {S : Addr} {F : MProp 64} {d : Nat}
    {Q : G → MachineData → Prop} {s t : MachineData} :
    VPost View G.Ok S F d Q s t ↔ Sep.Post S F d Q s t := by
  constructor
  · rintro ⟨g, hQ, hok, fr, v, hl, hm⟩
    exact ⟨g, fr, v, hQ, hok, hl, (sep_lc _ _ _).symm ▸ hm⟩
  · rintro ⟨g, fr, v, hQ, hok, hl, hm⟩
    exact ⟨g, hQ, hok, fr, v, hl, sep_lc _ _ _ ▸ hm⟩

theorem emissionVSpec [Host] [FunDecls] {f : Label}
    {A : G → MachineData → Prop} {d : Nat} {Q : G → G → MachineData → MachineData → Prop}
    (h : Spec f A d Q) : VSpec View G.Ok f A d Q := by
  intro asz osz K E
  refine ⟨fun s ⟨S, g, F, hp, hk⟩ => ?_⟩
  exact (h asz osz K E).1 s ⟨S, g, F, emissionPre_iff.mp hp,
    fun t ht ha => hk t (emissionPost_iff.mpr ht) ha⟩

theorem emissionUnit [Host] [FunDecls] {p : Program}
    {A : G → MachineData → Prop} {d : Nat} {Q : G → G → MachineData → MachineData → Prop}
    (h : VThm View G.Ok p A d Q) : UnitThm p A d Q := by
  intro S g F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  exact Program.wp_mono (fun _ h => h)
    (fun _ ⟨ha, hq, hag⟩ => ⟨ha, emissionPost_iff.mp hq, hag⟩)
    ((h S g F s ra).1 t ⟨ht, emissionPre_iff.mpr hp⟩)

theorem Kb.vmem {P F : MProp 64} {s t : MachineData} {ra : Int64} {fr : List Word}
    {d : Word} (h : Kb (P ∗ F) s ra fr d t) :
    (P ∗ Stk (rsp s) fr ra.toBitVec ∗ F).get t.dmem := by
  have := h.mem
  rwa [sep_lc] at this

theorem Kg.kp {S : Addr} {g : G} {F : MProp 64} {s t : MachineData} {ra : Int64}
    {fr : List Word} (h : Kg (View S g ∗ F) s ra fr t) : Kp S g F s ra fr t :=
  ⟨h.vmem, h.sp, h.bx, h.bp, h.r12, h.r13, h.r14, h.r15⟩

end Bbu.Unit
