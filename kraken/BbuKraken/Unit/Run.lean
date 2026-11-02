module

public import BbuKraken.Unit.Run.Assemble
import all BbuKraken.Unit.Run.Assemble

@[expose] public section

/-! `Emission::run` uses the planned mapping and agrees with `Flat.emissionRun`.
If the model reports an assertion failure, the assembly calls `exit(1)`.
The initial values of the lowest-height locals are existential, as in `LowestThm`.
`runA` states the concrete trace bounds and mapping conditions required by the callees. -/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit
open Bbu.Sep

theorem run_unit [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels runAsm, label l ≠ label "exit")
    (hsur : Sep.SpecWithExit Names.removeSurplus surplusA 4 surplusQ surplusX)
    (hlow : ∀ PM planned, VSpecWithExit (RunView PM planned) G.Ok Names.permuteAtLowestHeight
      (lowestA planned) lowestD (lowestQ planned) (lowestX planned))
    (hav : Sep.Spec Names.isAvailable isAvailableA 3 isAvailableQ)
    (hloop : Sep.SpecWithExit Names.buildBottomUp loopA 2068 loopQ loopX) : RunThm runAsm := by
  intro S PM planned g F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  apply Program.wp_mono (fun _ h => h) ?_
    ((RunU.run_vthm PM planned hexit hout (RunU.frame_specWithExit hsur) (hlow PM planned)
      (RunU.frame_spec hav) (RunU.frame_specWithExit hloop) S g F s ra).1 t
      ⟨ht, RunU.pre_iff.mpr hp⟩)
  rintro u (⟨ha, hq, hag⟩ | ⟨ha, harg, hx⟩)
  · exact Or.inl ⟨ha, RunU.post_iff.mp hq, hag⟩
  · exact Or.inr ⟨ha, harg, RunU.post_iff.mp hx⟩

end Bbu.Unit
