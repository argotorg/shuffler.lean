module

public import BbuKraken.Unit.Run.Assemble
import all BbuKraken.Unit.Run.Assemble

@[expose] public section

/-! `Emission::run` uses the planned mapping and returns the result of `Flat.emissionRun`.
The initial values of the lowest-height locals are existential, as in `LowestThm`.
`runA` states the concrete trace bounds and mapping conditions required by the callees. -/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit
open Bbu.Sep

theorem run_unit [Host] [FunDecls]
    (hsur : Sep.Spec Names.removeSurplus surplusA 2 surplusQ)
    (hlow : ∀ PM planned, VSpec (RunView PM planned) G.Ok Names.permuteAtLowestHeight
      (lowestA planned) lowestD (lowestQ planned))
    (hav : Sep.Spec Names.isAvailable isAvailableA 3 isAvailableQ)
    (hloop : Sep.Spec Names.buildBottomUp loopA 2068 loopQ) : RunThm runAsm := by
  intro S PM planned g F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  exact Program.wp_mono (fun _ h => h)
    (fun _ ⟨ha, hq, hag⟩ => ⟨ha, RunU.post_iff.mp hq, hag⟩)
    ((RunU.run_vthm PM planned (RunU.frame_spec hsur) (hlow PM planned)
      (RunU.frame_spec hav) (RunU.frame_spec hloop) S g F s ra).1 t
      ⟨ht, RunU.pre_iff.mpr hp⟩)

end Bbu.Unit
