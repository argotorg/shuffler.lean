module

public import BbuKraken.Unit.Run.Lowest
import all BbuKraken.Unit.Run.Lowest
public import BbuKraken.Unit.Run.Available
import all BbuKraken.Unit.Run.Available
public import BbuKraken.Unit.Run.Labels
import all BbuKraken.Unit.Run.Labels
public import BbuKraken.Unit.Run.Checks
import all BbuKraken.Unit.Run.Checks

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit.RunU
open Bbu.Sep

theorem run_vthm [Host] [FunDecls] (PM : Addr) (planned : Vector Word MAX_N)
    (hsur : VSpec (RunView PM planned) G.Ok Names.removeSurplus surplusA 2 surplusQ)
    (hlow : VSpec (RunView PM planned) G.Ok Names.permuteAtLowestHeight
      (lowestA planned) lowestD (lowestQ planned))
    (hav : VSpec (RunView PM planned) G.Ok Names.isAvailable isAvailableA 3 isAvailableQ)
    (hloop : VSpec (RunView PM planned) G.Ok Names.buildBottomUp loopA 2068 loopQ) :
    VThm (RunView PM planned) G.Ok runAsm (runA planned) runD (runQ planned) := by
  intro S g F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  subst ht
  obtain ⟨fr₀, hfr, hk0⟩ := hp.kg ra
  obtain ⟨lo, w, x, y, z, he, hl⟩ := split_frame hfr
  subst fr₀
  refine Program.WP.cfg (Inv S PM planned g F s ra) V ?_ rfl
  refine forallBlocks_cases [.entry, .label Names.run,
    .label ".LB.Emission.run.0", .label ".LB.Emission.run.1",
    .label ".LB.Emission.run.2", .label ".LB.Emission.run.3",
    .label ".LB.Emission.run.4", .label ".LB.Emission.run.5",
    .label ".LB.Emission.run.6", .label ".LB.Emission.run.7",
    .label ".LB.Emission.run.8", .label ".LB.Emission.run.9",
    .label ".LB.Emission.run.10"] (by simp only [Names.run]; cfg_labels) ?_
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry S PM planned g F s ra
  · exact b_fn S PM planned g F s ra hp lo w x y z hl hk0 hsur
  · exact b_0 S PM planned g F s ra
  · exact b_1 S PM planned g F s ra hp.args hlow
  · exact b_2 S PM planned g F s ra
  · exact b_3 S PM planned g F s ra
  · exact b_4 S PM planned g F s ra
  · exact b_5 S PM planned g F s ra
  · exact b_6 S PM planned g F s ra
  · exact b_7 S PM planned g F s ra
  · exact b_8 S PM planned g F s ra hp.args hloop
  · exact b_9 S PM planned g F s ra
  · exact b_10 S PM planned g F s ra hav

end Bbu.Unit.RunU
