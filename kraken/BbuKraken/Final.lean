import BbuKraken.Top
import BbuKraken.Link
import BbuKraken.Fn.IsSpilled
import BbuKraken.Fn.PositionOf
import BbuKraken.Fn.ShallowestCopy
import BbuKraken.Fn.Add
import BbuKraken.Fn.SwapWith
import BbuKraken.Fn.Produce
import BbuKraken.Fn.Generate
import BbuKraken.Fn.Finish
import BbuKraken.Fn.TakeBound
import BbuKraken.Fn.Urgent
import BbuKraken.Fn.Step

/-!
`build_bottom_up` in a host program that contains `c/build_bottom_up.S` and the
`permute` of `PermuteKraken` returns the result of the model `buildBottomUp`.
The spec of each callee comes from its body proof, from the leaves up.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

theorem buildBottomUp_correct [Host] (L : Linked) :
    letI := L.decls
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ TopPre s ⦄ buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ TopPost s t ∧ (topMod s).Agree s t ⦄ := by
  letI := L.decls
  letI : Embeds State.permuteAsm := ⟨⟨L.j, L.hp⟩⟩
  have hperm := permute_callSpec L.permute_decl
  have hspill := Program.WP.callSpec_of_triple L.isSpilled_decl isSpilled_body
  have hpos := Program.WP.callSpec_of_triple L.positionOf_decl positionOf_body
  have hcopy := Program.WP.callSpec_of_triple L.shallowestCopy_decl shallowestCopy_body
  have hadd := Program.WP.callSpec_of_triple L.add_decl (add_body hpos)
  have hswap := Program.WP.callSpec_of_triple L.swapWith_decl swapWith_body
  have hprod := Program.WP.callSpec_of_triple L.produce_decl (produce_body hcopy hspill hadd hpos)
  have hgen := Program.WP.callSpec_of_triple L.generate_decl (generate_body hprod hswap)
  have hfin := Program.WP.callSpec_of_triple L.finish_decl (finish_body hperm)
  have htake := Program.WP.callSpec_of_triple L.takeBound_decl (takeBound_body hswap)
  have hurg := Program.WP.callSpec_of_triple L.urgent_decl (urgent_body hpos hcopy hspill)
  have hstep := Program.WP.callSpec_of_triple L.step_decl (step_body hurg hgen hpos htake hswap)
  exact buildBottomUp_body hstep hfin

end Bbu
