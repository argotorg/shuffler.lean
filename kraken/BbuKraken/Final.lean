import BbuKraken.Fn.IsSpilled
import BbuKraken.Fn.ShallowestCopy
import BbuKraken.Fn.SwapWith
import BbuKraken.Fn.Push
import BbuKraken.Fn.Dup
import BbuKraken.Fn.Produce
import BbuKraken.Fn.Generate
import BbuKraken.Fn.Finish
import BbuKraken.Fn.Loop
import BbuKraken.Top
import BbuKraken.Link

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
  have hcopy := Program.WP.callSpec_of_triple L.shallowestCopy_decl shallowestCopy_body
  have hpush := Program.WP.callSpec_of_triple L.push_decl push_body
  have hdup := Program.WP.callSpec_of_triple L.dup_decl dup_body
  have hswap := Program.WP.callSpec_of_triple L.swapWith_decl swapWith_body
  have hprod := Program.WP.callSpec_of_triple L.produce_decl
    (produce_body hcopy hspill hpush hdup)
  have hgen := Program.WP.callSpec_of_triple L.generate_decl (generate_body hprod hswap)
  have hfin := Program.WP.callSpec_of_triple L.finish_decl (finish_body hperm)
  have hloop := Program.WP.callSpec_of_triple L.loop_decl
    (loop_body hfin hspill hcopy hgen hswap)
  exact buildBottomUp_body hloop

end Bbu
