import BbuKraken.Fn.Loop.Entry
import BbuKraken.Fn.Loop.Exit
import BbuKraken.Fn.Loop.Head
import BbuKraken.Fn.Loop.Urgent
import BbuKraken.Fn.Loop.Branch
import BbuKraken.Fn.Loop.Bound
import BbuKraken.Fn.Loop.Tail

/-!
`buildBottomUp` (`c/bbu/buildBottomUp.S`) refines `loop` (`Model.loop`) from offset `0`.
The invariants and the variant are in `Loop/Defs.lean`; each block of the cfg has its
own lemma in `Loop/`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

-- The labels of the blocks of `loopAsm`.
def labels : List CfgLabel :=
  [.entry, .label "buildBottomUp", .label ".LB65", .label ".LB103", .label ".LB73",
    .label ".LB66", .label ".LB102", .label ".LB74", .label ".LB64", .label ".LB85",
    .label ".LB63", .label ".LB67", .label ".LB104", .label ".LB61", .label ".LB106",
    .label ".LB105", .label ".LB78", .label ".LB80", .label ".LB107", .label ".LB77",
    .label ".LB81", .label ".LB83", .label ".LB90", .label ".LB108", .label ".LB75",
    .label ".LB109", .label ".LB92", .label ".LB62", .label ".LB87", .label ".LB89",
    .label ".LB93", .label ".LB94", .label ".LB95", .label ".LB96"]

-- Each block of `loopAsm` has a label in `labels`.
theorem labels_cover : loopAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  cfg_view as hview
  rw [Program.ForallBlocks, hview]
  simp [Program.forallBlocksFrom, labels]

end Loop

open Loop in
theorem loop_body [Host] [FunDecls]
    (hfin : Spec "permuteDestinations" finishF finishA finishR)
    (hspill : Spec "isSpilled" isSpilledF isSpilledA isSpilledR)
    (hcopy : Spec "shallowestCopyPosition" shallowestCopyF shallowestCopyA shallowestCopyR)
    (hgen : Spec "generate" generateF generateA generateR)
    (hswap : Spec "swapWith" swapWithF swapWithA swapWithR) :
    Body loopAsm loopF loopA loopR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre loopF loopA s := hpre
  refine Program.WP.cfg (LInv s ra) (V s) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl
  · exact entry
  · exact prologue hpre
  · exact lb65 hfin hpre
  · exact lb103 hpre
  · exact lb73 hpre
  · exact lb66 hspill hcopy hpre
  · exact lb102 hpre
  · exact lb74 hpre
  · exact lb64 hpre
  · exact lb85
  · exact lb63 hpre
  · exact lb67 hgen hpre
  · exact lb104 hgen hpre
  · exact lb61 hpre
  · exact lb106
  · exact lb105 hpre
  · exact lb78 hpre
  · exact lb80 hpre
  · exact lb107 hpre
  · exact lb77 hswap hpre
  · exact lb81 hpre
  · exact lb83 hswap hpre
  · exact lb90 hpre
  · exact lb108 hpre
  · exact lb75 hgen hpre
  · exact lb109 hpre
  · exact lb92
  · exact lb62 hpre
  · exact lb87
  · exact lb89
  · exact lb93
  · exact lb94
  · exact lb95
  · exact lb96

end Bbu
