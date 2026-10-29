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
  [.entry, .label "buildBottomUp", .label ".LB69", .label ".LB107", .label ".LB65",
    .label ".LB73", .label ".LB70", .label ".LB100", .label ".LB106", .label ".LB77",
    .label ".LB108", .label ".LB109", .label ".LB81", .label ".LB83", .label ".LB82",
    .label ".LB80", .label ".LB84", .label ".LB86", .label ".LB68", .label ".LB88",
    .label ".LB67", .label ".LB71", .label ".LB110", .label ".LB78", .label ".LB111",
    .label ".LB95", .label ".LB66", .label ".LB90", .label ".LB92", .label ".LB94",
    .label ".LB96", .label ".LB97", .label ".LB98", .label ".LB99"]

-- Each block of `loopAsm` has a label in `labels`.
theorem labels_cover : loopAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  cfg_view as hview
  rw [Program.ForallBlocks, hview]
  simp [Program.forallBlocksFrom, labels]

end Loop

open Loop in
theorem loop_body [Host] [FunDecls]
    (hfin : Spec "permuteDestinations" finishF finishA finishR)
    (hpos : Spec "positionOf" positionOfF positionOfA positionOfR)
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
  · exact lb69 hfin hpre
  · exact lb107 hpre
  · exact lb65 hpre
  · exact lb73 hpre
  · exact lb70 hpos hpre
  · exact lb100 hspill hcopy hpre
  · exact lb106 hpre
  · exact lb77 hpos hpre
  · exact lb108 hgen hpre
  · exact lb109 hpre
  · exact lb81 hpre
  · exact lb83 hpre
  · exact lb82 hpre
  · exact lb80 hswap hpre
  · exact lb84 hpre
  · exact lb86 hswap hpre
  · exact lb68 hpre
  · exact lb88 hpre
  · exact lb67 hpre
  · exact lb71 hpos hgen hpre
  · exact lb110 hpre
  · exact lb78 hgen hpre
  · exact lb111 hpre
  · exact lb95
  · exact lb66 hpre
  · exact lb90
  · exact lb92
  · exact lb94
  · exact lb96
  · exact lb97
  · exact lb98
  · exact lb99

end Bbu
