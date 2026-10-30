import BbuKraken.Unit.Defs
import BbuKraken.Unit.Permute.Cfg

/-! # Tests: `forallBlocks_cases`, `pm_labels`, `pm_block` on `finishAsm` -/

namespace Bbu.Unit.Permute.CfgTest

def labels : List CfgLabel :=
  [.entry, .label "_ZN12_GLOBAL__N_18Emission7permuteEv", .label ".LB57", .label ".LB54",
    .label ".LB56", .label ".LB58", .label ".LB61", .label ".LB62", .label ".LB95",
    .label ".LB64", .label ".LB65", .label ".LB66", .label ".LB68", .label ".LB63",
    .label ".LB70", .label ".LB60", .label ".LB71", .label ".LB96", .label ".LB86",
    .label ".LB72", .label ".LB97", .label ".LB74", .label ".LB98", .label ".LB78",
    .label ".LB80", .label ".LB84", .label ".LB73", .label ".LB82", .label ".LB99"]

example : Program.ForallBlocks finishAsm fun blk => blk.label ∈ labels := by
  simp only [labels]
  pm_labels

-- A list without `.LB99` fails.
example : True := by
  fail_if_success
    have : Program.ForallBlocks finishAsm fun blk => blk.label ∈ labels.dropLast := by
      simp only [labels, List.dropLast_cons₂, List.dropLast_singleton]
      pm_labels
  trivial

-- The index and the next label of some blocks.
example : Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB57" →
    blk.idx = 2 ∧ blk.next = .label ".LB54" := by
  pm_block

example : Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB73" →
    blk.idx = 26 ∧ blk.next = .label ".LB82" := by
  pm_block

example : Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB99" →
    blk.idx = 28 ∧ blk.next = .exit := by
  pm_block

-- A false index stays.
example : True := by
  fail_if_success
    have : Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB57" →
        blk.idx = 3 := by
      pm_block
  trivial

-- A label that is not in the program: no goal stays.
example : Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB7" → False := by
  pm_block

end Bbu.Unit.Permute.CfgTest
