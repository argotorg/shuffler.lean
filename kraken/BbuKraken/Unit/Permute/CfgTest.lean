module

public import BbuKraken.Unit.Defs
import all BbuKraken.Unit.Defs
public import BbuKraken.Unit.Permute.Cfg
import all BbuKraken.Unit.Permute.Cfg

@[expose] public section

/-! # Tests: `forallBlocks_cases`, `pm_labels`, `pm_block` on `finishAsm` -/

namespace Bbu.Unit.Permute.CfgTest

def labels : List CfgLabel :=
  [.entry, .label "_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE",
    .label ".LB.Emission.permute.0", .label ".LB.Emission.permute.1",
    .label ".LB.Emission.permute.2", .label ".LB.Emission.permute.3",
    .label ".LB.Emission.permute.4", .label ".LB.Emission.permute.5",
    .label ".LB.Emission.permute.6", .label ".LB.Emission.permute.7",
    .label ".LB.Emission.permute.8", .label ".LB.Emission.permute.9",
    .label ".LB.Emission.permute.10", .label ".LB.Emission.permute.11",
    .label ".LB.Emission.permute.12", .label ".LB.Emission.permute.13",
    .label ".LB.Emission.permute.14", .label ".LB.Emission.permute.15",
    .label ".LB.Emission.permute.16", .label ".LB.Emission.permute.17",
    .label ".LB.Emission.permute.18", .label ".LB.Emission.permute.19",
    .label ".LB.Emission.permute.20", .label ".LB.Emission.permute.21",
    .label ".LB.Emission.permute.22", .label ".LB.Emission.permute.23",
    .label ".LB.Emission.permute.24", .label ".LB.Emission.permute.25"]

example : Program.ForallBlocks finishAsm fun blk => blk.label ∈ labels := by
  simp only [labels]
  pm_labels

-- A list without `.LB.Emission.permute.25` fails.
example : True := by
  fail_if_success
    have : Program.ForallBlocks finishAsm fun blk => blk.label ∈ labels.dropLast := by
      simp only [labels, List.dropLast_cons₂, List.dropLast_singleton]
      pm_labels
  trivial

-- The index and the next label of some blocks.
example : Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.0" →
    blk.idx = 2 ∧ blk.next = .label ".LB.Emission.permute.1" := by
  pm_block

example : Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.24" →
    blk.idx = 26 ∧ blk.next = .label ".LB.Emission.permute.25" := by
  pm_block

example : Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.25" →
    blk.idx = 27 ∧ blk.next = .exit := by
  pm_block

-- A false index stays.
example : True := by
  fail_if_success
    have : Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.0" →
        blk.idx = 3 := by
      pm_block
  trivial

-- A label that is not in the program: no goal stays.
example : Program.ForallBlocks finishAsm fun blk =>
    blk.label = .label ".LB.Emission.shallowestCopyPosition.2" → False := by
  pm_block

end Bbu.Unit.Permute.CfgTest
