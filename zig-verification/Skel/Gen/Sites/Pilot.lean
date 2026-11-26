import Lift.Tactic.Compose
import Lift.Level3.L1

/-! The site lemmas of the pilot unit (benchmark level 3; task N11): one module for the program, so that the names
`Lift.Level3.L1.step.compose.*` are made once, and each check file of a pilot function imports them for
`lift_block_split` (N12). Do not import it with `Lift.Tactic.Test.Compose`, which makes the same names. -/

#lift_site_lemmas Lift.Level3.L1.step Lift.Level3.workspaceAlignmentPC Lift.Level3.pilotEndPC 0x100000 0x10022b
