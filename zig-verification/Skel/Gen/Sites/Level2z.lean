import Lift.Tactic.Compose
import Lift.Level2z.L1

/-! The site lemmas of the level2z unit (benchmark level 2 in Zig, task L2Z-0): one module for the program, so that the names
`Lift.Level2z.L1.step.compose.*` are made once, and each check file of a level2z function imports them for `lift_block_split`. -/

#lift_site_lemmas Lift.Level2z.L1.step Lift.Level2z.l2zAliasPC Lift.Level2z.l2zEndPC 0x100000 0x1003ee
