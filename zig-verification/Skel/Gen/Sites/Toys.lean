import Lift.Tactic.Compose
import Lift.Toys.L1

/-! The site lemmas of the toy unit (task N11): one module for the program, so that the names
`Lift.Toys.L1.step.compose.*` are made once, and each check file of a toy imports them for `lift_block_split` (N12). -/

#lift_site_lemmas Lift.Toys.L1.step Lift.Toys.toyCountPC Lift.Toys.toyEndPC 0x100000 0x100115
