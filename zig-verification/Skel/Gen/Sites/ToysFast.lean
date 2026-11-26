import Lift.Tactic.Compose
import Lift.Toys.Fast.L1

/-! The site lemmas of the ReleaseFast toy unit (`Lift/Toys/Fast/L1.lean`; task AF2-F): one module for the program, so that the
names `Lift.Toys.Fast.L1.step.compose.*` are made once, and each check file of `Skel/Toy/HeldFast.lean` imports them for
`lift_block_split`. The range is `toyCountPC` to `toyEndPC` of the unit. -/

#lift_site_lemmas Lift.Toys.Fast.L1.step Lift.Toys.Fast.toyCountPC Lift.Toys.Fast.toyEndPC 0x100000 0x1002a5
