import Lift.Tactic.Compose
import Lift.Spike.L1

/-! The site lemmas of the spike unit (`toySum`, `toyJob`; task N11): one module for the program, so that the names
`Lift.Spike.L1.step.compose.*` are made once, and each check file imports them for `lift_block_split` (N12). -/

#lift_site_lemmas Lift.Spike.L1.step Lift.Spike.toyJobPC Lift.Spike.toyEndPC 0x100000 0x100068
