import Lift.Tactic.Compose
import Lift.Shuffler.L1
import Lift.Shuffler.Entry

/-! The site lemmas of the full shuffler unit (SH-C): one module for the program, so that the names
`Lift.Shuffler.L1.step.compose.*` are made once, and each check file of a shuffler function imports them for
`lift_block_split`. The range is `shufflePC` to `shufflerEndPC` (`Lift/Shuffler/Entry.lean`). -/

#lift_site_lemmas Lift.Shuffler.L1.step Lift.Shuffler.shufflePC Lift.Shuffler.shufflerEndPC 0x100000 0x101c36
