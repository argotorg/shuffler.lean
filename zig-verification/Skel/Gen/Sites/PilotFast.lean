import Lift.Tactic.Compose
import Lift.Level3.Fast.L1

/-! The site lemmas of the ReleaseFast pilot unit (benchmark level 3; P-FAST): one module for the program, so that the names
`Lift.Level3.Fast.L1.step.compose.*` are made once. Do not import it with `Skel.Gen.Sites.Pilot`, which is the ReleaseSmall
unit (`Lift.Level3.L1`). -/

#lift_site_lemmas Lift.Level3.Fast.L1.step Lift.Level3.Fast.workspaceAlignmentPC Lift.Level3.Fast.pilotEndPC 0x100000 0x100335
