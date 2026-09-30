import Experiments.BuildBottomUp.Verified

open Lean Elab Command in
elab "check_no_legacy_imports" : command => do
  for name in (← getEnv).header.moduleNames do
    if (`Shuffler.BuildBottomUp).isPrefixOf name then
      throwError "checked proofs import legacy module {name}"

check_no_legacy_imports
