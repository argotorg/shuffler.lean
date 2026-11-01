import Lake
open Lake DSL

package PermuteKraken where
  version := v!"0.1.0"
  allowNonModules := true
  moreLeanArgs := #["-E", "warning"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require Kraken from git "https://github.com/AeneasVerif/kraken.git" @
  "2fd79ae53504b5db4407de57efa9d4bd4fbc3e2b"

@[default_target] lean_lib PermuteKraken
@[default_target] lean_lib BbuKraken
@[default_target] lean_lib ProofKit
@[default_target] lean_lib ProofKitTest

lean_exe model where
  root := `ModelMain

lean_exe bbu_model where
  root := `BbuModelMain

lean_exe bbu_flat where
  srcDir := "test"
  root := `BbuFlatMain

lean_exe pop_flat where
  srcDir := "test"
  root := `PopFlatMain

lean_exe surplus_flat where
  srcDir := "test"
  root := `SurplusFlatMain

lean_exe lowest_flat where
  srcDir := "test"
  root := `LowestFlatMain

lean_exe plan_flat where
  srcDir := "test"
  root := `PlanFlatMain
