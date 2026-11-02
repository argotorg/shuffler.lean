import Lake
open Lake DSL System

package ShufflerKraken where
  version := v!"0.1.0"
  allowNonModules := true
  moreLeanArgs := #["-E", "warning"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require Kraken from git "https://github.com/AeneasVerif/kraken.git" @
  "2fd79ae53504b5db4407de57efa9d4bd4fbc3e2b"

-- Let CMake check source dependencies, then trace the generated proof input.
target bbuAssembly pkg : FilePath := Job.async do
  let root ← IO.FS.realPath (pkg.dir / "..")
  let buildDir := root / "build"
  proc { cmd := "cmake", args := #["-S", root.toString, "-B", buildDir.toString, "-G", "Ninja"] }
    (quiet := true)
  proc { cmd := "cmake", args := #["--build", buildDir.toString, "--target", "shuffler_assembly"] }
    (quiet := true)
  let assembly := buildDir / "kraken" / "c" / "build_bottom_up.S"
  setTrace (← computeTrace (TextFilePath.mk assembly))
  return assembly

@[default_target] lean_lib BbuKraken where
  extraDepTargets := #[`bbuAssembly]
@[default_target] lean_lib ProofKit
@[default_target] lean_lib ProofKitTest

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
