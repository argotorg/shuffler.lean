import Lake
open Lake DSL System

/-! A Lean lakefile, not TOML, for the C shim of `LeanTools.Http` (`c/http.c`, linked with
libcurl). The nix package reads the loogle pin from lake-manifest.json. -/

package leantools where
  version := v!"0.1.0"
  testDriver := "tests"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
  moreLinkArgs := #["-lcurl"]

/-- The loogle binary that `lean_loogle` runs, built with this toolchain:
`lake build @loogle/loogle`. -/
require loogle from "../../vendor/loogle"

target http.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "http.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "http.c"
  buildO oFile srcJob #["-I", (← getLeanIncludeDir).toString, "-fPIC"] #["-O2", "-Wall", "-Werror"] "cc"

extern_lib libleantoolshttp pkg := do
  let o ← fetch <| pkg.target ``http.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leantoolshttp") #[o]

lean_lib LeanTools

lean_lib Test where
  globs := #[`Test.Harness, `Test.HoleFeedback, `Test.Text, `Test.History, `Test.Pos, `Test.Validate, `Test.Config,
    `Test.Http, `Test.Chat, `Test.OpenAI, `Test.Responses, `Test.Anthropic, `Test.Prove, `Test.ProveBudget, `Test.ProveConfig, `Test.Tools, `Test.Deny, `Test.Report,
    `Test.RunMetadata, `Test.Axioms, `Test.AxiomsLemma, `Test.Ask].map .one

@[default_target]
lean_exe leantools where
  root := `Main
  supportInterpreter := true

lean_exe tests where
  root := `Test
  supportInterpreter := true

lean_exe integration where
  root := `Test.Integration
  supportInterpreter := true
