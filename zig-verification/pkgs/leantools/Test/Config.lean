import LeanTools.Workspace
import Test.Harness

open LeanTools Test Lean

namespace Test.Config

def parse (s : String) : Option LeanTools.Config := (Json.parse s >>= fromJson?).toOption

def suite : T Unit := do
  checkEq "empty object gives the defaults" (parse "{}") (some {})
  checkEq "a missing field keeps its default"
    (parse "{\"loogleModule\": \"Kraken\"}") (some { loogleModule := some "Kraken" })
  checkEq "all fields" (parse "{\"loogleModule\": \"M\", \"grepRoots\": [\"a\"], \"maxOpen\": 2}")
    (some { loogleModule := some "M", grepRoots := #["a"], maxOpen := 2 })
  checkEq "a wrong type is an error" (parse "{\"maxOpen\": \"x\"}") none

  checkEq "check limit parses" (parse "{\"maxConcurrentChecks\": 2}")
    (some { maxConcurrentChecks := ⟨2, by decide⟩ })
  for bad in ["0", "-1", "1.5", "\"3\""] do
    checkEq s!"check limit rejects {bad}" (parse ("{\"maxConcurrentChecks\": " ++ bad ++ "}")) none

end Test.Config
