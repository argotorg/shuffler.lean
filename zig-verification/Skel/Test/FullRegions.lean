import Skel.Test.DiscoverRegions
import Skel.Discover.Targets

namespace FullRegionsTests

open Skel Skel.Gen Skel.Discover Skel.Discover.Joint
open DiscoverRegionsTests

/-- The real seven-head permute function keeps a joint row and its composition. No held-out proof is read. -/
def permuteTests : IO (List (String × Bool)) := do
  let dir ← Skel.tempDir "permute-regions"
  let us ← Skel.Discover.Targets.fullUnitsOf dir 180000 ["emissionPermute"]
  let some (_, .ok u) := us.head? | return [(s!"permute generates its joint unit: {us.map (fun (n, r) => (n, r.toOption.isSome))}", false)]
  let g := u.upper.generated
  let some ob := g.obligations.find? (·.id.name == "regions") | return [("permute has a regions row", false)]
  let some refines := g.obligations.find? (·.id.name == "refines_l3") | return [("permute has refines_l3", false)]
  let some proof := g.det.lookup refines.id | return [("permute has a composition proof", false)]
  let some text := GenL2LoopsTests.refinesFile u.header g.modelText ob refines proof
    | return [("permute composition file renders", false)]
  let checked ← GenL2LoopsTests.runFile "permute-regions" text s!"{u.header.namespace_}.refines_l3"
  let found ← Skel.Discover.Upper.discoverFn cfg u dir
  let request := dir / u.fn / "regions" / "regions.request.json"
  pure
    [ ("permute keeps all seven heads", u.plan.heads.length == 7),
      (s!"permute composition checks with its joint row: {repr checked}", GenL2LoopsTests.accepted checked),
      ("permute discovery emits one open joint request", found.length == 1 && found.all (fun s => s.status == "open" && s.row == some "regions") && (← request.pathExists)) ]


def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "permuteregions" then return 0
  let checks ← permuteTests
  let failed := checks.filter (!·.2)
  for (name, _) in failed do IO.println s!"FAIL permuteregions: {name}"
  return failed.length

end FullRegionsTests
