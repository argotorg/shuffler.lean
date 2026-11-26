import Skel.Discover.Joint

namespace DiscoverJointTests

open Skel Skel.Discover Skel.Discover.Joint

def q (rank : Nat) (out : Option String := some "0") : Quad :=
  { inv := [], measure := .one (.const rank), bound := none, result := out }

def failed {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def heads : List String := ["entry", "outer", "inner"]

def raw : List (String × Quad) := [("inner", q 0), ("entry", q 2), ("outer", q 1)]

def pureChecks : List (String × Bool) :=
  [ ("a map keeps the required head order", (CandidateMap.parse heads raw).toOption.map (·.names) == some heads),
    ("a missing head is refused", failed (CandidateMap.parse heads (raw.drop 1))),
    ("an extra head is refused", failed (CandidateMap.parse heads (raw ++ [("other", q 0)]))),
    ("a duplicate head is refused", failed (CandidateMap.parse heads (raw ++ [("entry", q 0)]))),
    ("duplicate required heads are refused", failed (CandidateMap.parse ["entry", "entry"] [("entry", q 0)])),
    ("an empty head set is refused", failed (CandidateMap.parse [] [])),
    ("a missing output is refused", failed (CandidateMap.parse ["entry"] [("entry", q 0 none)])),
    ("a blank output is refused", failed (CandidateMap.parse ["entry"] [("entry", q 0 (some " \n"))])),
    ("a blank rank is refused", failed (CandidateMap.parse ["entry"] [("entry", { q 0 with measure := .one (.free " \n") })])),
    ("a tuple rank is refused", failed (CandidateMap.parse ["entry"] [("entry", { q 0 with measure := .two (.const 1) (.const 0) })])),
    ("a zero map limit gives no combinations", combinations 0 [("entry", [q 0])] == []),
    ("the map limit bounds combinations", (combinations 3 [("entry", [q 0, q 1]), ("outer", [q 0, q 1])]).length == 3) ]

def accepted (proof : String) : Checked := ⟨proof, .accepted [], 0⟩

def effectChecks : IO (List (String × Bool)) := do
  let composed ← IO.mkRef false
  let base : Env :=
    { heads, procs := 2,
      regionCheck := fun _ head => pure (accepted head),
      compose := fun _ checked => do
        composed.set true
        pure (accepted (" ".intercalate (checked.map (·.1)))) }
  let ok ← runMaps base [raw]
  let allComposed ← composed.get
  composed.set false
  let bad ← runMaps { base with regionCheck := fun _ head => do
      if head == "inner" then pure ⟨"", .failed ["the cross-head rank does not decrease"], 0⟩
      else pure (accepted head) } [raw]
  let badComposed ← composed.get
  let refused ← runMaps base [raw.drop 1]
  let finalBad ← runMaps { base with compose := fun _ _ => pure ⟨"", .gateRefused ["sorryAx"], 0⟩ } [raw]
  pure
    [ ("all regional checks precede composition", ok.closed.isSome && allComposed),
      ("regional results keep the head order", ok.attempts.head?.map (fun a => a.regions.map (·.1)) == some heads),
      ("a failed region prevents composition", bad.closed.isNone && !badComposed),
      ("a partial map cannot close", refused.closed.isNone && refused.attempts.head?.map (·.regions.isEmpty) == some true),
      ("a refused composition cannot close", finalBad.closed.isNone) ]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverjoint" then return 0
  let checks := pureChecks ++ (← effectChecks)
  let failed := checks.filter (!·.2)
  for (name, _) in failed do IO.println s!"FAIL discoverjoint: {name}"
  return failed.length

end DiscoverJointTests
