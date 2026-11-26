import Skel.Discover.Lang
import Skel.RungFlags

/-! A candidate map for cut regions. Every local check sees the whole map. A candidate closes only after all
regional checks and the composition check pass. Candidate parsing fixes the head set and accepts one Nat rank per head. -/

namespace Skel.Discover.Joint

open Skel

/-- One head's proposed invariant, Nat rank and machine result. -/
structure HeadCandidate where
  inv : List Atom
  rank : Feature
  out : String
  deriving DecidableEq, Repr

/-- A complete map in the required head order. Only `parse` constructs a map. -/
structure CandidateMap where private mk ::
  entries : List (String × HeadCandidate)
  deriving Repr

def CandidateMap.names (m : CandidateMap) : List String := m.entries.map (·.1)

/-- Parse a complete map. Tuple ranks need a bound before they can become a Nat rank, so this interface refuses them. -/
def CandidateMap.parse (heads : List String) (qs : List (String × Quad)) : Except String CandidateMap := do
  if heads.isEmpty then throw "no region heads"
  if heads.eraseDups != heads then throw "duplicate required region head"
  let names := qs.map (·.1)
  if names.eraseDups != names then throw "duplicate candidate head"
  if let some n := names.find? (!heads.contains ·) then throw s!"unknown candidate head {n}"
  let entries ← heads.mapM fun h => do
    let some q := qs.lookup h | throw s!"missing candidate head {h}"
    let rank ← match q.measure with
      | .one f => pure f
      | _ => throw s!"head {h}: the cut rule needs one Nat rank"
    let rankSource := match rank with | .free t => t | _ => rank.text
    unless rankSource.toList.any (!·.isWhitespace) do throw s!"head {h}: blank rank term"
    let some out := q.result | throw s!"head {h}: no output term"
    unless out.toList.any (!·.isWhitespace) do throw s!"head {h}: blank output term"
    pure (h, { inv := q.inv, rank, out : HeadCandidate })
  pure ⟨entries⟩

/-- At most `limit` maps, in choice order. The cap applies during construction. -/
def combinations (limit : Nat) (choices : List (String × List Quad)) : List (List (String × Quad)) :=
  choices.foldl (fun maps (h, qs) => (maps.flatMap fun m => qs.map (fun q => m ++ [(h, q)])).take limit)
    (if limit == 0 then [] else [[]])

/-- The proof text submitted to a checker and its checked result. -/
structure Checked where
  proof : String
  outcome : Outcome
  ms : Nat
  deriving Repr

def Checked.accepted (c : Checked) : Bool := match c.outcome with
  | .accepted _ => true
  | _ => false

/-- The regional checker proves a local pass against the full map. Composition checks the joint certificate. -/
structure Env where
  heads : List String
  regionCheck : CandidateMap → String → IO Checked
  compose : CandidateMap → List (String × Checked) → IO Checked
  procs : Nat := 2

/-- The result of one map. A parse error starts no regional check. -/
structure Attempt where
  map : Except String CandidateMap
  regions : List (String × Checked)
  composition : Option Checked
  deriving Repr

structure Result where
  closed : Option (CandidateMap × Checked)
  attempts : List Attempt
  deriving Repr

/-- Check maps in order, and regions within one map in parallel. A failed region prevents composition. -/
def runMaps (env : Env) (maps : List (List (String × Quad))) : IO Result :=
  go maps []
where
  go : List (List (String × Quad)) → List Attempt → IO Result
  | [], attempts => pure ⟨none, attempts⟩
  | raw :: rest, attempts => do
    match CandidateMap.parse env.heads raw with
    | .error e => go rest (attempts ++ [⟨.error e, [], none⟩])
    | .ok m =>
      let checked ← RungFlags.mapPar env.procs (fun h => do pure (h, ← env.regionCheck m h)) m.names
      if checked.all (·.2.accepted) then
        let composed ← env.compose m checked
        let attempts := attempts ++ [⟨.ok m, checked, some composed⟩]
        if composed.accepted then pure ⟨some (m, composed), attempts⟩ else go rest attempts
      else go rest (attempts ++ [⟨.ok m, checked, none⟩])

end Skel.Discover.Joint
