import Skel.Full.Driver
import Skel.TempDir

/-! Semantic capability is available only after a summary closes and its module builds.
The checker and builder are fakes; these checks exercise the production scheduler. -/

namespace FullSummaryTests

open Skel Skel.Gen Skel.Full Skel.Report.Level3

private def generated (name : String) (summary : Bool) : Generated :=
  let lower : ObId := ⟨name, "decompiles_l2"⟩
  let sem : ObId := ⟨name, "call_summary"⟩
  let row (id : ObId) : Obligation :=
    { id, cls := .refine, origin := .unit, statement := "True", deps := [], claim := .none }
  { modelText := "", obligations := [row lower] ++ (if summary then [row sem] else []),
    refuteText := fun _ _ => none,
    det := [(lower, "by trivial")] ++ (if summary then [(sem, "by trivial")] else []) }

private def fixture (name : String) (callees : List String) : Spec :=
  let header : Header := { namespace_ := s!"SummaryFixture.{name}", imports := [], opens := [] }
  let lower := generated name false
  let upper := generated name true
  let input (mods labels : List String) (_ : Option String) : FnInput :=
    let marker := if labels.contains "leaf" then "semantic interface" else "lower interface"
    { short := name, entry := name, instrs := 0, blocks := [], loopHeads := [],
      header := withImports header mods, gen := .ok lower,
      upper := .ok { generated := { upper with modelText := s!"-- {marker}" }, spec := .error (.shape 0 "no sampler") } }
  { label := name, short := name, callees, source := .moved "SummaryFixture.Statement", own := .ok lower, header,
    input := fun mods stop => input mods [] stop, semanticInput := some input }

private def trial (closeSummary buildModule : Bool) : IO (List (String × Bool)) := do
  let seen ← IO.mkRef ([] : List String)
  let dir ← Skel.tempDir "full-summary"
  let check : Measured := fun lf => do
    seen.modify (· ++ [lf.text])
    let accepted := closeSummary || lf.name != "SummaryFixture.leaf.call_summary"
    pure (if accepted then .accepted ["propext"] else .failed ["open summary"], 1, 0)
  let d : Deps :=
    { check, refute := fun _ _ _ => pure (.pass 1, 1),
      build := fun name _ => pure (if buildModule || !name.endsWith ".leaf" then .ok () else .error "module failure"),
      dir, cfg := { gate := .strict, seed := 1, samples := 1, limitMs := 1000 }, procs := 1 }
  let result ← runSpecs d [fixture "leaf" [], fixture "caller" ["leaf"]]
  let leaf := result.find? (·.label == "leaf")
  let caller := result.find? (·.label == "caller")
  let texts ← seen.get
  let has (part : String) : Bool := texts.any fun t => (t.splitOn part).length > 1
  pure [
    (s!"capability {closeSummary}/{buildModule}: matches the checked summary and built module",
      leaf.any fun o => o.semanticSummary == (closeSummary && buildModule)),
    (s!"selection {closeSummary}/{buildModule}: semantic models need both checks",
      has "semantic interface" == (closeSummary && buildModule)),
    (s!"module {closeSummary}/{buildModule}: failure removes the caller module",
      if buildModule then caller.any (·.module.isSome) else caller.any (·.module.isNone)) ]

def copyChecks : IO (List (String × Bool)) := do
  let root ← Skel.tempDir "region-map-copy"
  let old := root / "old"
  let dest := root / "new"
  IO.FS.createDirAll (old / "region-maps" / "leaf")
  let source := old / "region-maps" / "leaf" / "map.json"
  let target := dest / "region-maps" / "leaf" / "map.json"
  IO.FS.writeFile source "proposal"
  copyRegionMaps none dest ["leaf"]
  let absent := !(← target.pathExists)
  copyRegionMaps (some old.toString) dest ["leaf", "missing"]
  let copied := (← IO.FS.readFile target) == "proposal"
  IO.FS.writeFile target "current proposal"
  copyRegionMaps (some old.toString) dest ["leaf"]
  let preserved := (← IO.FS.readFile target) == "current proposal"
  copyRegionMaps (some old.toString) old ["leaf"]
  pure [("no resume copies no proposal", absent), ("resume copies a complete proposal file", copied),
    ("resume retains a proposal already in the destination", preserved),
    ("a same-directory resume preserves the source", (← IO.FS.readFile source) == "proposal")]

def checks : IO (List (String × Bool)) := do
  pure ((← trial true true) ++ (← trial false true) ++ (← trial true false) ++ (← copyChecks))

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "fullsummary" then return 0
  let mut failed := 0
  for (name, ok) in (← checks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  fullsummary: {name}"
  return failed

end FullSummaryTests
