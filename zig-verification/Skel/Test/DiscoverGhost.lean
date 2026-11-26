import Skel.Discover.Smt.Rung
import Skel.Test.DiscoverGhostSite
import Skel.Test.DiscoverSolver
import Skel.Test.DiscoverSmtBack

/-! The tests of the ghost encoding of arrays (`Skel/Discover/Smt/Ts.lean`, `Query.lean`, `Back.lean`; suite `discoverghost`,
task INV-S6): `lake exe skel-test --only discoverghost`. Each check is a value that must hold. A check that does not hold
prints one `FAIL` line; the suite gives the number of failed checks.

The answers of z3 are in the cache `Skel/Test/data/discoverghost/`, read with no solver (the solver commands are paths that do
not exist). To fill or refresh the cache, remove the files and run the suite with `DISCOVERGHOST_FILL=1` in the dev shell.

The sites are in `Skel/Test/DiscoverGhostSite.lean`. For each, the production `Rung.propose` gives the proposal, and the goals
of its quad close by the tactics of D9 (`Close.closeGoals`). -/

namespace DiscoverGhostTests

open Skel Skel.Discover Skel.Discover.Smt DiscoverGoalsTests DiscoverCloseTests

def cacheDir : String := "Skel/Test/data/discoverghost"
def siteImport : String := "Skel.Test.DiscoverGhostSite"

/-! ## The sites -/

def fillJson : String := site_json% DiscoverGhostSites.fill
def swapJson : String := site_json% DiscoverGhostSites.swap
def selJson : String := site_json% DiscoverGhostSites.selPass
def copyJson : String := site_json% DiscoverGhostSites.copy
def badJson : String := site_json% DiscoverGhostSites.swapBad

def fillSite : Option LoopSite := withCaller fillJson "st.2 = 0" (some "16 - st.2 + 1")
def swapSite : Option LoopSite := withCaller swapJson "st.2.1 = 0 ∧ st.2.2 = 7" (some "st.2.2 - st.2.1 + 1")
def selSite : Option LoopSite := withCaller selJson "True" (some "8 - st.2.2 + 1")
def copySite : Option LoopSite := withCaller copyJson "st.2.2 = 0" (some "8 - st.2.2 + 1")
def badSite : Option LoopSite := withCaller badJson "st.2.1 = 0 ∧ st.2.2 = 7" (some "st.2.2 - st.2.1 + 1")

def callOf (fn : String) : String := s!"DiscoverGhostSites.{fn} fuel st"

/-! ## The configuration -/

def fill : IO Bool := do pure (← IO.getEnv "DISCOVERGHOST_FILL").isSome

def cfgOf (log : IO.Ref (List String)) : IO Rung.Cfg := do
  let solver : Smt.Config :=
    if (← fill) then { cache := some cacheDir }
    else { z3 := "/nonexistent/z3", cvc5 := "/nonexistent/cvc5", cache := some cacheDir }
  pure { solver, imports := [siteImport], log := fun s => log.modify (· ++ [s]) }

def fuelQuads (p : Rung.Proposal) : List Quad := p.quads.filter (·.fuelIndexed)

/-- Whether the three goals of the quad close. -/
def closes (tag : String) (site : LoopSite) (q : Quad) (call : String) : IO Bool := do
  let dir ← DiscoverCloseTests.newDir s!"ghost-{tag}"
  match fueledGoals site q call [siteImport] [] with
  | .error _ => pure false
  | .ok g =>
    let rs ← Close.closeGoals { dir, sampler := none } g
    pure (rs.length == 3 && rs.all fun (_, r) => isClosed (some r))

/-- An atom with a quantifier over a ghost index: a D1 element atom, or a solver term with `∀`. -/
partial def quantified : Atom → Bool
  | .forallBelow .. => true
  | .smt t => has t.text "∀"
  | _ => false

def isPerm : Atom → Bool
  | .permSlice .. => true
  | _ => false

/-- One site: the proposal has one quad of the fuel-indexed form with an atom of `kind`, from the cache, and its goals
close. -/
def siteChecks (tag : String) (site : Option LoopSite) (fn : String) (kind : Atom → Bool) (what : String) :
    IO (List (String × Bool)) := do
  let log ← IO.mkRef []
  let fillMode ← fill
  let some s := site | return [(s!"{tag}: the site", false)]
  let p ← Rung.propose (← cfgOf log) s
  let q? := (fuelQuads p).head?
  let ok ← match q? with
    | some q => closes tag s q (callOf fn)
    | none => pure false
  pure
    [ (s!"{tag}: one quad of the fuel-indexed form (notes: {p.notes})", (fuelQuads p).length == 1),
      (s!"{tag}: the quad has {what}", (q?.map fun q => q.inv.any kind) == some true),
      (s!"{tag}: the Spacer queries are answered by the cache (by the solver in the fill mode)",
        p.runs.length == 2 && p.runs.all fun r => (r.cached || fillMode) && r.result matches .solved _),
      (s!"{tag}: its three goals close", ok) ]

/-- The mutant: Spacer refutes the permutation (unsat), so there is no quad, and a note says so. -/
def mutantChecks : IO (List (String × Bool)) := do
  let log ← IO.mkRef []
  let some s := badSite | return [("mutant: the site", false)]
  let p ← Rung.propose (← cfgOf log) s
  let anyCloses ← p.quads.anyM fun q => closes "bad" s q (callOf "swapBad")
  pure
    [ ("mutant: the fuel query is sat and the ghost query is unsat",
        (p.runs.map fun r => r.result matches .infeasible) == [false, true]),
      ("mutant: no quad", p.quads.isEmpty),
      ("mutant: a note names the refuted ghost property", p.notes.any fun n => has n "unsat" && has n "perm"),
      ("mutant: no quad closes", !anyCloses) ]

/-! ## The rules, and the parse of `ite` and of array sizes -/

open Lift.Smt in
def fillSys : Except SolverError Sys := sys% DiscoverGhostSites.fill
def swapSys : Except SolverError Sys := sys% DiscoverGhostSites.swap
def selSys : Except SolverError Sys := sys% DiscoverGhostSites.selPass
def copySys : Except SolverError Sys := sys% DiscoverGhostSites.copy
def badSys : Except SolverError Sys := sys% DiscoverGhostSites.swapBad

def ghostsOf (s : Except SolverError Sys) : Option (List Ghost) := s.toOption.map (·.ghosts)

open Lift.Smt in
def v (n : String) : Tm := .var n

open Lift.Smt in
def sel (a i : String) : Tm := .app "select" [v a, v i]

def kSlots : List Slot := [.int (.nat (fld ["k"]))]
def readK (body : String) : Except BackError BTerm := readBool kSlots (DiscoverSmtBackTests.def1 ["x!0"] body)
def kI : ITerm := .nat (fld ["k"])

def isIll {α : Type} : Except BackError α → Bool
  | .error (.illFormed _) => true
  | _ => false

open Lift.Smt in
def pureChecks : List (String × Bool) :=
  [ ("rule index: fill stores 0 at snd and increments snd", ghostsOf fillSys == some [.index "fst" "snd" (.num 0)]),
    ("rule index: copy stores a[i] at i of b", ghostsOf copySys == some [.index "snd_fst" "snd_snd" (sel "fst" "snd_snd")]),
    ("rule perm: swap, the selection pass and the mutant move elements of fst",
      ghostsOf swapSys == some [.perm ["fst"]] && ghostsOf selSys == some [.perm ["fst"]] && ghostsOf badSys == some [.perm ["fst"]]),
    ("no rule: the vector loop stores a value that reads the vector itself, so it has no ghost",
      ghostsOf DiscoverSmtTests.vecLoopSys == some []),
    ("no rule: a site with no array has no ghost", ghostsOf DiscoverSmtTests.countDownSys == some []),
    ("trackTo: a swap of i and j moves q from j to i and from i to j",
      trackTo "a" [(v "i", sel "a" "j"), (v "j", sel "a" "i")] (v "q") ==
        Tm.ite (Tm.eq (v "q") (v "j")) (v "i") (Tm.ite (Tm.eq (v "q") (v "i")) (v "j") (v "q"))),
    ("trackTo: a store of a new value at i after the swap removes the move to i",
      trackTo "a" [(v "i", sel "a" "j"), (v "j", sel "a" "i"), (v "i", .num 0)] (v "q") ==
        Tm.ite (Tm.eq (v "q") (v "i")) (v "j") (v "q")),
    ("trackTo: a store of a value of another array is no move", movesOf "a" [(v "i", sel "b" "i")] == []),
    ("ite of Int: a comparison of an ite is a conjunction of the cases",
      readK "(<= (ite (>= x!0 3) x!0 3) 5)" ==
        .ok (.and (.imp (.le (.num 3) kI) (.le kI (.num 5))) (.imp (.not (.le (.num 3) kI)) (.le (.num 3) (.num 5))))),
    ("ite of Int: a sum with an ite has the cases of the ite",
      readK "(= (+ (ite (> x!0 0) 1 0) x!0) 2)" ==
        .ok (.and (.imp (.lt (.num 0) kI) (.eq (.add (.num 1) kI) (.num 2)))
          (.imp (.not (.lt (.num 0) kI)) (.eq (.add (.num 0) kI) (.num 2))))),
    ("ite of Int: an ite of Int at the top of an integer answer is ill-formed",
      isIll (readInt kSlots { DiscoverSmtBackTests.def1 ["x!0"] "(ite (> x!0 0) 1 0)" with sort := .atom "Int" })),
    ("ite of Int: an ite in a place that is not an integer is ill-formed", isIll (readK "(and (ite (> x!0 0) 1 0))")),
    ("array size: the size of an Array is the length of its list",
      match DiscoverSmtTests.arrLoopSys with
      | .ok s => s.slot "fst_size" == .ok (.int (.nat (.len ["st", "fst", "toList"])))
      | .error _ => false) ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoverghost`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverghost" then return 0
  let _ := (seed, cases)
  let checks := pureChecks ++
    (← siteChecks "fill" fillSite "fill" quantified "a ∀ atom over the ghost index") ++
    (← siteChecks "swap" swapSite "swap" isPerm "a permSlice atom") ++
    (← siteChecks "selection pass" selSite "selPass" isPerm "a permSlice atom") ++
    (← siteChecks "copy" copySite "copy" quantified "a ∀ atom over the ghost index") ++
    (← mutantChecks)
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverghost: {name}"
  return failed

end DiscoverGhostTests
