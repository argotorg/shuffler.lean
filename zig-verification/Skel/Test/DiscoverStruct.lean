import Skel.Discover.Smt.Rung
import Skel.Test.DiscoverStructSite
import Skel.Test.DiscoverGhost

/-! The tests of vectors of structures in the solver source (`Skel/Discover/Smt/Ts.lean`, `Query.lean`, `Back.lean`; suite
`discoverstruct`, task SOLV-STRUCT): `lake exe skel-test --only discoverstruct`. Each check is a value that must hold. A check
that does not hold prints one `FAIL` line; the suite gives the number of failed checks.

A vector of structures is one SMT array for each field (a structure of arrays). The answers of z3 are in the cache
`Skel/Test/data/discoverstruct/`, read with no solver. To fill or refresh the cache, remove the files and run the suite with
`DISCOVERSTRUCT_FILL=1` in the dev shell. The live check runs z3 with no cache, and is skipped when z3 is not on the path.

The sites are in `Skel/Test/DiscoverStructSite.lean`. For each, the production `Rung.propose` gives the proposal, and the goals
of its quad close by the tactics of D9 (`Close.closeGoals`). No check makes a model call. -/

namespace DiscoverStructTests

open Skel Skel.Discover Skel.Discover.Smt DiscoverGoalsTests DiscoverCloseTests

def cacheDir : String := "Skel/Test/data/discoverstruct"
def siteImport : String := "Skel.Test.DiscoverStructSite"

/-! ## The sites -/

def sumJson : String := site_json% DiscoverStructSites.sumFst
def flagsJson : String := site_json% DiscoverStructSites.setFlags
def clearJson : String := site_json% DiscoverStructSites.clearFlags
def swapJson : String := site_json% DiscoverStructSites.swapPairs
def badJson : String := site_json% DiscoverStructSites.swapPairsBad

def sumSite : Option LoopSite := withCaller sumJson "st.2.1 = 0" (some "8 - st.2.1 + 1")
def flagsSite : Option LoopSite := withCaller flagsJson "st.2 = 0" (some "8 - st.2 + 1")
def clearSite : Option LoopSite := withCaller clearJson "st.2 = 0" (some "8 - st.2 + 1")
def swapSite : Option LoopSite := withCaller swapJson "st.2.1 = 0 ∧ st.2.2 = 7" (some "st.2.2 - st.2.1 + 1")
def badSite : Option LoopSite := withCaller badJson "st.2.1 = 0 ∧ st.2.2 = 7" (some "st.2.2 - st.2.1 + 1")

def callOf (fn : String) : String := s!"DiscoverStructSites.{fn} fuel st"

/-! ## The configuration -/

def fill : IO Bool := do pure (← IO.getEnv "DISCOVERSTRUCT_FILL").isSome

def cfgOf (log : IO.Ref (List String)) : IO Rung.Cfg := do
  let solver : Smt.Config :=
    if (← fill) then { cache := some cacheDir }
    else { z3 := "/nonexistent/z3", cvc5 := "/nonexistent/cvc5", cache := some cacheDir }
  pure { solver, imports := [siteImport], log := fun s => log.modify (· ++ [s]) }

def fuelQuads (p : Rung.Proposal) : List Quad := p.quads.filter (·.fuelIndexed)

/-- Whether the three goals of the quad close at the site. -/
def closes (tag : String) (site : LoopSite) (q : Quad) (call : String) : IO Bool := do
  let dir ← DiscoverCloseTests.newDir s!"struct-{tag}"
  match fueledGoals site q call [siteImport] [] with
  | .error _ => pure false
  | .ok g =>
    let rs ← Close.closeGoals { dir, sampler := none } g
    pure (rs.length == 3 && rs.all fun (_, r) => isClosed (some r))

/-- The text of the invariant of a quad. -/
def invText (q : Quad) : String := " ∧ ".intercalate (q.inv.map Atom.text)

/-- One site: the proposal has one quad of the fuel-indexed form whose invariant text has `part`, from the cache, and its goals
close. -/
def siteChecks (tag : String) (site : Option LoopSite) (fn part : String) (ghost : Bool) : IO (List (String × Bool)) := do
  let log ← IO.mkRef []
  let fillMode ← fill
  let some s := site | return [(s!"{tag}: the site", false)]
  let p ← Rung.propose (← cfgOf log) s
  let q? := (fuelQuads p).head?
  let ok ← match q? with
    | some q => closes tag s q (callOf fn)
    | none => pure false
  let spacer := p.runs.filter (·.solver == "z3")
  pure
    [ (s!"{tag}: one quad of the fuel-indexed form (notes: {p.notes})", (fuelQuads p).length == 1),
      (s!"{tag}: the invariant has {part} ({q?.map invText})", (q?.map fun q => has (invText q) part) == some true),
      (s!"{tag}: the Spacer queries are answered by the cache (by the solver in the fill mode)",
        spacer.length == (if ghost then 2 else 1) && spacer.all fun r => (r.cached || fillMode) && r.result matches .solved _),
      (s!"{tag}: its three goals close", ok) ]

/-- The negative controls. The swap mutant: Spacer refutes the permutation (unsat), so there is no quad. The quad of `setFlags`
claimed for `clearFlags`: its goals do not close. -/
def mutantChecks : IO (List (String × Bool)) := do
  let log ← IO.mkRef []
  let some bad := badSite | return [("mutant: the site", false)]
  let p ← Rung.propose (← cfgOf log) bad
  let anyCloses ← p.quads.anyM fun q => closes "bad" bad q (callOf "swapPairsBad")
  let some fl := flagsSite | return [("mutant: the flags site", false)]
  let some cl := clearSite | return [("mutant: the clear site", false)]
  let pf ← Rung.propose (← cfgOf (← IO.mkRef [])) fl
  let wrong ← match (fuelQuads pf).head? with
    | some q => do pure (some (← closes "clear" cl q (callOf "clearFlags")))
    | none => pure none
  pure
    [ ("mutant: the fuel query is sat and the ghost query is unsat",
        (p.runs.map fun r => r.result matches .infeasible) == [false, true]),
      ("mutant: no quad", p.quads.isEmpty),
      ("mutant: a note names the refuted ghost property", p.notes.any fun n => has n "unsat" && has n "perm"),
      ("mutant: no quad closes", !anyCloses),
      ("claimed: the quad of setFlags does not close for clearFlags", wrong == some false) ]

/-- The live run of z3 on `setFlags`, with no cache; skipped when z3 is not on the path. -/
def liveChecks : IO (List (String × Bool)) := do
  match ← probeVersion "z3" with
  | none => pure [("live: z3 is not on the path, the check is skipped", true)]
  | some v =>
    let some s := flagsSite | return [("live: the site", false)]
    let cfg : Rung.Cfg := { solver := { cache := none, cvc5 := "/nonexistent/cvc5" }, imports := [siteImport] }
    let p ← Rung.propose cfg s
    pure
      [ (s!"live ({v}): Spacer gives a quad of the fuel-indexed form (notes: {p.notes})", (fuelQuads p).length == 1),
        ("live: no run is from a cache", p.runs.all (!·.cached)),
        ("live: the goals of the quad close", ← match (fuelQuads p).head? with
          | some q => closes "live" s q (callOf "setFlags")
          | none => pure false) ]

/-! ## The fragment, the rules and the way back -/

def sumSys : Except SolverError Sys := sys% DiscoverStructSites.sumFst
def flagsSys : Except SolverError Sys := sys% DiscoverStructSites.setFlags
def swapSys : Except SolverError Sys := sys% DiscoverStructSites.swapPairs
def badSys : Except SolverError Sys := sys% DiscoverStructSites.swapPairsBad
def nestedSys : Except SolverError Sys := sys% DiscoverStructSites.nested
def pushSys : Except SolverError Sys := sys% DiscoverStructSites.pushCells
def strSys : Except SolverError Sys := sys% DiscoverStructSites.strPairs

def isOk (s : Except SolverError Sys) : Bool := s matches .ok _

def errText (s : Except SolverError Sys) : String :=
  match s with
  | .error (.outOfFragment w) => w
  | _ => ""

def ghostNames (s : Except SolverError Sys) : Option (List String) := s.toOption.map (·.ghosts.map (·.name))

def stateNames (s : Except SolverError Sys) : List String := (s.toOption.map (·.state.map (·.name))).getD []

/-- The variables that a path of `s` changes. -/
def changed (s : Except SolverError Sys) : List String := (s.toOption.map (·.changed)).getD []

/-- The proposition of the answer `(define-fun inv ((x!0 Int)) Bool body)` over the slot of the variable `n` of `s` and the
bound name `g`. -/
def readOver (s : Except SolverError Sys) (n body : String) : Except BackError BTerm := do
  let .ok sys := s | throw (.noRead "no system")
  let slots ← slotsOf sys [n, "g"] ["g"]
  readBool slots (DiscoverSmtBackTests.def1 ["x!0", "x!1"] body)

/-- The answer read back, as an `Atom.smt` text, parses back to the same atom, and its SMT text over the same slots reads back
to the same term. -/
def roundTrip (s : Except SolverError Sys) (n body : String) : Bool :=
  match s, readOver s n body with
  | .ok sys, .ok t =>
    let named : Option (List (String × Slot)) := do
      let ss ← (slotsOf sys [n, "g"] ["g"]).toOption
      pure (["x!0", "x!1"].zip ss)
    let smt := named.bind fun ns => t.smt ns
    parseAtom (Atom.smt t).text == some (.smt t) &&
      (smt.map fun b => readOver s n b == .ok t) == some true
  | _, _ => false

/-- A system with one array of `el` at `st.b`. -/
def oneArray (el : Scalar) (src : Src) : Sys :=
  { state := [{ name := "b", kind := .array el (.num 4) }], params := [], havoc := [], paths := [], exits := [],
    srcs := [("b", src)] }

def slotChecks : List (String × Bool) :=
  [ ("slot: a vector of Bool reads toNat", (oneArray .bool (.field ["st", "b"])).slot "b" == .ok (.vec ["st", "b"] ["toNat"])),
    ("slot: a vector of Fin reads val", (oneArray (.fin 3) (.field ["st", "b"])).slot "b" == .ok (.vec ["st", "b"] ["val"])),
    ("slot: a word field of the elements", (oneArray (.bv 64) (.elem ["st", "b"] ["w"])).slot "b" ==
      .ok (.vec ["st", "b"] ["w", "toNat"])),
    ("slot: a vector of Int has no read", (oneArray .int (.field ["st", "b"])).slot "b" == .error (.noRead "b")),
    ("slot: an Int field of the elements has no read", (oneArray .int (.elem ["st", "b"] ["z"])).slot "b" == .error (.noRead "b")) ]

def pureChecks : List (String × Bool) := slotChecks ++
  [ ("fragment: each site with a vector or an array of structures has a system",
      [sumSys, flagsSys, swapSys, badSys, nestedSys, pushSys].all isOk),
    ("fragment: the old error \"a vector of\" is gone", !(has (errText sumSys) "a vector of")),
    ("fragment: a field outside the fragment is named (String)", has (errText strSys) "String"),
    ("layout: one array for each field of Cell, and the index",
      stateNames flagsSys == ["fst_w", "fst_n", "fst_flag", "snd"]),
    ("layout: a nested structure gives one array for each scalar leaf",
      stateNames nestedSys == ["fst_fst", "fst_snd_w", "fst_snd_n", "fst_snd_flag", "snd"]),
    ("layout: an Array of structures has one size", stateNames pushSys == ["fst_size", "fst_w", "fst_n", "fst_flag", "snd"]),
    ("store: the fields that the step does not change are not changed", changed flagsSys == ["fst_flag", "snd"]),
    ("rule index: setFlags stores 1 at snd of the flag array", ghostNames flagsSys == some ["∀ g < snd, fst_flag[g] = 1"]),
    ("rule perm: the swap moves the elements of both field arrays together",
      ghostNames swapSys == some ["perm fst_fst fst_snd"] && ghostNames badSys == some ["perm fst_fst fst_snd"]),
    ("rule: the sum reads a field and stores nothing, so it has no ghost", ghostNames sumSys == some []),
    ("back: a select of a field array reads the field of the element",
      ((readOver flagsSys "fst_flag" "(= (select x!0 x!1) 1)").map BTerm.text) ==
        .ok "((↑((st.fst[((↑g : Int) : Int).toNat]!).flag.toNat) : Int) = (1 : Int))"),
    ("back: a select of a Nat field", ((readOver flagsSys "fst_n" "(<= (select x!0 x!1) 3)").map BTerm.text) ==
        .ok "((↑((st.fst[((↑g : Int) : Int).toNat]!).n) : Int) ≤ (3 : Int))"),
    ("back: a field of a nested structure", ((readOver nestedSys "fst_snd_w" "(= (select x!0 x!1) 0)").map BTerm.text) ==
        .ok "((↑((st.fst[((↑g : Int) : Int).toNat]!).snd.w.toNat) : Int) = (0 : Int))"),
    ("round trip: Lean text and SMT text of a field read", roundTrip flagsSys "fst_flag" "(= (select x!0 x!1) 1)" &&
      roundTrip nestedSys "fst_snd_w" "(<= (select x!0 (+ x!1 1)) 5)") ]

/-- Gives the number of failed checks. The suite runs when `only` is none or `discoverstruct`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverstruct" then return 0
  let _ := (seed, cases)
  let checks := pureChecks ++
    (← siteChecks "sum" sumSite "sumFst" "st.snd.fst" false) ++
    (← siteChecks "flags" flagsSite "setFlags" ".flag.toNat" true) ++
    (← siteChecks "swap" swapSite "swapPairs" ".Perm st₀.fst.toList" true) ++
    (← mutantChecks) ++ (← liveChecks)
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverstruct: {name}"
  return failed

end DiscoverStructTests
