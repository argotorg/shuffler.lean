import Skel.Discover.Ladder
import Skel.Test.DiscoverLadder
import Skel.Test.DiscoverLinSite

/-! The tests of the linear measures in the ladder (suite `discoverlin`): `lake exe skel-test --only discoverlin`. Each check is
a value that must hold. A check that does not hold prints one `FAIL` line; the suite gives the number of failed checks.

The loop is `twoCount` (`Skel/Test/DiscoverLinSite.lean`): two counters, and no one feature falls at each step. The checks run
the production effects (`Ladder.Fueled`: the traces, the search of a state, the closing of the goals) and the production ladder.
The model of a check is a function of the test that counts its calls. No check makes a paid call. -/

namespace DiscoverLinTests

open Skel.Discover Skel.Discover.Ladder DiscoverSiteTests DiscoverGoalsTests DiscoverCloseTests DiscoverLadderTests
open System (FilePath)

def fA : Feature := .field ["st", "a"]
def fB : Feature := .field ["st", "b"]
def fW : Feature := .field ["st", "w"]

/-- The measure `2 * a + b + 1`: the steps that are left, with the exit. -/
def mLin : Measure := .one (.add (.add (.scale 2 fA) fB) (.const 1))

def twoSampler : Close.Sampler :=
  { stateTy := "DiscoverLinSiteTests.Two",
    draw := "fun g => ⟨(g.natIn 0 5).1, ((g.stream 1).natIn 0 5).1, ((g.stream 2).natIn 0 5).1⟩" }

def twoSite : Option LoopSite := withCaller DiscoverLinSiteTests.twoCountJson "True" (some "2 * st.a + st.b + 1")

def twoFuel : Feature := mLin.first

def twoFueled (site : LoopSite) (dir : FilePath) : Fueled :=
  { site, call := "DiscoverLinSiteTests.twoCount fuel st", imports := ["Skel.Test.DiscoverLinSite"],
    closeCfg := cfgOf dir (sampler := some twoSampler),
    trace := { site, imports := ["Skel.Test.DiscoverLinSite"], opens := [], draw := twoSampler.draw, args := [],
               features := [fA, fB, fW], atoms := [], fuel := 20, seed := 1, runs := 60 },
    dir }

/-- The quad of a reply text: the first of its quads. -/
def quadOfReply (reply : String) : Option Quad :=
  match parseQuads reply with
  | .ok (q :: _) => some q
  | _ => none

/-- The ladder on `twoCount`, with the plain features as measures (the list of `Pool.measures`) and no model: it closes with a
linear measure that the traces give, and no call. -/
def checkLadder : IO (List (String × Bool)) := do
  let some site := twoSite | return [("two counters: the site", false)]
  let dir ← DiscoverCloseTests.newDir "lin-ladder"
  let asks ← IO.mkRef 0
  let model : Nat → String → IO (Except ProposeError (List Quad)) := fun _ _ => do
    asks.modify (· + 1)
    pure (.error .noReply)
  let c := twoFueled site dir
  let r ← Ladder.run (c.env [fA, fB, fW] [] [.one fA, .one fB, .one fW] [] (some twoFuel) (ask := some model))
  pure
    [ ("two counters: closed", r.ledger.status == "closed"),
      ("two counters: the closed measure is 2 * a + b + 1", r.ledger.quad.map (·.measure) == some mLin.text),
      ("two counters: the closed quad is from the traces",
        (r.ledger.rounds.getLast?.map fun x => x.candidates.any (·.source == "dynamic")) == some true),
      ("two counters: no model call", (← asks.get) == 0 && (r.ledger.rounds.all fun x => !x.asked)) ]

/-- The closer on the text of a reply: the measure `2 * st.a + st.b + 1` closes its goals; the wrong measures `st.a + st.b + 1` (it
does not fall when `a` falls), `2 * st.a - st.b + 1` (it rises when `b` falls), and `2 * st.a + st.b` (it is zero at the exit
state, so the zero case is false) do not. -/
def checkCloser : IO (List (String × Bool)) := do
  let some site := twoSite | return [("two counters closer: the site", false)]
  let dir ← DiscoverCloseTests.newDir "lin-close"
  let c := twoFueled site dir
  let reply (m : String) : String := s!"```quad\nmeasure: {m}\nbound: fuel\n```\n"
  let goals (m : String) : IO (Option (List (String × Close.Result))) := do
    match quadOfReply (reply m) with
    | some q => pure (some (← c.close q))
    | none => pure none
  let good ← goals "2 * st.a + st.b + 1"
  let sum ← goals "st.a + st.b + 1"
  let diff ← goals "2 * st.a - st.b + 1"
  let noOne ← goals "2 * st.a + st.b"
  let closed (g : Option (List (String × Close.Result))) : Bool :=
    g.any fun gs => !gs.isEmpty && gs.all fun x => DiscoverLadderTests.isClosed x.2
  pure
    [ ("closer: the reply 2 * st.a + st.b + 1 is read", (quadOfReply (reply "2 * st.a + st.b + 1")).map (·.measure) == some mLin),
      ("closer: the goals of 2 * st.a + st.b + 1 close", closed good),
      ("closer: the wrong measure st.a + st.b + 1 does not close", sum.isSome && !closed sum),
      ("closer: the wrong measure 2 * st.a - st.b + 1 does not close", diff.isSome && !closed diff),
      ("closer: the measure 2 * st.a + st.b does not close", noOne.isSome && !closed noOne) ]

/-- The sum of the failed checks. The suite runs when `only` is none or `discoverlin`. -/
def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "discoverlin" then return 0
  let mut failed := 0
  for (name, ok) in (← checkLadder) ++ (← checkCloser) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  discoverlin: {name}"
  return failed

end DiscoverLinTests
