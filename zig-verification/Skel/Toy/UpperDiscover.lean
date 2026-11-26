import Skel.Toy.Held
import Skel.Toy.MachineDiscover
import Skel.Discover.Upper

/-! The discovery ladder on the loop row of the generated upper chain of `toyFind`, `toyWalk` and `toyFill` (task D11b):
`skel run find|walk|fill --discover`. The site is the loop head of the plan (`Held.planOf`), the pool is the pool of one pass
of the generated `blocksP` from the head with the spec items of the plan and the statement shape (`Upper.specCtxOf`, INV-D4c), the
refute file is the generated refute spec (`Upper.spec`), and the check is the
check file of the loop row with `loopProof` of the triple and the slot lines and unfold names of the plan. The result of the
quads comes from `Upper.discoverResult` (DISC-RESULT): the spec sources, and the template results only with the templates on. -/

namespace Skel.Toy.UpperDiscover

open Skel Skel.Gen Skel.Discover Skel.Toy.Held Skel.Toy.MachineDiscover
open System (FilePath)

/-- The unit of the general entry (`Skel/Discover/Upper.lean`) for the toy `fn`: its upper chain, plan, shape, blocks and
the header of its check files. -/
def unitOf (fn : String) : Except String Upper.FnUnit := do
  let u ← (upperOf fn).mapError causeText
  let pl ← (planOf fn).mapError causeText
  let some sh := shapeOf fn | throw s!"{fn}: no statement shape"
  let bs ← (blocksFrom (upperCode fn).1 (upperSource fn) fn).mapError causeText
  pure { fn, upper := u, plan := pl, shape := sh, blocks := bs, header := upperHeader fn }

/-- The machine of the loop row of `fn`, with the files below `dir`: the machine of the general entry (`Upper.machineFor`) at
the one loop head of the plan. `mutate` changes the model text of the generator (the refute files and the check of the row read
the changed text); a test uses it for a loop that does not follow the spec. -/
def machineOf (cfg : Config) (fn : String) (dir : FilePath) (mutate : String → String := id) : Except String Machine := do
  let un ← unitOf fn
  let head ← headOf (un.plan.heads.map (·.name.s))
  let some s := (Upper.sitesOf un).find? (·.head == head) | throw s!"{fn}: no site at {head}"
  (Upper.machineFor cfg un s dir mutate).mapError (·.text)

/-- The discovery of the loop row of `fn`; the ledger goes to `dir`. -/
def discover (cfg : Config) (fn : String) (dir : FilePath) (limit : Nat := 6) (mutate : String → String := id) :
    IO (Except String (Discover.Ladder.Result × Option Triple)) := do
  match unitOf fn with
  | .error e => pure (.error e)
  | .ok un =>
    match headOf (un.plan.heads.map (·.name.s)) with
    | .error e => pure (.error e)
    | .ok head =>
      let some s := (Upper.sitesOf un).find? (·.head == head) | pure (.error s!"{fn}: no site at {head}")
      pure ((← Upper.discoverResult cfg un s dir limit mutate).map fun rr => (rr.result, rr.triple))

/-- `run find|walk|fill --discover`: the discovery, then the upper run with the discover rung after the templates. The ledger of
the discovery is `discover-<fn>.json` in its directory. A discovery that fails prints its error, and the run goes on with no
discover rung. -/
def runUpperDiscover (cfg : Config) (fn : String) (prove : Option Prove.Cfg := none) : IO UInt32 := do
  let dir : FilePath := ".skel" / "runs" / s!"{← utcStamp}-{fn}-discover"
  match ← discover cfg fn dir with
  | .error e =>
    IO.println s!"discovery: failed: {e}"
    runUpper cfg fn prove
  | .ok (r, found) =>
    let quad := r.ledger.quad.map fun q => (q.inv, q.measure)
    IO.println s!"discovery: {r.ledger.status}, {r.ledger.rounds.length} rounds, quad {repr quad}, ledger {Discover.Ladder.Ledger.path dir r.ledger.fn}"
    runUpper cfg fn prove (discovered := found)

end Skel.Toy.UpperDiscover
