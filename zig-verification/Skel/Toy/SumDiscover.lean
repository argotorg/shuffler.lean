import Skel.Driver
import Skel.Toy.Held
import Skel.Toy.MachineDiscover

/-! The discovery ladder on the loop of `toySum` (`Skel/Discover/Ladder.lean`, tasks D11 and D11b), with the effects of
`Skel/Toy/MachineDiscover.lean`. The loop is a machine site: its head is the loop head of the plan of the upper generator
(`Held.planOf`), and its pool is the pool of one pass of the hand `blocksP` from the head (`machinePoolOf`). The refute file is
`SumRefute.spec`, the check is the check file of the loop row with `loopProof` of the triple. The result is the result of the
template rule. -/

namespace Skel.Toy.SumDiscover

open Skel Skel.Discover Skel.Toy.Sum Skel.Toy.MachineDiscover
open System (FilePath)

/-- The head of the loop of `toySum`, from the plan of the generator. -/
def head : Except String String := do
  match Skel.Toy.Held.planOf "toySum" with
  | .error e => throw s!"no plan: {Skel.Toy.Held.causeText e}"
  | .ok pl => headOf (pl.heads.map (·.name.s))

/-- The effects of the loop of `toySum` for the setup `s` of the driver (`Driver.setup` with no discovered triple). The files go
below `dir`. -/
def machine (cfg : Config) (s : Driver.Setup) (ob : Obligation) (dir : FilePath) : Except String Machine := do
  let h ← head
  pure { spec := Skel.Toy.SumRefute.spec, gen := s.env.gen, ob, head := h, result := some template1.result,
         refuteName := fun t => Driver.refuteName ob.id (.triple t),
         check := fun t => do
           let proof := loopProof ob.statement t
           let (o, ms) ← Io.checker dir cfg.gate (Driver.checkFileOf s.env (Ledger.init s.env.gen.obligations) ob proof)
           pure (proof, o, ms),
         dir, seed := cfg.seed, limitMs := cfg.limitMs }

/-- The machine of the loop of `toySum` from the sources. -/
def machineOf (cfg : Config) (src : Sources) (dir : FilePath) : Except String Machine := do
  let s ← Driver.setup { cfg with discover := false } .none src
  let some ob := s.env.gen.obligations.find? (·.claim == .loop) | throw "no loop obligation"
  machine cfg s ob dir

/-- Runs the discovery of the loop of `toySum` from the sources and writes its ledger to `dir`. The result is the ledger and
the triple of the closed quad, if there is one. -/
def discover (cfg : Config) (src : Sources) (dir : FilePath) (limit : Nat := 6) :
    IO (Except String (Ladder.Result × Option Triple)) := do
  match machineOf cfg src dir with
  | .error e => pure (.error e)
  | .ok m => m.discover limit (Discover.Smt.Rung.ofFlag cfg.solver)

end Skel.Toy.SumDiscover
