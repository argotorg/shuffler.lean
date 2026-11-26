import Skel.Types
import Skel.Source
import Skel.Toy.Sum
import Skel.Toy.RefuteCommon

/-! The refute glue of `toySum` (`docs/one-way-lift-skeleton-plan-20261118.md`, 5.3; the spec in 5.7). All functions are
pure.

`spec` gives the parts of the refute file of `toySum` that differ from the other toys. `refuteText` gives the text of a
Lean file that prints one verdict line: for the claim of the obligation with claim `models` (row 9, `refines_l3`), and
for a triple candidate of the obligation with claim `loop` (row 8). The file imports `Skel.Lean.Refute` and
`Skel.Lean.Sum`, holds the model text, and passes the constructors of the hand model to the generic refuter.
`replayText` gives the file of a stored counterexample: the same file, with a `#guard` that holds while the
counterexample fails. `handTriple` reads the hand triple of the loop from the text of `Sum.lean`. -/

namespace Skel.Toy.SumRefute

open Skel Skel.Toy.Sum Skel.Toy.RefuteCommon

/-- The parts of the refute file of `toySum` (5.7). The model text of the file is `Generated.modelText`; the names are
those of the hand model text in `Lift/Spike/Sum.lean`, which the sampler reads. -/
def spec : RefuteSpec :=
  { fn := "Sum"
    imports := ["Skel.Lean.Refute", "Skel.Lean.Sum", "Lift.Sem.Sim", "Lift.Sem.Heap", "Lift.Spike.Sites", "Lift.Spike.L1"]
    opens := "Lift.P2.Total Lift.Sem Lift.Spike Coordinator.Dst"
    modelNames := ["In2", "In2p", "Lbl", "St", "init", "blocks", "blocksP", "post", "l2", "l2p", "run", "C", "l3", "Loop",
      "At", "SimIn", "SimArr", "SimSt"]
    loopLabel := "LBB1_1"
    -- The fuel of one run from the loop head to the next visit, and of a whole run: `2 * 6 + 8`, with 6 the greatest
    -- length of an array of the sampler.
    fuel := 20
    helpers := ["def xsOf (a : In2p) : List (BitVec 64) :=\n  match a.heap.find? (fun o => o.addr == a.rdi.toBitVec) with\n"
      ++ "  | some o => o.cells.filterMap (fun c => c.get .W64)\n  | none => []"]
    ghostTy := "Unit"
    stateTy := "St In2p"
    resultTy := "UInt64"
    lets := ["let a := x.input", "let xs := xsOf a"]
    admitted := "def refuteAdmitted (g : Rng) : Unit × St In2p × UInt64 :=\n  let (xs, h, p, n) := Skel.Sum.inputs g\n"
      ++ "  ((), init (⟨h, p, n⟩ : In2p), UInt64.ofBitVec xs.sum)"
    free := "def refuteFree (g : Rng) : Unit × St In2p :=\n  let (_, h, p, n, i, acc) := Skel.Sum.states g\n  ((), ⟨⟨h, p, n⟩, acc, i⟩)"
    render := "def refuteRender (x : St In2p) : String :=\n  \"xs = \" ++ toString (xsOf x.input) ++ \", rcx = \" ++ toString x.rcx ++ \", rax = \" ++ toString x.rax"
    claimDecls :=
      [ "def claimLhs (x : List (BitVec 64) × Heap × UInt64 × UInt64) : Option UInt64 :=\n"
          ++ "  match blocksP.run noRun (2 * x.1.length + 8) Lbl.entry (init (⟨x.2.1, x.2.2.1, x.2.2.2⟩ : In2p)) with\n"
          ++ "  | .ok r => some r\n  | _ => none",
        "def claimRhs (x : List (BitVec 64) × Heap × UInt64 × UInt64) : Option UInt64 :=\n  (run x.1).map UInt64.ofBitVec",
        "def claimRender (x : List (BitVec 64) × Heap × UInt64 × UInt64) : String :=\n"
          ++ "  \"xs = \" ++ toString x.1 ++ \", rdi = \" ++ toString x.2.2.1 ++ \", rsi = \" ++ toString x.2.2.2" ] }

/-- The refute file of a candidate (5.3), for the seed `seed` and `samples` samples: a `models` obligation with a proof
candidate gives the claim file, a `loop` obligation with a triple candidate gives the triple file. Another
obligation, an unknown id, or another kind of candidate gives `none`. -/
def refuteText (seed samples : Nat) (g : Generated) (ob : ObId) (c : Candidate) : Option String :=
  RefuteCommon.refuteText spec.files seed samples g ob c

/-- The file of a stored counterexample (5.3): the refute file of the subject of `cex`, with `#guard` that the sample
`cex.index` of `cex.seed` fails, in place of the verdict line. `none` when the obligation has no refute text for the
subject. The file has no errors while the counterexample fails. -/
def replayText (g : Generated) (cex : Cex) : Option String :=
  RefuteCommon.replayText spec.files g cex

/-- The lines of `Sum.lean` that hold the hand triple of the loop (the `have loop` of `refines_l3`): the statement and
the two functions of `Blocks.Returns.loop`, 1-based and inclusive. -/
def tripleLines : Nat × Nat := (220, 223)

/-- The text of `s` before the first `stop`; `none` when `stop` does not occur. -/
private def before (s stop : String) : Option String :=
  match s.splitOn stop with
  | h :: _ :: _ => some h
  | _ => none

/-- The text of `s` after the one marker `start`; `none` when `start` does not occur exactly once. -/
private def after (s start : String) : Option String :=
  match s.splitOn start with
  | [_, rest] => some rest
  | _ => none

/-- The hand triple of the loop (5.2, item 2), read from `Sum.lean`: the invariant after the frame conjunct
`x.input = a ∧`, the measure and the result, the two `fun x : St In2p =>` of `Blocks.Returns.loop`. -/
def handTriple (src : Sources) : Except String Triple := do
  let some raw := lineRange src.sum tripleLines.1 tripleLines.2 | throw "no triple lines in Sum.lean"
  let s := squash raw
  let some inv := (after s "x.input = a ∧ ").bind (before · " →") | throw "no invariant in the hand loop"
  match s.splitOn "(fun x : St In2p => " with
  | [_, m, r] =>
    let some measure := before m ") " | throw "no measure in the hand loop"
    let some result := before r ") ?_" | throw "no result in the hand loop"
    pure { inv, measure, result }
  | _ => throw "no measure and result in the hand loop"

end Skel.Toy.SumRefute
