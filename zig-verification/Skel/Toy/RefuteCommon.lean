import Skel.Types
import Skel.Source

/-! The parts of the refute glue that do not depend on the function (`docs/one-way-lift-skeleton-plan-20261118.md`,
5.3): the end of a refute file, the choice of the file for an obligation and a candidate, and the file of a stored
counterexample. The refute file of one function is a `RefuteSpec` (`docs/one-way-lift-g3-plan-20261118.md`, 5.7): its
parts that differ between the functions, and `RefuteSpec.files`, which gives the texts from them. All functions are
pure. -/

namespace Skel.Toy.RefuteCommon

open Skel

/-- The end of a refute file: the verdict line, or the guard of a stored counterexample. -/
inductive Ending where
  /-- `#eval` of the verdict line of `samples` samples from the seed `seed`. -/
  | print (seed samples : Nat)
  /-- `#guard` that the sample `index` of `seed` still fails. -/
  | guard (seed index : Nat)

/-- The end of the loop part of a refute file. `shown` is the name of the function that shows a sample, `head` the
label of the loop head and `fuel` the fuel of one run. The refute file defines `refuteInv`, `refuteMeasure`,
`refuteResult`, `refuteAdmitted`, `refuteFree` and `refuteRender`; each sample is a ghost with its state (`refuteLoopG`). -/
def loopEndingOn (leaf : String) (shown head : String) (fuel : Nat) : Ending → String
  | .print seed samples =>
    "#eval IO.println ((Skel.Refute.refuteLoopG " ++ leaf ++ " " ++ head ++ " " ++ toString fuel
      ++ " refuteInv refuteMeasure refuteResult refuteAdmitted refuteFree " ++ toString seed ++ " "
      ++ toString samples ++ ").line (" ++ shown ++ " refuteRender refuteAdmitted refuteFree " ++ toString seed ++ "))"
  | .guard seed index =>
    "#guard (match Skel.Refute.sampleAtG? refuteAdmitted refuteFree " ++ toString seed ++ " " ++ toString index
      ++ " with\n  | some (.admitted (g, x) e) => (Skel.Refute.runFailsG " ++ leaf ++ " " ++ head ++ " " ++ toString fuel
      ++ " refuteInv refuteMeasure refuteResult g x e).isSome\n  | some (.free (g, x)) => (Skel.Refute.stepFailsG " ++ leaf ++ " "
      ++ head ++ " " ++ toString fuel ++ " refuteInv refuteMeasure refuteResult g x).isSome\n  | none => false)"

/-- `loopEndingOn` with the blocks `blocksP`: the end of the refute file of a function whose results are compared whole. -/
def loopEnding (shown head : String) (fuel : Nat) : Ending → String :=
  loopEndingOn "blocksP" shown head fuel

/-- The term of the blocks that the loop part of a refute file runs, for the projection `proj` of the results (`RefuteSpec.proj`):
`blocksP` for no projection, else `blocksP` with `proj` applied to each result (`Skel.Refute.projRet`). -/
def leafText (proj : String) : String :=
  if proj.isEmpty then "blocksP" else "(Skel.Refute.projRet blocksP (" ++ proj ++ "))"

/-- The end of the claim part of a refute file. `inputs` is the name of the sampler of the admitted inputs and `shown`
the name of the function that shows a sample. The refute file defines `claimLhs`, `claimRhs` and `claimRender`. -/
def claimEnding (inputs shown : String) : Ending → String
  | .print seed samples =>
    "#eval IO.println ((Skel.Refute.refuteClaim " ++ inputs ++ " claimLhs claimRhs " ++ toString seed ++ " "
      ++ toString samples ++ ").line (" ++ shown ++ " claimRender " ++ inputs ++ " " ++ toString seed ++ "))"
  | .guard seed index =>
    "#guard (match Skel.Refute.InputFn.draw " ++ inputs ++ " (Rng.stream (Rng.ofSeed " ++ toString seed ++ ") " ++ toString index
      ++ ") with\n  | some x => claimLhs x != claimRhs x\n  | none => false)"

/-- The two files of a function: the claim file of the claim `models` (the `refines_l3` row) and the loop file of a
triple (the `loop` row). -/
structure Files where
  claim : Generated → Ending → String
  loop : Generated → Triple → Ending → String

/-- The refute file of one toy function (5.7): the parts in which the functions differ. `RefuteSpec.files` gives the
two files from them; the parts that the functions share are the text of `RefuteSpec.files`. The Lean texts are the
declarations of the file, one string each, in the order of the file. -/
structure RefuteSpec where
  /-- The name of the function: the namespace `Skel.Gen.fn` of the file, and the module `Skel.fn` of its samplers. -/
  fn : String
  /-- The imports of the file: the refuter, the samplers, and the modules of the model text. -/
  imports : List String
  /-- The names that follow `open` in the file. -/
  opens : String
  /-- The declarations of the fixture that the model text holds, in order (`RefuteSpec.modelText`). -/
  modelNames : List String
  /-- The label of the loop head, without `Lbl.`. -/
  loopLabel : String
  /-- The fuel of one run from the loop head to the next visit, and of a whole run. -/
  fuel : Nat
  /-- The declarations between the prelude and the slots: the helpers that read the state. -/
  helpers : List String
  /-- The type of the ghost of a sample (`g : ghostTy`): the logical values that are fixed at the entry of a run and
  that the state does not hold. `Unit` when the state has all of them (D35). The sampler gives a ghost with each state. -/
  (ghostTy : String)
  /-- The state type of the slots (`x : stateTy`), and the result type of `refuteResult`. -/
  (stateTy resultTy : String)
  /-- The `let` lines of each slot, before its body. -/
  lets : List String
  /-- The declarations `refuteAdmitted`, `refuteFree` and `refuteRender`. -/
  (admitted free render : String)
  /-- The declarations of the claim part, between `noRun` and the end of the file. -/
  claimDecls : List String
  /-- A function `R → R` on the results of the blocks (L3-U7), or empty for none. A result narrower than 64 bits is the whole
  register, and the L3 value fixes its low bits only: the function keeps the low bits (`fun (r : UInt64) => r &&& 0xFFFF`). The
  loop part runs the blocks with it (`leafText`) and applies it to the result of a triple, and the sampler applies it to the
  expected result. A function with a result of 64 bits has none. -/
  proj : String := ""
  /-- The L3 text of the statement (`StmtShape.l3Text`): the prompts of the models show it. Empty when it was not read. -/
  l3Text : String := ""
  /-- The runner of the callee of blocks with a call (HARNESS-LOOP2 H5): the name of a declaration of the helpers of type
  `∀ f, X f → Res (Y f)`. The loop part runs `Skel.Refute.inline blocksP runner` (`RefuteSpec.leaf`). Empty: blocks with
  no call. -/
  runner : String := ""

/-- The blocks `blocksP` as a leaf: with the runner of the callee when `r` has one. -/
def RefuteSpec.inlined (r : RefuteSpec) : String :=
  if r.runner.isEmpty then "blocksP" else s!"(Skel.Refute.inline blocksP {r.runner})"

/-- The blocks of the loop part of the refute file of `r` (`leafText`), with the runner of the callee when `r` has one. -/
def RefuteSpec.leaf (r : RefuteSpec) : String :=
  if r.proj.isEmpty then r.inlined else "(Skel.Refute.projRet " ++ r.inlined ++ " (" ++ r.proj ++ "))"

/-- The model text of `r` for the fixture text `src`: the declarations of `r.modelNames`, each in its own block. It has
no `theorem`. -/
def RefuteSpec.modelText (r : RefuteSpec) (src : String) : Except String String := do
  let decls ← r.modelNames.mapM fun n =>
    match declText src n with
    | some t => pure t
    | none => throw s!"no declaration {n}"
  return "\n\n".intercalate decls

/-- The start of a refute file up to the model text: imports, namespace, opens, the model, and the decidable
equality of the labels that `Skel.Refute` needs. -/
private def prelude (r : RefuteSpec) (g : Generated) : String :=
  "\n".intercalate
    (r.imports.map (fun m => s!"import {m}") ++
      [ "namespace Skel.Gen." ++ r.fn, "open " ++ r.opens, g.modelText, "deriving instance DecidableEq for Lbl" ])

/-- The loop part of a refute file: the helpers, the invariant, the measure and the result of the triple `t` as
functions of a state, the samplers, and the end. -/
private def loopFile (r : RefuteSpec) (g : Generated) (t : Triple) : Ending → String := fun e =>
  let slot (name ty body : String) : String :=
    "def " ++ name ++ " (g : " ++ r.ghostTy ++ ") (x : " ++ r.stateTy ++ ") : " ++ ty ++ " :=\n  "
      ++ "\n  ".intercalate (r.lets ++ [body])
  "\n".intercalate
    ([prelude r g] ++ r.helpers ++
      [ slot "refuteInv" "Bool" ("decide (" ++ t.inv ++ ")"),
        slot "refuteMeasure" "Nat" t.measure,
        slot "refuteResult" r.resultTy (if r.proj.isEmpty then t.result else r.proj ++ " (" ++ t.result ++ ")"),
        r.admitted, r.free, r.render,
        loopEndingOn r.leaf "Skel.Refute.shownG" ("Lbl." ++ r.loopLabel) r.fuel e,
        "end Skel.Gen." ++ r.fn, "" ])

/-- The claim part of a refute file: `blocksP` run from `entry` against `run`, on the admitted inputs, and the end. -/
private def claimFile (r : RefuteSpec) (g : Generated) : Ending → String := fun e =>
  "\n".intercalate
    ([prelude r g, "def noRun (f : Empty) : Empty.elim f → Res (Empty.elim f) := f.elim"] ++ r.claimDecls ++
      [claimEnding ("Skel." ++ r.fn ++ ".inputs") "Skel.Refute.shownClaim" e, "end Skel.Gen." ++ r.fn, ""])

/-- The two files of the function of `r`. -/
def RefuteSpec.files (r : RefuteSpec) : Files :=
  { claim := claimFile r, loop := loopFile r }

/-- The refute file of a candidate (5.3), for the seed `seed` and `samples` samples: a `models` obligation with a
proof candidate gives the claim file, a `loop` obligation with a triple candidate gives the triple file. Another
obligation, an unknown id, or another kind of candidate gives `none`. -/
def refuteText (fs : Files) (seed samples : Nat) (g : Generated) (ob : ObId) (c : Candidate) : Option String :=
  match g.obligations.find? (·.id == ob), c with
  | some o, .proof _ _ => if o.claim == .models then some (fs.claim g (.print seed samples)) else none
  | some o, .triple _ t => if o.claim == .loop then some (fs.loop g t (.print seed samples)) else none
  | some _, .ask _ => none
  | none, _ => none

/-- The file of a stored counterexample (5.3): the refute file of the subject of `cex`, with `#guard` that the sample
`cex.index` of `cex.seed` fails, in place of the verdict line. `none` when the obligation has no refute text for the
subject. The file has no errors while the counterexample fails. -/
def replayText (fs : Files) (g : Generated) (cex : Cex) : Option String :=
  match g.obligations.find? (·.id == cex.ob), cex.subject with
  | some o, .claim => if o.claim == .models then some (fs.claim g (.guard cex.seed cex.index)) else none
  | some o, .triple t => if o.claim == .loop then some (fs.loop g t (.guard cex.seed cex.index)) else none
  | none, _ => none

end Skel.Toy.RefuteCommon
