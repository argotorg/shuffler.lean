import Skel.Gen.UpperRel
import Skel.Gen.UpperModel
import Skel.Types

/-! Local regions for functions whose heads do not have one fixed entry state.
Each region stops at every loop head. One invariant, rank, and output map must meet all region conditions.
A rank decrease is checked on every transition, including a transition between different heads. -/

namespace Skel.Gen

/-- Use the region rule for several heads or for a head with carried state. -/
def usesRegions (p : UpperPlan) : Bool :=
  p.heads.length > 1 || p.heads.any (·.generalized)

/-- The entry region and each cut region, with no duplicate entry. -/
def regionLabels (p : UpperPlan) : List String :=
  ("entry" :: p.heads.map (·.name.s)).eraseDups

/-- The selected cuts. The source block executes before a later arrival stops the region. -/
def regionsText (p : UpperPlan) : String :=
  let arms := p.heads.map fun h => s!"  | .{h.name.s} => true"
  "\n".intercalate (["def regionHeads : Lbl → Bool"] ++ arms ++ ["  | _ => false", "",
    s!"def regionStarts : List Lbl := [{", ".intercalate ((regionLabels p).map ("." ++ ·))}]"])

/-- The shared certificate of all regions. The result relation is supplied by the upper row generator. -/
def regionsRow (p : UpperPlan) (sh : StmtShape) (cal : List Callee)
    (result : String → String → String → Except GenError String) : Except GenError Obligation := do
  let fm := sh.form
  let a := freshName sh p "a"
  let y := freshName sh p "y"
  let inv := freshName sh p "inv"
  let rank := freshName sh p "rank"
  let out := freshName sh p "out"
  let args := p.params.map (·.name.s) ++ ["frame"]
  let bs := p.params.map binderText ++ ["(frame : Heap)"] ++ fm.binderTexts ++ [s!"({a} : In2p)", sh.resultBinder y]
  let state := p.stateType
  let res := match p.kind with | .value => "UInt64" | .heap => "Heap" | .both => "(UInt64 × Heap)"
  let callee := if cal.isEmpty then "noCall" else calleeRel cal
  let start := s!"(initP {a})"
  let final ← result a y s!"({out} .entry {start})"
  let body :=
    s!"SimArr {" ".intercalate (args ++ fm.names)} {a} → {sh.returnsText y} →\n" ++
    s!"  ∃ ({inv} : Lbl → {state} → Prop) ({rank} : Lbl → {state} → Nat) ({out} : Lbl → {state} → {res}),\n" ++
    s!"    {inv} .entry {start} ∧\n" ++
    s!"    (∀ l s, {inv} l s → ∃ e, (blocksP.cut regionHeads).Returns {callee} (.block l) s e ∧\n" ++
    s!"      Lift.Sem.CutExit.Progress {inv} {rank} {out} l s e) ∧\n" ++
    s!"    ({final})"
  let statement := if bs.isEmpty then body else "∀ " ++ " ".intercalate bs ++ ", " ++ body
  pure { id := { function := p.fn, name := "regions" }, cls := .refine, origin := .unit,
         statement, deps := [], claim := .loop }

/-- Compose the certificate through the generic cut rule. -/
def regionsL3Proof (p : UpperPlan) (sh : StmtShape) : String :=
  let fm := sh.form
  let args := p.params.map (·.name.s) ++ ["frame"]
  let a := freshName sh p "a"
  let y := freshName sh p "y"
  let inv := freshName sh p "inv"
  let rank := freshName sh p "rank"
  let out := freshName sh p "out"
  let apply := " ".intercalate (["regions"] ++ args ++ fm.names ++ [a, y, "hs", "hy"])
  "\n".intercalate ["by", s!"  intro {" ".intercalate (args ++ fm.modelArgs)}",
    s!"  intro {fm.pat} {a} {y} hs hy",
    s!"  obtain ⟨{inv}, {rank}, {out}, hstart, hsteps, hresult⟩ := {apply}",
    s!"  exact ⟨{out} .entry (initP {a}), blocksP.cut_loop regionHeads _ {inv} {rank} {out} hsteps .entry (initP {a}) hstart, hresult⟩"]

end Skel.Gen
