import Lift.Sem.Blocks
import Coordinator.Dst.Rng
import Lean.Data.Json

/-! The Lean-side refuter of the walking skeleton (`docs/one-way-lift-skeleton-plan-20261118.md`, section 3).
It runs sampled states through a `Leaf` model and gives `pass`, `real` or `cti`. All functions are pure. -/

namespace Skel.Refute
open Lift.Sem Coordinator.Dst

inductive Stop (σ R : Type) where
  | head (x : σ) | ret (r : R) | fail (why : String)

/-- Runs at least one block from `l`, then until the blocks are at `head` again, return, or fail. -/
def stepTo {L σ R : Type} [DecidableEq L] (b : Leaf L σ R) (head : L) : Nat → L → σ → Stop σ R
  | 0, _, _ => .fail "no fuel"
  | fuel + 1, l, x => match b.step l x with
    | .ok (.goto l' x') => if l' = head then .head x' else stepTo b head fuel l' x'
    | .ok (.ret r) => .ret r
    | .ok (.call f _ _) => f.elim
    | .stuck why => .fail why
    | .noFuel => .fail "no fuel"

/-- The blocks `b` with `proj` applied to each result that they return. A loop with a result narrower than 64 bits returns the
whole register, and the L3 value fixes its low bits only (L3-U7): the refuter runs the blocks `projRet b proj` and compares
`proj` of the results. `proj` is the identity for a result of 64 bits, and the blocks are then `b` itself (the refute files of
such a function do not use `projRet`). A block that calls is a failure, as in `stepTo`: a leaf has no call. -/
def projRet {L σ R : Type} (b : Leaf L σ R) (proj : R → R) : Leaf L σ R :=
  ⟨fun l x => match b.step l x with
    | .ok (.goto l' x') => .ok (.goto l' x')
    | .ok (.ret r) => .ok (.ret (proj r))
    | .ok (.call f _ _) => f.elim
    | .stuck why => .stuck why
    | .noFuel => .noFuel⟩

/-! ## A callee given by a runner (DISC-CALL)

A loop whose body calls a callee runs the blocks `inline b run`: the call of `f` on `a` is a jump to the label and the state of
`k y`, where `y` is the result of the runner `run f a`. The runner of a callee is its L3 spec, not its machine code, so a run
of the loop uses the meaning that the callee rows of the upper chain give to the call. `inline_sound`: a return of the inlined
blocks is a return of `b` with each callee relation that the runner satisfies. `refuteCallee` compares a runner with another
one (the spec runner with the run of the callee's own blocks) on samples. -/

/-- The blocks `b` with each call run by `run`. A runner that is stuck or out of fuel makes the block stuck or out of fuel. -/
def inline {L σ R F : Type} {X Y : F → Type} (b : Blocks L σ R F X Y) (run : ∀ f, X f → Res (Y f)) : Leaf L σ R :=
  ⟨fun l x => match b.step l x with
    | .ok (.goto l' x') => .ok (.goto l' x')
    | .ok (.ret r) => .ok (.ret r)
    | .ok (.call f a k) => match run f a with
      | .ok y => .ok (.goto (k y).1 (k y).2)
      | .stuck why => .stuck why
      | .noFuel => .noFuel
    | .stuck why => .stuck why
    | .noFuel => .noFuel⟩

/-- A return of `inline b run` is a return of `b` when each result of the runner is a result of `callee`. -/
theorem inline_sound {L σ R F : Type} {X Y : F → Type} {b : Blocks L σ R F X Y} {run : ∀ f, X f → Res (Y f)}
    {callee : ∀ f, X f → Y f → Prop} (hc : ∀ f x y, run f x = .ok y → callee f x y) {l : L} {s : σ} {r : R}
    (h : (inline b run).Returns noCall l s r) : b.Returns callee l s r := by
  induction h with
  | ret hs =>
    simp only [inline] at hs
    split at hs
    · cases hs
    · cases hs; exact .ret (by assumption)
    · split at hs <;> cases hs
    · cases hs
    · cases hs
  | goto hs _ ih =>
    simp only [inline] at hs
    split at hs
    · cases hs; exact .goto (by assumption) ih
    · cases hs
    · split at hs
      · cases hs; exact .call (by assumption) (hc _ _ _ (by assumption)) ih
      · cases hs
      · cases hs
    · cases hs
    · cases hs
  | call _ _ _ _ => exact (by assumption : Empty).elim

inductive Sample (σ R : Type) where
  | admitted (x : σ) (expected : R)
  | free (x : σ)

/-- Even index: admitted; odd index: free. Uses `Rng.stream (Rng.ofSeed seed) index`. -/
def sampleAt {σ R : Type} (admitted : Rng → σ × R) (free : Rng → σ) (seed index : Nat) : Sample σ R :=
  let g := Rng.stream (Rng.ofSeed seed) index
  if index % 2 = 0 then
    let (x, expected) := admitted g
    .admitted x expected
  else
    .free (free g)

/-- The step condition of `Blocks.Returns.loop` at `x`; `none` if it holds or `I x` is false. -/
def stepFails {L σ R : Type} [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (I : σ → Bool) (μ : σ → Nat) (out : σ → R) (x : σ) : Option String :=
  if !I x then none else
  match stepTo b head fuel head x with
  | .ret r => if r == out x then none else some "returns a result other than out"
  | .head y =>
    if !I y then some "leaves the invariant"
    else if decide (μ y < μ x) && out y == out x then none
    else some "measure does not decrease or result changes"
  | .fail why => some why

/-- Admitted: `I x`, `out x == expected`, then `stepFails` at each head visit of the run. -/
def runFails {L σ R : Type} [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (I : σ → Bool) (μ : σ → Nat) (out : σ → R) (x : σ) (expected : R) : Option String :=
  if !I x then some "entry: invariant fails"
  else if !(out x == expected) then some "entry: result differs from expected"
  else walk (μ x + 1) x
where
  /-- The visits of the run: `stepFails` holds at each, so the measure drops at each visit.
  The fuel `k` is above the measure of the visit, so `0` is not reached when the checks hold. -/
  walk : Nat → σ → Option String
    | 0, _ => some "measure"
    | k + 1, y => match stepFails b head fuel I μ out y with
      | some w => some w
      | none => match stepTo b head fuel head y with
        | .head z => walk k z
        | _ => none

/-- A sampler of the admitted samples (HARNESS-LOOP2): a total one, `Rng → γ × σ × R`, or one that can find no admitted
input, `Rng → Option (γ × σ × R)`. The second is the sampler of a spec whose admitted inputs are a test on drawn inputs
(the family `objects`): a draw that the test refuses is no entry of a run, so it is no admitted sample. -/
class AdmitFn (α : Type) (γ σ R : outParam Type) where
  admit : α → Rng → Option (γ × σ × R)

instance {γ σ R : Type} : AdmitFn (Rng → γ × σ × R) γ σ R := ⟨fun f g => some (f g)⟩

instance {γ σ R : Type} : AdmitFn (Rng → Option (γ × σ × R)) γ σ R := ⟨id⟩

/-- A free draw can fail admission. No state is checked when it gives `none`. -/
class FreeFn (β : Type) (γ σ : outParam Type) where
  draw : β → Rng → Option (γ × σ)

instance {γ σ : Type} : FreeFn (Rng → γ × σ) γ σ := ⟨fun f g => some (f g)⟩

instance {γ σ : Type} : FreeFn (Rng → Option (γ × σ)) γ σ := ⟨id⟩

/-- A claim input can fail admission. Total samplers retain their existing behavior. -/
class InputFn (α : Type) (input : outParam Type) where
  draw : α → Rng → Option input

instance (priority := low) {input : Type} : InputFn (Rng → input) input := ⟨fun f g => some (f g)⟩

instance {input : Type} : InputFn (Rng → Option input) input := ⟨id⟩

/-- An admitted or free sample, with no invalid fallback when both draws fail. -/
def sampleAtG? {γ σ R α β : Type} [AdmitFn α γ σ R] [FreeFn β γ σ]
    (admitted : α) (free : β) (seed index : Nat) : Option (Sample (γ × σ) R) :=
  let g := Rng.stream (Rng.ofSeed seed) index
  if index % 2 = 0 then
    match AdmitFn.admit admitted g with
    | some (ghost, x, expected) => some (.admitted (ghost, x) expected)
    | none => (FreeFn.draw free g).map Sample.free
  else
    (FreeFn.draw free g).map Sample.free

/-- `sampleAt` with a ghost `γ`: an admitted sample is its ghost, its state and the expected result; a free sample is
its ghost and its state. At an even index with no admitted input (`AdmitFn.admit` gives none) the sample is the free sample of
that index: a free sample is checked by one step, and no entry check runs on a state that no entry reaches. -/
def sampleAtG {γ σ R : Type} {α : Type} [AdmitFn α γ σ R] (admitted : α) (free : Rng → γ × σ) (seed index : Nat) :
    Sample (γ × σ) R :=
  let g := Rng.stream (Rng.ofSeed seed) index
  if index % 2 = 0 then
    match AdmitFn.admit admitted g with
    | some (ghost, x, expected) => .admitted (ghost, x) expected
    | none => .free (free g)
  else
    .free (free g)

/-- A render of a sample (HARNESS-LOOP2): of the state only, `σ → String`, or of the ghost and the state, `γ → σ → String`,
so that a counterexample shows the logical inputs of its run (the ghost) with the registers. -/
class RenderFn (ρ : Type) (γ σ : Type) where
  render : ρ → γ → σ → String

instance {γ σ : Type} : RenderFn (σ → String) γ σ := ⟨fun f _ x => f x⟩

instance {γ σ : Type} : RenderFn (γ → σ → String) γ σ := ⟨id⟩

/-- The state of an admitted draw for a trace (a run from an entry): the admitted input of `g`, else the first one of the
streams `1` to `7` of `g`, else the state of the free sample of `g`. A total sampler gives the state of `g`. -/
def admittedState {γ σ R : Type} {α : Type} [AdmitFn α γ σ R] (admitted : α) (free : Rng → γ × σ) (g : Rng) : σ :=
  match AdmitFn.admit admitted g <|> (List.range 7).findSome? fun i => AdmitFn.admit admitted (g.stream (i + 1)) with
  | some (_, x, _) => x
  | none => (free g).2

/-- An entry draw for a trace, with no state when all admitted and free draws fail. -/
def admittedState? {γ σ R α β : Type} [AdmitFn α γ σ R] [FreeFn β γ σ]
    (admitted : α) (free : β) (g : Rng) : Option σ :=
  match AdmitFn.admit admitted g <|> (List.range 7).findSome? fun i => AdmitFn.admit admitted (g.stream (i + 1)) with
  | some (_, x, _) => some x
  | none => (FreeFn.draw free g).map (·.2)

/-- `stepFails` with a ghost `g`. The ghost is the same at each visit of a run: the step does not change it. -/
def stepFailsG {L σ γ R : Type} [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R) (g : γ) (x : σ) : Option String :=
  if !I g x then none else
  match stepTo b head fuel head x with
  | .ret r => if r == out g x then none else some "returns a result other than out"
  | .head y =>
    if !I g y then some "leaves the invariant"
    else if decide (μ g y < μ g x) && out g y == out g x then none
    else some "measure does not decrease or result changes"
  | .fail why => some why

/-- `runFails` with a ghost `g`, carried with the state to each visit of the run. -/
def runFailsG {L σ γ R : Type} [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R) (g : γ) (x : σ) (expected : R) : Option String :=
  if !I g x then some "entry: invariant fails"
  else if !(out g x == expected) then some "entry: result differs from expected"
  else walk (μ g x + 1) x
where
  /-- The visits of the run, as in `runFails`, with the same ghost `g` at each visit. -/
  walk : Nat → σ → Option String
    | 0, _ => some "measure"
    | k + 1, y => match stepFailsG b head fuel I μ out g y with
      | some w => some w
      | none => match stepTo b head fuel head y with
        | .head z => walk k z
        | _ => none

inductive Found where
  | pass (samples : Nat) | real (index : Nat) (why : String) | cti (index : Nat) (why : String)
  | unknown (why : String)
  deriving Repr, BEq

/-- Only admitted draws count as checked samples. Zero requests retain `pass 0`. -/
private def noFailure (requested checked : Nat) : Found :=
  if requested > 0 && checked == 0 then .unknown "no admitted samples" else .pass checked

/-- Each sample is checked in order; the first failure gives the result. Admitted failure: `real`;
free failure: `cti`. Zero samples give `pass 0`. -/
def refuteLoop {L σ R : Type} [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (I : σ → Bool) (μ : σ → Nat) (out : σ → R)
    (admitted : Rng → σ × R) (free : Rng → σ) (seed samples : Nat) : Found :=
  let check (index : Nat) : Option Found :=
    match sampleAt admitted free seed index with
    | .admitted x expected => (runFails b head fuel I μ out x expected).map (Found.real index)
    | .free x => (stepFails b head fuel I μ out x).map (Found.cti index)
  ((List.range samples).findSome? check).getD (Found.pass samples)

/-- `refuteLoop` with a ghost `γ`. Each sample is a ghost with its state, so the invariant, the measure and the result
read the ghost of their own sample. -/
def refuteLoopG {L σ γ R : Type} [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R)
    {α β : Type} [AdmitFn α γ σ R] [FreeFn β γ σ] (admitted : α) (free : β) (seed samples : Nat) : Found :=
  go 0 samples 0
where
  go (index : Nat) : Nat → Nat → Found
    | 0, checked => noFailure samples checked
    | left + 1, checked =>
      match sampleAtG? admitted free seed index with
      | none => go (index + 1) left checked
      | some (.admitted (ghost, x) expected) =>
        match runFailsG b head fuel I μ out ghost x expected with
        | some why => .real index why
        | none => go (index + 1) left (checked + 1)
      | some (.free (ghost, x)) =>
        match stepFailsG b head fuel I μ out ghost x with
        | some why => .cti index why
        | none => go (index + 1) left (checked + 1)

/-- The state text of sample `index` for `refuteLoopG`: the state of the admitted or the free sample. -/
def shownG {γ σ R : Type} {ρ : Type} [RenderFn ρ γ σ] (render : ρ)
    {α β : Type} [AdmitFn α γ σ R] [FreeFn β γ σ] (admitted : α) (free : β) (seed index : Nat) : String :=
  match sampleAtG? admitted free seed index with
  | some (.admitted (g, x) _) => RenderFn.render render g x
  | some (.free (g, x)) => RenderFn.render render g x
  | none => "no admitted sample"

/-- The input text of sample `index` for `refuteClaim`: `render` of the input that `inputs` draws from the stream of
`index`, as `refuteClaim` draws it. -/
def shownClaim {α input : Type} [InputFn (Rng → α) input] (render : input → String)
    (inputs : Rng → α) (seed index : Nat) : String :=
  match InputFn.draw inputs (Rng.stream (Rng.ofSeed seed) index) with
  | some x => render x
  | none => "no admitted sample"

/-- Each sample `i` is `gen` of stream `i`; a sample with `lhs` and `rhs` that differ is `real`.
Zero samples give `pass 0`. -/
def refuteClaim {α input R : Type} [InputFn (Rng → α) input] [BEq R] (gen : Rng → α) (lhs rhs : input → Option R)
    (seed samples : Nat) : Found :=
  go 0 samples 0
where
  go (index : Nat) : Nat → Nat → Found
    | 0, checked => noFailure samples checked
    | left + 1, checked =>
      match InputFn.draw gen (Rng.stream (Rng.ofSeed seed) index) with
      | none => go (index + 1) left checked
      | some x =>
        if lhs x == rhs x then go (index + 1) left (checked + 1)
        else .real index "lhs and rhs differ"

/-- Each sample `i` is `gen` of stream `i`, and its argument `arg`; a sample on which the runners `spec` and `machine` differ
(a result, a stuck run or no fuel) is `real`. -/
def refuteCallee {α X Y : Type} [DecidableEq Y] (gen : Rng → α) (arg : α → X) (spec machine : X → Res Y)
    (seed samples : Nat) : Found :=
  let opt (r : Res Y) : Option (Option Y) := match r with
    | .ok y => some (some y)
    | .stuck _ => some none
    | .noFuel => none
  refuteClaim gen (fun a => opt (spec (arg a))) (fun a => opt (machine (arg a))) seed samples

/-- One JSON line, for example `{"verdict":"cti","index":3,"why":"stuck","shown":"..."}`. -/
def Found.line (f : Found) (shown : Nat → String) : String :=
  let str (s : String) : String := (Lean.Json.str s).compress
  let obj (verdict : String) (index : Nat) (why : String) : String :=
    "{\"verdict\":" ++ str verdict ++ ",\"index\":" ++ toString index ++ ",\"why\":" ++ str why
      ++ ",\"shown\":" ++ str (shown index) ++ "}"
  match f with
  | .pass n => "{\"verdict\":\"pass\",\"samples\":" ++ toString n ++ "}"
  | .real i why => obj "real" i why
  | .cti i why => obj "cti" i why
  | .unknown why => "{\"verdict\":\"unknown\",\"why\":" ++ str why ++ "}"

/-! ## The coverage of the edges (REFUTE-COV)

A candidate that no sampled run refutes can still be wrong on a branch that no run takes. The refuter counts the edges of the
blocks that the checked steps run: an edge is a jump from a label to a label, or a return. A step is checked at a state in
which the invariant holds, so a step at another state counts no edge. When the samples leave an edge of the edgeSet (the
edges of the pass of the loop, from the blocks of the function) with no visit, the refuter draws more samples, and runs only the
samples whose run takes such an edge. If an edge is still not visited, the verdict is `uncovered`: no failure was found, and the
candidate is not shown to hold. -/

/-- An edge of the blocks: a jump from a label to a label (`some`), or a return (`none`). -/
abbrev Edge (L : Type) : Type := L × Option L

/-- The visits of the edges, in the order of the first visit. -/
abbrev Counts (L : Type) : Type := List (Edge L × Nat)

/-- `stepTo`, with the edges that the pass runs, in order. A block that fails runs no edge. -/
def stepEdges {L σ R : Type} [DecidableEq L] (b : Leaf L σ R) (head : L) : Nat → L → σ → List (Edge L) × Stop σ R
  | 0, _, _ => ([], .fail "no fuel")
  | fuel + 1, l, x => match b.step l x with
    | .ok (.goto l' x') =>
      if l' = head then ([(l, some l')], .head x')
      else
        let (es, s) := stepEdges b head fuel l' x'
        ((l, some l') :: es, s)
    | .ok (.ret r) => ([(l, none)], .ret r)
    | .ok (.call f _ _) => f.elim
    | .stuck why => ([], .fail why)
    | .noFuel => ([], .fail "no fuel")

/-- The counts with one more visit of `e`. -/
def bump {L : Type} [DecidableEq L] (cs : Counts L) (e : Edge L) : Counts L :=
  if cs.any (fun p => decide (p.1 = e)) then cs.map fun p => if decide (p.1 = e) then (p.1, p.2 + 1) else p else cs ++ [(e, 1)]

/-- The reason that the step at `x` fails, from the pass `s` that starts at `x`: the checks of `stepFailsG` after the test of `I g x`. -/
def stepVerdictG {σ γ R : Type} [BEq R] (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R) (g : γ) (x : σ) :
    Stop σ R → Option String
  | .ret r => if r == out g x then none else some "returns a result other than out"
  | .head y =>
    if !I g y then some "leaves the invariant"
    else if decide (μ g y < μ g x) && out g y == out g x then none
    else some "measure does not decrease or result changes"
  | .fail why => some why

/-- `stepFailsG` at a free state, with the counts. A state outside the invariant is not checked and counts no edge. -/
def freeCov {L σ γ R : Type} [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R) (g : γ) (x : σ) (cs : Counts L) : Option String × Counts L :=
  if !I g x then (none, cs)
  else
    let (es, s) := stepEdges b head fuel head x
    (stepVerdictG I μ out g x s, es.foldl bump cs)

/-- `runFailsG` with the counts. The pass of each visit runs once, and the measure, the result and the invariant of a state
are computed once, for the step that leaves it and for the step that enters it. -/
def runCov {L σ γ R : Type} [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R) (g : γ) (x : σ) (expected : R) (cs : Counts L) :
    Option String × Counts L :=
  if !I g x then (some "entry: invariant fails", cs)
  else if !(out g x == expected) then (some "entry: result differs from expected", cs)
  else walk (μ g x + 1) x (μ g x) (out g x) cs
where
  /-- The visits of the run from `x`, at which the invariant holds; `mx` and `ox` are its measure and result. -/
  walk : Nat → σ → Nat → R → Counts L → Option String × Counts L
    | 0, _, _, _, cs => (some "measure", cs)
    | k + 1, x, mx, ox, cs =>
      let (es, s) := stepEdges b head fuel head x
      let cs := es.foldl bump cs
      match s with
      | .ret r => (if r == ox then none else some "returns a result other than out", cs)
      | .fail why => (some why, cs)
      | .head y =>
        if !I g y then (some "leaves the invariant", cs)
        else
          let my := μ g y
          let oy := out g y
          if decide (my < mx) && oy == ox then walk k y my oy cs
          else (some "measure does not decrease or result changes", cs)

/-- The samples from the index `i`, `n` of them, as `refuteLoopG` checks them, with the counts. The first failure and the counts. -/
def scanFrom {L σ γ R : Type} [DecidableEq L] [BEq R] (b : Leaf L σ R) (head : L) (fuel : Nat)
    (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R)
    {α β : Type} [AdmitFn α γ σ R] [FreeFn β γ σ] (admitted : α) (free : β) (seed : Nat) : Nat → Nat → Counts L → Option Found × Counts L × Nat
  | _, 0, cs => (none, cs, 0)
  | i, n + 1, cs =>
    match sampleAtG? admitted free seed i with
    | none => scanFrom b head fuel I μ out admitted free seed (i + 1) n cs
    | some sample =>
      let (failure, cs') := match sample with
        | .admitted (g, x) e =>
          let (w, cs') := runCov b head fuel I μ out g x e cs
          (w.map (Found.real i), cs')
        | .free (g, x) =>
          let (w, cs') := freeCov b head fuel I μ out g x cs
          (w.map (Found.cti i), cs')
      match failure with
      | some f => (some f, cs', 1)
      | none =>
        let (f, cs'', checked) := scanFrom b head fuel I μ out admitted free seed (i + 1) n cs'
        (f, cs'', checked + 1)

/-- The visits of each edge of `edgeSet` over the first `samples` samples (the checked steps only; the scan stops at a failure). -/
def edgeCounts {L σ γ R : Type} [DecidableEq L] [BEq R] (edgeSet : List (String × Edge L)) (b : Leaf L σ R) (head : L)
    (fuel : Nat) (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R)
    {α β : Type} [AdmitFn α γ σ R] [FreeFn β γ σ] (admitted : α) (free : β) (seed samples : Nat) : List (String × Nat) :=
  let (_, cs, _) := scanFrom b head fuel I μ out admitted free seed 0 samples []
  edgeSet.map fun (name, e) => (name, ((cs.find? fun p => decide (p.1 = e)).map (·.2)).getD 0)

/-- The edges of `edgeSet` with no visit in `cs`. -/
def missingOf {L : Type} [DecidableEq L] (edgeSet : List (String × Edge L)) (cs : Counts L) : List (String × Edge L) :=
  edgeSet.filter fun (_, e) => !(cs.any fun p => decide (p.1 = e))

/-- Whether an edge of `es` is an edge of `ms`. -/
def touches {L : Type} [DecidableEq L] (ms es : List (Edge L)) : Bool := ms.any fun m => es.any fun e => decide (e = m)

/-- Whether the passes of the visits of the run from `x` (at most `k`, with no test of the invariant) run an edge of `ms`, and the
number of passes that it ran, added to `v`. -/
def probeRun {L σ R : Type} [DecidableEq L] (b : Leaf L σ R) (head : L) (fuel : Nat) (ms : List (Edge L)) :
    Nat → σ → Nat → Bool × Nat
  | 0, _, v => (false, v)
  | k + 1, y, v =>
    let (es, s) := stepEdges b head fuel head y
    if touches ms es then (true, v + 1)
    else match s with
      | .head z => probeRun b head fuel ms k z (v + 1)
      | _ => (false, v + 1)

/-- The extra samples from the index `i`, at most `n` of them, while an edge of `edgeSet` has no visit and the budget of passes
lasts. A free sample is checked when its pass runs a missing edge; an admitted sample, when its run does (the probe of the run
runs no invariant). The first failure, the counts and the number of samples that were looked at. -/
def steer {L σ γ R : Type} [DecidableEq L] [BEq R] (edgeSet : List (String × Edge L)) (b : Leaf L σ R) (head : L) (fuel : Nat)
    (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R)
    {α β : Type} [AdmitFn α γ σ R] [FreeFn β γ σ] (admitted : α) (free : β) (seed : Nat) :
    Nat → Nat → Nat → Counts L → Nat → Option Found × Counts L × Nat
  | _, 0, _, cs, t => (none, cs, t)
  | i, n + 1, budget, cs, t =>
    let ms := (missingOf edgeSet cs).map (·.2)
    if ms.isEmpty || budget == 0 then (none, cs, t)
    else
      match sampleAtG? admitted free seed i with
      | none => steer edgeSet b head fuel I μ out admitted free seed (i + 1) n budget cs t
      | some (.free (g, x)) =>
        let (es, _) := stepEdges b head fuel head x
        if !touches ms es then steer edgeSet b head fuel I μ out admitted free seed (i + 1) n (budget - 1) cs (t + 1)
        else
          match freeCov b head fuel I μ out g x cs with
          | (some w, cs') => (some (.cti i w), cs', t + 1)
          | (none, cs') => steer edgeSet b head fuel I μ out admitted free seed (i + 1) n (budget - 1) cs' (t + 1)
      | some (.admitted (g, x) e) =>
        if !I g x then (some (.real i "entry: invariant fails"), cs, t + 1)
        else if !(out g x == e) then (some (.real i "entry: result differs from expected"), cs, t + 1)
        else
          let (hit, v) := probeRun b head fuel ms (μ g x + 1) x 0
          if !hit then steer edgeSet b head fuel I μ out admitted free seed (i + 1) n (budget - v - 1) cs (t + 1)
          else
            match runCov b head fuel I μ out g x e cs with
            | (some w, cs') => (some (.real i w), cs', t + 1)
            | (none, cs') => steer edgeSet b head fuel I μ out admitted free seed (i + 1) n (budget - 2 * v - 1) cs' (t + 1)

/-- The result of the refuter with the coverage: the result of `refuteLoopG`, or `uncovered`: no sample fails, and the edges
named have no visit after the extra samples (`tried` of them were looked at). -/
inductive CovFound where
  | found (f : Found)
  | uncovered (samples tried : Nat) (missing : List String)
  deriving Repr, BEq

/-- The most extra samples, as a multiple of the samples of the run. -/
def extraFactor : Nat := 4

/-- The least budget of passes of the extra samples, as a multiple of the samples of the run. The budget is the count of the
visits of the first samples, when that is more. -/
def budgetFactor : Nat := 50

/-- `refuteLoopG` with the coverage of the edges of `edgeSet` (the name of each edge, and the edge). The first `samples` samples
are checked as `refuteLoopG` checks them, so a failure there is the same failure. With no failure and an edge with no visit, the
samples after them are drawn (`steer`). A failure of an extra sample is a failure of that sample. With no failure and an edge with
no visit at the end, the result is `uncovered`; with no edge missing it is `pass samples`. -/
def refuteLoopCov {L σ γ R : Type} [DecidableEq L] [BEq R] (edgeSet : List (String × Edge L)) (b : Leaf L σ R) (head : L)
    (fuel : Nat) (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R)
    {α β : Type} [AdmitFn α γ σ R] [FreeFn β γ σ] (admitted : α) (free : β) (seed samples : Nat) : CovFound :=
  let (f1, cs1, checked) := scanFrom b head fuel I μ out admitted free seed 0 samples []
  match f1 with
  | some f => .found f
  | none =>
    if (missingOf edgeSet cs1).isEmpty then .found (noFailure samples checked)
    else
      let budget := max (cs1.foldl (fun a p => a + p.2) 0) (budgetFactor * samples)
      let (f2, cs2, tried) :=
        steer edgeSet b head fuel I μ out admitted free seed samples (extraFactor * samples) budget cs1 0
      match f2 with
      | some f => .found f
      | none =>
        match missingOf edgeSet cs2 with
        | [] => .found (noFailure samples (checked + tried))
        | ms => .uncovered samples tried (ms.map (·.1))

/-- The verdict line of the result: as `Found.line`, and for `uncovered` an `unknown` verdict that names the edges. -/
def CovFound.line (c : CovFound) (shown : Nat → String) : String :=
  match c with
  | .found f => f.line shown
  | .uncovered samples tried missing =>
    let why := s!"edge not covered: {", ".intercalate missing} ({samples} samples, {tried} more tried)"
    "{\"verdict\":\"unknown\",\"why\":" ++ (Lean.Json.str why).compress ++ "}"

/-! ## Draws guided by the branch conditions (HARNESS-LOOP3)

The random draws can miss a path whose branch needs two inputs to agree (a slot of the source equal to the target slot): then
its edges have no visit, and each candidate is `uncovered`. The guided search mutates admitted inputs. The words of a mutation
are the operands of the branch conditions of the blocks that the run reaches (`Guide.ops`), and the words 0 and all ones; a
mutation can set a part of the input to such a word, so that a comparison of the run holds (or fails) at the next run. A
mutant whose run takes an edge that no run took before is kept as a seed of later mutations (coverage feedback); a mutant whose
run takes a missing edge is checked as an admitted sample. A mutant is an admitted sample: its input is one that the spec
accepts, and its run starts at the entry. -/

/-- The labels and the states at the start of the blocks of the pass from `l` at `x`, the first one included. -/
def passStates {L σ R : Type} [DecidableEq L] (b : Leaf L σ R) (head : L) : Nat → L → σ → List (L × σ)
  | 0, _, _ => []
  | fuel + 1, l, x => (l, x) :: match b.step l x with
    | .ok (.goto l' x') => if l' = head then [] else passStates b head fuel l' x'
    | _ => []

/-- The guide of the search: `mutant g m d gh` is the admitted sample (ghost, state, expected result) of the input of the ghost
`gh` after a mutation drawn from `m` with the words `d`, built with the stream `g` (none when the spec refuses the input); `ops
l x` are the operands of the branch condition of the block `l` at its start state `x`; `render` shows a sample. -/
structure Guide (L γ σ R : Type) where
  mutant : Rng → Rng → List UInt64 → γ → Option (γ × σ × R)
  ops : L → σ → List UInt64
  render : γ → σ → String

/-- The words of the run from `x`: the operands of the branch conditions in the passes of at most `k` visits. -/
def runWords {L σ R : Type} [DecidableEq L] (b : Leaf L σ R) (head : L) (fuel : Nat) (ops : L → σ → List UInt64) :
    Nat → σ → List UInt64
  | 0, _ => []
  | k + 1, x =>
    (passStates b head fuel head x).flatMap (fun (l, y) => ops l y) ++
      match stepTo b head fuel head x with
      | .head z => runWords b head fuel ops k z
      | _ => []

/-- The edges of the passes of at most `k` visits of the run from `x`, with no test of the invariant. -/
def runEdges {L σ R : Type} [DecidableEq L] (b : Leaf L σ R) (head : L) (fuel : Nat) : Nat → σ → List (Edge L)
  | 0, _ => []
  | k + 1, x =>
    let (es, s) := stepEdges b head fuel head x
    es ++ match s with
      | .head z => runEdges b head fuel k z
      | _ => []

/-- The most visits of a run of the guided search. -/
def guideVisits : Nat := 64

/-- A seed of the guided search: the stream of its build, its ghost, its state and its expected result. -/
structure Seed (γ σ R : Type) where
  (g : Rng) (ghost : γ) (x : σ) (expected : R)

/-- The result of the guided search: a failure with its reason and the render of the mutant, or none; the counts; the number of
mutants. -/
abbrev GuidedOut (L : Type) : Type := Option (String × String) × Counts L × Nat

/-- The guided search from the mutant `i`, at most `n` more, with the seeds `corpus`, the counts `cs` of the checked runs and the
edges `seen` of all runs. -/
private def guidedWithCount {L σ γ R : Type} [DecidableEq L] [BEq R] (edgeSet : List (String × Edge L)) (b : Leaf L σ R) (head : L)
    (fuel : Nat) (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R) (guide : Guide L γ σ R) (seed : Nat) :
    Nat → Nat → List (Seed γ σ R) → Counts L → List (Edge L) → Option (String × String) × Counts L × Nat × Nat
  | _, 0, _, cs, _ => (none, cs, 0, 0)
  | i, n + 1, corpus, cs, seen =>
    let ms := (missingOf edgeSet cs).map (·.2)
    match corpus with
    | [] => (none, cs, 0, 0)
    | c0 :: _ =>
      if ms.isEmpty then (none, cs, 0, 0) else
      let r := Rng.stream (Rng.ofSeed seed) (1000003 + i)
      let c := corpus[(r.natIn 0 (corpus.length - 1)).1]?.getD c0
      let words := [0, 18446744073709551615] ++ runWords b head fuel guide.ops 8 c.x
      match guide.mutant c.g (r.stream 1) words c.ghost with
      | none =>
        let (f, cs', t, accepted) := guidedWithCount edgeSet b head fuel I μ out guide seed (i + 1) n corpus cs seen
        (f, cs', t + 1, accepted)
      | some (g', x', e') =>
        let es := runEdges b head fuel guideVisits x'
        let fresh := (es.filter fun e => !seen.any fun s => decide (s = e)).eraseDups
        let corpus := if fresh.isEmpty then corpus else corpus ++ [⟨c.g, g', x', e'⟩]
        let seen := seen ++ fresh
        if !touches ms es then
          let (f, cs', t, accepted) := guidedWithCount edgeSet b head fuel I μ out guide seed (i + 1) n corpus cs seen
          (f, cs', t + 1, accepted + 1)
        else if !I g' x' then (some ("entry: invariant fails", guide.render g' x'), cs, 1, 1)
        else if !(out g' x' == e') then (some ("entry: result differs from expected", guide.render g' x'), cs, 1, 1)
        else
          match runCov b head fuel I μ out g' x' e' cs with
          | (some w, cs') => (some (w, guide.render g' x'), cs', 1, 1)
          | (none, cs') =>
            let (f, cs'', t, accepted) := guidedWithCount edgeSet b head fuel I μ out guide seed (i + 1) n corpus cs' seen
            (f, cs'', t + 1, accepted + 1)

/-- The guided search with attempted mutation counts, for existing callers. -/
def guided {L σ γ R : Type} [DecidableEq L] [BEq R] (edgeSet : List (String × Edge L)) (b : Leaf L σ R) (head : L)
    (fuel : Nat) (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R) (guide : Guide L γ σ R) (seed : Nat)
    (index remaining : Nat) (corpus : List (Seed γ σ R)) (cs : Counts L) (seen : List (Edge L)) : GuidedOut L :=
  let (f, cs', attempted, _) := guidedWithCount edgeSet b head fuel I μ out guide seed index remaining corpus cs seen
  (f, cs', attempted)

/-- The seeds of the guided search: the admitted samples at the even indices below `2 * k`. -/
def seedsOf {γ σ R : Type} {α : Type} [AdmitFn α γ σ R] (admitted : α) (seed k : Nat) : List (Seed γ σ R) :=
  (List.range k).filterMap fun j =>
    let g := Rng.stream (Rng.ofSeed seed) (2 * j)
    (AdmitFn.admit admitted g).map fun (gh, x, e) => ⟨g, gh, x, e⟩

/-- The number of seeds of the guided search. -/
def guideSeeds : Nat := 16

/-- The result of the refuter with the guided search: as `CovFound`, and a failure of a mutant (`real`, with its reason and its
render). -/
inductive GuidedFound where
  | cov (c : CovFound)
  | mutant (why shown : String) (tried : Nat)

/-- `refuteLoopCov`, then the guided search (at most `extraFactor * samples` mutants) when an edge has no visit. -/
def refuteLoopCovG {L σ γ R : Type} [DecidableEq L] [BEq R] (edgeSet : List (String × Edge L)) (guide : Guide L γ σ R)
    (b : Leaf L σ R) (head : L) (fuel : Nat) (I : γ → σ → Bool) (μ : γ → σ → Nat) (out : γ → σ → R)
    {α β : Type} [AdmitFn α γ σ R] [FreeFn β γ σ] (admitted : α) (free : β) (seed samples : Nat) : GuidedFound :=
  let (f1, cs1, checked) := scanFrom b head fuel I μ out admitted free seed 0 samples []
  match f1 with
  | some f => .cov (.found f)
  | none =>
    if (missingOf edgeSet cs1).isEmpty then .cov (.found (noFailure samples checked)) else
    let budget := max (cs1.foldl (fun a p => a + p.2) 0) (budgetFactor * samples)
    let (f2, cs2, tried) := steer edgeSet b head fuel I μ out admitted free seed samples (extraFactor * samples) budget cs1 0
    match f2 with
    | some f => .cov (.found f)
    | none =>
      if (missingOf edgeSet cs2).isEmpty then .cov (.found (noFailure samples (checked + tried))) else
      let seen := cs2.map (·.1)
      let (f3, cs3, mutants, accepted) := guidedWithCount edgeSet b head fuel I μ out guide seed 0 (extraFactor * samples)
        (seedsOf admitted seed guideSeeds) cs2 seen
      match f3 with
      | some (why, shown) => .mutant why shown mutants
      | none =>
        match missingOf edgeSet cs3 with
        | [] => .cov (.found (noFailure samples (checked + tried + accepted)))
        | ms => .cov (.uncovered samples (tried + mutants) (ms.map (·.1)))

/-- The verdict line: as `CovFound.line`; a failing mutant is `real` with the index `0` and its render. -/
def GuidedFound.line (f : GuidedFound) (shown : Nat → String) : String :=
  match f with
  | .cov c => c.line shown
  | .mutant why s tried =>
    let str (s : String) : String := (Lean.Json.str s).compress
    "{\"verdict\":\"real\",\"index\":0,\"why\":" ++ str s!"{why} (a guided mutant, {tried} mutants)" ++ ",\"shown\":" ++ str s ++ "}"

end Skel.Refute
