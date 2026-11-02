module

public import ShufflerBridge.Emission.Basic
import all ShufflerBridge.Emission.Basic
public import ShufflerBridge.Emission.Unfold
import all ShufflerBridge.Emission.Unfold

@[expose] public section

/-!
The statements of the bridge lemmas, one for each model function. Each lemma is
proved in its own file and takes the statements that it uses as hypotheses, so
the proofs do not depend on each other. `ShufflerBridge.Emission.BuildBottomUp` puts them together.
-/

namespace ShufflerBridge.Emission

open Shuffler Shuffler.Emission

/-! ## Actions -/

-- `add` with a push is `State.push`.
def PushStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (v : FlatShuffler.StackSlot)
    (d : Nat) (hd : d < (decodedTargetStack e).length),
    Rel e st state → StackSlotHasCanonicalEncoding v →
    ((decodeStackSlot v).can_be_freely_generated ∨ (spilledVariables e source).is_spilled (decodeStackSlot v)) →
    Corr (Rel e) (FlatShuffler.add st v d (.push v)) (state.push (decodeStackSlot v) ⟨d, hd⟩)

-- `add` with a dup of the slot at `c` is `State.dup`. As `emit`, the model
-- first rejects a function return label.
def DupStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (c d : Nat)
    (hd : d < (decodedTargetStack e).length),
    Rel e st state → c < st.len → st.len - 1 - c ≤ FlatShuffler.MAX_DUP_DEPTH →
    Corr (Rel e)
      (if (st.val c).kind == FlatShuffler.FunctionReturnLabel then .error .assertion
        else FlatShuffler.add st (st.val c) d (.dup (st.len - c)))
      (state.dup c ⟨d, hd⟩)

def SwapWithStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (pos : Nat),
    Rel e st state → Corr (Rel e) (FlatShuffler.swapWith st pos) (state.swapWith pos)

def SwapDestStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (a b : Nat),
    Rel e st state → a < st.len → b < st.len →
    ∃ state', state.swapDestinations a b = .ok state' ∧ Rel e (FlatShuffler.swapDestinations st a b) state'

/-! ## Generation -/

def ProduceStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (d : Nat)
    (hd : d < (decodedTargetStack e).length),
    Rel e st state → 0 < st.pendingGenerations →
    ResCorr (Rel e) (FlatShuffler.produce e st d) (state.produce ⟨d, hd⟩)

def GenerateStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (d : Nat),
    Rel e st state → 0 < st.pendingGenerations →
    ResCorr (Rel e) (FlatShuffler.generate e st d) (state.generate d)

/-! ## Scans -/

-- The model urgent offset `u` (`n` for none) and the original choice.
def UrgentRel (n u : Nat) : Option Nat → Prop
  | none => u = n
  | some x => x < n ∧ u = x

-- The scan of the original returns a block at once, so the statement takes the
-- rest of the iteration as the continuations `restM` and `restO`.
def UrgentStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (t : Nat)
    (restM : Nat → FlatShuffler.M (FlatShuffler.St × FlatShuffler.Next))
    (restO : Option Nat → Except ShuffleErr (OResult e source)),
    Rel e st state →
    (∀ u uo, UrgentRel e.n u uo → StepCorr e (restM u) state (restO uo)) →
    StepCorr e ((FlatShuffler.urgent e st t).bind restM) state (origScan state t restO)

def CopyScanStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source)
    (b : Fin state.stack.length),
    Rel e st state → origCopyScan state b = .ok ((FlatShuffler.movableCopy st b).getD b)

/-! ## The final permutation -/

def FinishStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source),
    Rel e st state →
    ResCorr (Rel e) (if st.len = e.n then FlatShuffler.finish st else .error .assertion)
      (post (origFinish state))

/-! ## The branches of `step` after the urgent scan -/

-- An urgent offset: generate it, and stay at `t`.
def RestUrgentStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (t u : Nat)
    (uo : Option Nat),
    Rel e st state → 0 < st.pendingGenerations → t < e.n → UrgentRel e.n u uo →
    (u ≠ e.n ∧ u ≠ t ∧ st.len < t + FlatShuffler.MAX_SWAP_DEPTH) →
    StepCorr e ((FlatShuffler.generate e st u).map (·, .next t)) state (origRest t state uo)

-- The offset at the top: generate it, and stay at `t`.
def RestTopStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (t u : Nat)
    (uo : Option Nat),
    Rel e st state → 0 < st.pendingGenerations → t < e.n → UrgentRel e.n u uo →
    ¬(u ≠ e.n ∧ u ≠ t ∧ st.len < t + FlatShuffler.MAX_SWAP_DEPTH) →
    (u = e.n ∧ t < st.len ∧ st.len < e.n ∧ FlatShuffler.positionOf st st.len = none ∧
      st.len < t + FlatShuffler.MAX_SWAP_DEPTH) →
    StepCorr e ((FlatShuffler.generate e st st.len).map (·, .next t)) state (origRest t state uo)

-- The slot at `b` is bound for `t`.
def RestBoundStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (t u : Nat)
    (uo : Option Nat) (b : Nat),
    Rel e st state → t < e.n → UrgentRel e.n u uo →
    ¬(u ≠ e.n ∧ u ≠ t ∧ st.len < t + FlatShuffler.MAX_SWAP_DEPTH) →
    ¬(u = e.n ∧ t < st.len ∧ st.len < e.n ∧ FlatShuffler.positionOf st st.len = none ∧
      st.len < t + FlatShuffler.MAX_SWAP_DEPTH) →
    FlatShuffler.positionOf st t = some b →
    StepCorr e ((FlatShuffler.takeBound st t).bind fun (st, done) =>
        if done then .ok (st, .next (t + 1)) else FlatShuffler.placeTop st t)
      state (origRest t state uo)

-- No slot is bound for `t`: generate it.
def RestUnboundStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (t u : Nat)
    (uo : Option Nat),
    Rel e st state → 0 < st.pendingGenerations → t < e.n → UrgentRel e.n u uo →
    ¬(u ≠ e.n ∧ u ≠ t ∧ st.len < t + FlatShuffler.MAX_SWAP_DEPTH) →
    ¬(u = e.n ∧ t < st.len ∧ st.len < e.n ∧ FlatShuffler.positionOf st st.len = none ∧
      st.len < t + FlatShuffler.MAX_SWAP_DEPTH) →
    FlatShuffler.positionOf st t = none →
    StepCorr e ((FlatShuffler.generate e st t).bind fun st =>
        if t < st.len ∧ st.dest t = t then .ok (st, .next (t + 1)) else FlatShuffler.placeTop st t)
      state (origRest t state uo)

/-! ## The loop -/

def StepStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (t : Nat),
    Rel e st state → t < e.n → StepCorr e (FlatShuffler.step e st t) state (buildBottomUp.loop t state)

def LoopStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : Stack) (st : FlatShuffler.St) (state : OState e source) (t : Nat),
    Rel e st state →
    ResCorr (Rel e) (FlatShuffler.loop FlatShuffler.finish e st t) (post (buildBottomUp.loop t state))

/-! ## The initial state -/

def InitValidStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : List FlatShuffler.StackSlot) (dests : List Nat) (h : ModelValid e source dests),
    (initState e source dests h).Valid

def InitRelStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : List FlatShuffler.StackSlot) (dests : List Nat) (h : ModelValid e source dests),
    Rel e (FlatShuffler.init e source dests) (initState e source dests h)

def ExpectedStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : List FlatShuffler.StackSlot) (dests : List Nat) (h : ModelValid e source dests),
    (initState e source dests h).expectedStack = (expected e source dests).map decodeStackSlot

def MappedStmt : Prop :=
  ∀ (e : FlatShuffler.Env) (source : List FlatShuffler.StackSlot) (dests : List Nat) (h : ModelValid e source dests),
    Mapped e source dests →
    ∀ i j, (initState e source dests h).mapping i = some j →
      (initState e source dests h).stack[i] = (decodedTargetStack e)[j]

end ShufflerBridge.Emission
