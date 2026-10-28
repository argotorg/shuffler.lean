import BbuBridge.Basic
import BbuBridge.Unfold

/-!
The statements of the bridge lemmas, one for each model function. Each lemma is
proved in its own file and takes the statements that it uses as hypotheses, so
the proofs do not depend on each other. `BbuBridge.Bbu` puts them together.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

/-! ## Actions -/

-- `add` with a push is `State.push`.
def PushStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (v : Bbu.Word)
    (d : Nat) (hd : d < (tgt e).length),
    Rel e st state → (Bbu.isFree v = true ∨ Bbu.isSpilled e v = true) →
    Corr (Rel e) (Bbu.add st v d (.push v)) (state.push (decode v) ⟨d, hd⟩)

-- `add` with a dup of the slot at `c` is `State.dup`.
def DupStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (c d : Nat)
    (hd : d < (tgt e).length),
    Rel e st state → c < st.len → st.len - 1 - c ≤ Bbu.MAX_DUP_DEPTH →
    Corr (Rel e) (Bbu.add st (st.val c) d (.dup (st.len - c))) (state.dup c ⟨d, hd⟩)

def SwapWithStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (pos : Nat),
    Rel e st state → Corr (Rel e) (Bbu.swapWith st pos) (state.swapWith pos)

def SwapDestStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (a b : Nat),
    Rel e st state → a < st.len → b < st.len →
    ∃ state', state.swapDestinations a b = .ok state' ∧ Rel e (Bbu.swapDest st a b) state'

/-! ## Generation -/

def ProduceStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (d : Nat)
    (hd : d < (tgt e).length),
    Rel e st state → Corr (Rel e) (Bbu.produce e st d) (state.produce ⟨d, hd⟩)

def GenerateStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (d : Nat),
    Rel e st state → Corr (Rel e) (Bbu.generate e st d) (state.generate d)

/-! ## Scans -/

-- The model urgent offset `u` (`n` for none) and the original choice.
def UrgentRel (n u : Nat) : Option Nat → Prop
  | none => u = n
  | some x => x < n ∧ u = x

def UrgentStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (t : Nat),
    Rel e st state → Corr (UrgentRel e.n) (Bbu.urgent e st t) (origUrgent state t)

def CopyScanStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source)
    (b : Fin state.stack.length),
    Rel e st state → origCopyScan state b = .ok ((Bbu.movableCopy st b).getD b)

/-! ## The final permutation -/

def FinishStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source),
    Rel e st state →
    (if st.len = e.n then Bbu.finish st else .error .assertion) =
      encodeRes (post (tgt e) (origFinish state))

/-! ## The branches of `step` after the urgent scan -/

-- An urgent offset: generate it, and stay at `t`.
def RestUrgentStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (t u : Nat)
    (uo : Option Nat),
    Rel e st state → t < e.n → UrgentRel e.n u uo →
    (u ≠ e.n ∧ u ≠ t ∧ st.len < t + Bbu.MAX_SWAP_DEPTH) →
    StepCorr e ((Bbu.generate e st u).map (·, .next t)) state (origRest t state uo)

-- The offset at the top: generate it, and stay at `t`.
def RestTopStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (t u : Nat)
    (uo : Option Nat),
    Rel e st state → t < e.n → UrgentRel e.n u uo →
    ¬(u ≠ e.n ∧ u ≠ t ∧ st.len < t + Bbu.MAX_SWAP_DEPTH) →
    (u = e.n ∧ t < st.len ∧ st.len < e.n ∧ Bbu.positionOf st st.len = none ∧
      st.len < t + Bbu.MAX_SWAP_DEPTH) →
    StepCorr e ((Bbu.generate e st st.len).map (·, .next t)) state (origRest t state uo)

-- The slot at `b` is bound for `t`.
def RestBoundStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (t u : Nat)
    (uo : Option Nat) (b : Nat),
    Rel e st state → t < e.n → UrgentRel e.n u uo →
    ¬(u ≠ e.n ∧ u ≠ t ∧ st.len < t + Bbu.MAX_SWAP_DEPTH) →
    ¬(u = e.n ∧ t < st.len ∧ st.len < e.n ∧ Bbu.positionOf st st.len = none ∧
      st.len < t + Bbu.MAX_SWAP_DEPTH) →
    Bbu.positionOf st t = some b →
    StepCorr e ((Bbu.takeBound st t b).bind fun (st, done) =>
        if done then .ok (st, .next (t + 1)) else Bbu.placeTop st t)
      state (origRest t state uo)

-- No slot is bound for `t`: generate it.
def RestUnboundStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (t u : Nat)
    (uo : Option Nat),
    Rel e st state → t < e.n → UrgentRel e.n u uo →
    ¬(u ≠ e.n ∧ u ≠ t ∧ st.len < t + Bbu.MAX_SWAP_DEPTH) →
    ¬(u = e.n ∧ t < st.len ∧ st.len < e.n ∧ Bbu.positionOf st st.len = none ∧
      st.len < t + Bbu.MAX_SWAP_DEPTH) →
    Bbu.positionOf st t = none →
    StepCorr e ((Bbu.generate e st t).bind fun st =>
        if t < st.len ∧ st.dest t = t then .ok (st, .next (t + 1)) else Bbu.placeTop st t)
      state (origRest t state uo)

/-! ## The loop -/

def StepStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (t : Nat),
    Rel e st state → t < e.n → StepCorr e (Bbu.step e st t) state (buildBottomUp.loop t state)

def LoopStmt : Prop :=
  ∀ (e : Bbu.Env) (source : Stack) (st : Bbu.St) (state : OState e source) (t : Nat),
    Rel e st state → Bbu.loop e st t = encodeRes (post (tgt e) (buildBottomUp.loop t state))

/-! ## The initial state -/

def InitValidStmt : Prop :=
  ∀ (e : Bbu.Env) (source : List Bbu.Word) (dests : List Nat) (h : ModelValid e source dests),
    (initState e source dests h).Valid

def InitRelStmt : Prop :=
  ∀ (e : Bbu.Env) (source : List Bbu.Word) (dests : List Nat) (h : ModelValid e source dests),
    Rel e (initSt e source dests) (initState e source dests h)

def ExpectedStmt : Prop :=
  ∀ (e : Bbu.Env) (source : List Bbu.Word) (dests : List Nat) (h : ModelValid e source dests),
    (initState e source dests h).expectedStack = (expected e source dests).map decode

def MappedStmt : Prop :=
  ∀ (e : Bbu.Env) (source : List Bbu.Word) (dests : List Nat) (h : ModelValid e source dests),
    Mapped e source dests →
    ∀ i j, (initState e source dests h).mapping i = some j →
      (initState e source dests h).stack[i] = (tgt e)[j]

end BbuBridge
