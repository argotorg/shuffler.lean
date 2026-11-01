module

public import BbuKraken.FlatRel
import all BbuKraken.FlatRel
public import BbuKraken.FlatModelTest
import all BbuKraken.FlatModelTest

@[expose] public section

/-!
Tests of the statement of `FlatBridge.lean`. `relB` is a decision procedure for `Rel`
(`relB_sound`). The `#guard`s check that `Rel` holds for the result of `build_bottom_up` and
of the list model on the inputs of `FlatModelTest.lean` (`n ≤ 3`; `n ≤ 2` for `u2`, for time)
and on its deep stacks, so that the bridge theorem is not false on them. The negative tests show
that `Rel` does not hold for a wrong result.
-/

namespace Bbu.Flat.RelTest

open Bbu Bbu.Flat Bbu.Flat.Test

/-! ## A decision procedure for `Rel` -/

def holdsB (fs : St) (st : Bbu.St) (pos excess : Nat) : Bool :=
  decide (fs.trace = st.trace) && decide (slotsOf fs = st.slots.map Slot.val)
    && decide (fs.blockedOffset = BitVec.ofNat 64 pos)
    && decide (fs.blockedExcess = BitVec.ofNat 64 excess)

def relB (r : Word × Option St) : M Bbu.St → Bool
  | .ok st => match r.2 with
    | some fs => decide (r.1 = BitVec.ofNat 64 st.trace.length) && holdsB fs st 0 0
    | none => false
  | .error (.blocked pos excess st) => match r.2 with
    | some fs => decide (r.1 = BitVec.ofNat 64 st.trace.length) && holdsB fs st pos excess
    | none => false
  | .error .assertion => decide (r.1 = -2#64)

theorem holdsB_sound {fs : St} {st : Bbu.St} {pos excess : Nat}
    (h : holdsB fs st pos excess = true) : Holds fs st pos excess := by
  simp only [holdsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem relB_sound {r : Word × Option St} : ∀ {res : M Bbu.St}, relB r res = true → Rel r res
  | .ok st, h => by
    obtain ⟨w, o⟩ := r
    cases o with
    | none => simp [relB] at h
    | some fs =>
      simp only [relB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨fs, by rw [h.1], holdsB_sound h.2⟩
  | .error (.blocked pos excess st), h => by
    obtain ⟨w, o⟩ := r
    cases o with
    | none => simp [relB] at h
    | some fs =>
      simp only [relB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨fs, by rw [h.1], holdsB_sound h.2⟩
  | .error .assertion, h => by simpa [relB, Rel] using h

/-! ## The inputs of the bridge -/

-- The inputs of `build_bottom_up` for a case of `FlatModelTest.lean`: the data above `m` is
-- `junkSlots`.
def dataOf (source : List StackSlot) : Vector StackSlot MAX_N :=
  Vector.ofFn fun i => source[i.val]?.getD junkSlots[i]

def flatR (u : Uninit) (source target : List StackSlot) (dests spilled : List Nat) :
    Word × Option St :=
  build_bottom_up (.ofNat 64 source.length) (.ofNat 64 target.length) (dataOf source) (vec target)
    (vec (words dests)) (spillsOf spilled) u

-- The list model on the inputs that the bridge gives (`listEnv`, `listSource`, `listDests`).
def listR (source target : List StackSlot) (dests spilled : List Nat) : M Bbu.St :=
  Bbu.buildBottomUp (listEnv target.length (vec target) (spillsOf spilled))
    (listSource source.length (dataOf source)) (listDests source.length (vec (words dests)))

def relOn (u : Uninit) (source target : List StackSlot) (dests spilled : List Nat) : Bool :=
  relB (flatR u source target dests spilled) (listR source target dests spilled)

-- `Dests n` as a `Bool`: the hypothesis `hd` of the bridge.
def destsB (n : Nat) (l : List Nat) : Bool := l.all (· < n) && l.Nodup

/-! ## The bridge inputs are the inputs of the list tests -/

#guard (cases.filter (·.2.1.length ≤ 2)).all fun (s, t, d) =>
  (listEnv t.length (vec t) (spillsOf [1])).target == t
    && listSource s.length (dataOf s) == s
    && listDests s.length (vec (words d)) == d
    && destsB t.length d

/-! ## `Rel` holds -/

#guard cases.all fun (s, t, d) => relOn u1 s t d [1]
#guard (cases.filter (·.2.1.length ≤ 2)).all fun (s, t, d) => relOn u2 s t d [1]
#guard deepCases.all fun (s, t, d) => relOn u1 s t d []
-- The cases reach the three results.
#guard (cases.filter (·.2.1.length ≤ 2)).any fun (s, t, d) => listR s t d [1] matches .ok _
#guard (cases.filter (·.2.1.length ≤ 2)).any fun (s, t, d) =>
  listR s t d [1] matches .error .assertion
#guard deepCases.any fun (s, t, d) => listR s t d [] matches .error (.blocked ..)

/-! ## `Rel` does not hold for a wrong result -/

-- Two slots that change places: one swap.
def sw := flatR u1 [x, y] [x, y] [1, 0] []
def swL := listR [x, y] [x, y] [1, 0] []
#guard relB sw swL
-- A wrong count of operations.
#guard !relB (5, sw.2) swL
-- No state.
#guard !relB (sw.1, none) swL
-- The state of another input.
#guard !relB (flatR u1 [x, y] [x, y] [0, 1] []) swL
-- Blocked words that are not 0.
#guard !relB (sw.1, sw.2.map fun fs => { fs with blockedExcess := 1 }) swL
-- A stack with one more slot.
#guard !relB (sw.1, sw.2.map fun fs => { fs with size := fs.size + 1 }) swL
-- A done result for an assertion, and an assertion for a done result.
#guard !relB sw (.error .assertion)
#guard !relB (-2, none) swL
#guard relB (-2, none) (.error .assertion)
-- A done result for a blocked result.
#guard match swL with
  | .ok st => !relB sw (.error (.blocked 0 1 st)) && relB sw (.ok st)
  | .error _ => false

end Bbu.Flat.RelTest
