import Shuffler.Feasibility.Spec

/-!
Costs for traces with a fixed spill set and source stack. Placement fixes the
target stack. Generation permits any final order with the same additions.
Gas is a static sum. It does not include memory expansion or spill stores.
Encoded PUSH widths are supplied by the caller because layout can set them.

The optimality predicates below specify the comparison set. They do not give
a structural condition for an optimal trace or implement an optimal planner.
-/

namespace Shuffler.Optimality

@[ext]
structure Cost where
  gas : Nat
  bytes : Nat
  deriving DecidableEq, Repr

def Cost.zero : Cost := ⟨0, 0⟩

def Cost.add (a b : Cost) : Cost := ⟨a.gas + b.gas, a.bytes + b.bytes⟩

@[simp] theorem Cost.zero_add (a : Cost) : Cost.zero.add a = a := by
  cases a
  simp [Cost.zero, Cost.add]

@[simp] theorem Cost.add_zero (a : Cost) : a.add Cost.zero = a := by
  cases a
  simp [Cost.zero, Cost.add]

theorem Cost.add_assoc (a b c : Cost) : (a.add b).add c = a.add (b.add c) := by
  simp [Cost.add, Nat.add_assoc]

-- Integer weights also represent rational ratios after clearing denominators.
-- A zero weight is allowed, but both weights cannot be zero.
structure Weights where
  gas : Nat
  bytes : Nat
  positive : 0 < gas ∨ 0 < bytes
  deriving DecidableEq

def Weights.gasOnly : Weights := ⟨1, 0, by decide⟩

def Weights.bytesOnly : Weights := ⟨0, 1, by decide⟩

def Cost.score (cost : Cost) (weights : Weights) : Nat :=
  weights.gas * cost.gas + weights.bytes * cost.bytes

@[simp] theorem Cost.score_gasOnly (cost : Cost) :
    cost.score Weights.gasOnly = cost.gas := by
  simp [Cost.score, Weights.gasOnly]

@[simp] theorem Cost.score_bytesOnly (cost : Cost) :
    cost.score Weights.bytesOnly = cost.bytes := by
  simp [Cost.score, Weights.bytesOnly]

@[simp] theorem Cost.score_zero (weights : Weights) :
    Cost.zero.score weights = 0 := by
  simp [Cost.score, Cost.zero]

theorem Cost.score_add (a b : Cost) (weights : Weights) :
    (a.add b).score weights = a.score weights + b.score weights := by
  simp [Cost.score, Cost.add, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm]

-- The argument to `push` is the immediate width minus one: 0 means PUSH1,
-- and 31 means PUSH32. PUSH0 is a separate encoding.
inductive PushEncoding where
  | push0
  | push (widthMinusOne : Fin 32)
  deriving DecidableEq, Repr

def PushEncoding.cost : PushEncoding → Cost
  | .push0 => ⟨2, 1⟩
  | .push widthMinusOne => ⟨3, widthMinusOne.val + 2⟩

-- A supplied cost model can represent other instruction sets or estimates.
structure PrimitiveCosts where
  swap : Cost
  dup : Cost
  pop : Cost
  push : Value → Cost
  load : VarId → Cost

-- The caller supplies the encodings actually used by the emitter. This is
-- a cost model, so it does not prove that a PUSH encoding encodes its value.
-- LOAD consists of an address PUSH followed by MLOAD. MLOAD costs 3 gas here;
-- the memory expansion charge is outside this static model.
def PrimitiveCosts.evm (pushEncoding : Value → PushEncoding)
    (loadAddressEncoding : VarId → PushEncoding) : PrimitiveCosts where
  swap := ⟨3, 1⟩
  dup := ⟨3, 1⟩
  pop := ⟨2, 1⟩
  push value := (pushEncoding value).cost
  load id := (loadAddressEncoding id).cost.add ⟨3, 1⟩

-- The C++ shuffler estimates each LOAD at 6 gas, even when its address uses
-- PUSH0. The encoded byte cost still comes from the supplied address width.
def PrimitiveCosts.cppEstimate (pushEncoding : Value → PushEncoding)
    (loadAddressEncoding : VarId → PushEncoding) : PrimitiveCosts :=
  { PrimitiveCosts.evm pushEncoding loadAddressEncoding with
    load := fun id => ⟨6, (loadAddressEncoding id).cost.bytes + 1⟩ }

def traceCost (costs : PrimitiveCosts) : Trace spills source target → Cost
  | .Lit _ => Cost.zero
  | .Swap _ _ _ _ trace => (traceCost costs trace).add costs.swap
  | .Dup _ _ _ _ trace => (traceCost costs trace).add costs.dup
  | .Pop _ trace => (traceCost costs trace).add costs.pop
  | .Push value _ trace => (traceCost costs trace).add (costs.push value)
  | .Load id _ trace => (traceCost costs trace).add (costs.load id)

theorem traceCost_concat (costs : PrimitiveCosts)
    (first : Trace spills source middle) (second : Trace spills middle target) :
    traceCost costs (first.concat second) =
      (traceCost costs first).add (traceCost costs second) := by
  induction second <;> simp_all [Trace.concat, traceCost, Cost.add_assoc]

theorem score_concat (costs : PrimitiveCosts) (weights : Weights)
    (first : Trace spills source middle) (second : Trace spills middle target) :
    (traceCost costs (first.concat second)).score weights =
      (traceCost costs first).score weights + (traceCost costs second).score weights := by
  rw [traceCost_concat, Cost.score_add]

def Cost.AtMost (a b : Cost) : Prop := a.gas ≤ b.gas ∧ a.bytes ≤ b.bytes

-- At least one component must be strictly less for dominance.
def Cost.Dominates (a b : Cost) : Prop :=
  a.AtMost b ∧ (a.gas < b.gas ∨ a.bytes < b.bytes)

instance (a b : Cost) : Decidable (a.AtMost b) := by
  unfold Cost.AtMost
  infer_instance

instance (a b : Cost) : Decidable (a.Dominates b) := by
  unfold Cost.Dominates
  infer_instance

theorem Cost.score_le_of_atMost {a b : Cost} (weights : Weights) (h : a.AtMost b) :
    a.score weights ≤ b.score weights := by
  exact Nat.add_le_add (Nat.mul_le_mul_left weights.gas h.1)
    (Nat.mul_le_mul_left weights.bytes h.2)

theorem Cost.score_lt_of_dominates {a b : Cost} (weights : Weights)
    (hgas : 0 < weights.gas) (hbytes : 0 < weights.bytes) (h : a.Dominates b) :
    a.score weights < b.score weights := by
  rcases h with ⟨⟨hgas_le, hbytes_le⟩, hgas_lt | hbytes_lt⟩
  · have hg := Nat.mul_lt_mul_of_pos_left hgas_lt hgas
    have hb := Nat.mul_le_mul_left weights.bytes hbytes_le
    dsimp [Cost.score]
    omega
  · have hg := Nat.mul_le_mul_left weights.gas hgas_le
    have hb := Nat.mul_lt_mul_of_pos_left hbytes_lt hbytes
    dsimp [Cost.score]
    omega

-- Source, target, and spill set are fixed by the Trace type. The remaining
-- restrictions fix the additions and exclude POP from every comparison.
def Eligible (missing : Multiset Value) (trace : Trace spills source target) : Prop :=
  trace.noPop ∧ trace.additions = missing

def ParetoOptimal (costs : PrimitiveCosts) (missing : Multiset Value)
    (trace : Trace spills source target) : Prop :=
  Eligible missing trace ∧
    ∀ other : Trace spills source target, Eligible missing other →
      ¬(traceCost costs other).Dominates (traceCost costs trace)

def WeightedOptimal (costs : PrimitiveCosts) (weights : Weights)
    (missing : Multiset Value) (trace : Trace spills source target) : Prop :=
  Eligible missing trace ∧
    ∀ other : Trace spills source target, Eligible missing other →
      (traceCost costs trace).score weights ≤ (traceCost costs other).score weights

-- Generation compares all final stacks. The source, spill set, and additions
-- remain fixed, and every comparison still excludes POP.
def GenerationParetoOptimal (costs : PrimitiveCosts) (missing : Multiset Value)
    (trace : Trace spills source target) : Prop :=
  Eligible missing trace ∧
    ∀ (result : Stack) (other : Trace spills source result), Eligible missing other →
      ¬(traceCost costs other).Dominates (traceCost costs trace)

def GenerationWeightedOptimal (costs : PrimitiveCosts) (weights : Weights)
    (missing : Multiset Value) (trace : Trace spills source target) : Prop :=
  Eligible missing trace ∧
    ∀ (result : Stack) (other : Trace spills source result), Eligible missing other →
      (traceCost costs trace).score weights ≤ (traceCost costs other).score weights

theorem weightedOptimal_gasOnly_iff (costs : PrimitiveCosts)
    (missing : Multiset Value) (trace : Trace spills source target) :
    WeightedOptimal costs Weights.gasOnly missing trace ↔
      Eligible missing trace ∧
        ∀ other : Trace spills source target, Eligible missing other →
          (traceCost costs trace).gas ≤ (traceCost costs other).gas := by
  simp only [WeightedOptimal, Cost.score_gasOnly]

theorem weightedOptimal_bytesOnly_iff (costs : PrimitiveCosts)
    (missing : Multiset Value) (trace : Trace spills source target) :
    WeightedOptimal costs Weights.bytesOnly missing trace ↔
      Eligible missing trace ∧
        ∀ other : Trace spills source target, Eligible missing other →
          (traceCost costs trace).bytes ≤ (traceCost costs other).bytes := by
  simp only [WeightedOptimal, Cost.score_bytesOnly]

-- Strictly positive weights exclude every dominated trace. At an endpoint,
-- a trace can tie in the measured component and lose in the ignored one.
theorem weightedOptimal_paretoOptimal (costs : PrimitiveCosts) (weights : Weights)
    (missing : Multiset Value) (trace : Trace spills source target)
    (hgas : 0 < weights.gas) (hbytes : 0 < weights.bytes)
    (h : WeightedOptimal costs weights missing trace) :
    ParetoOptimal costs missing trace := by
  refine ⟨h.1, ?_⟩
  intro other he hdom
  exact Nat.not_le_of_gt (Cost.score_lt_of_dominates weights hgas hbytes hdom)
    (h.2 other he)

theorem generationWeightedOptimal_generationParetoOptimal
    (costs : PrimitiveCosts) (weights : Weights)
    (missing : Multiset Value) (trace : Trace spills source target)
    (hgas : 0 < weights.gas) (hbytes : 0 < weights.bytes)
    (h : GenerationWeightedOptimal costs weights missing trace) :
    GenerationParetoOptimal costs missing trace := by
  refine ⟨h.1, ?_⟩
  intro result other he hdom
  exact Nat.not_le_of_gt (Cost.score_lt_of_dominates weights hgas hbytes hdom)
    (h.2 result other he)

end Shuffler.Optimality
