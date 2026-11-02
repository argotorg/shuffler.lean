module

public import Shuffler.Trace
import all Shuffler.Trace
public import FlatShuffler.FlatPlan
import all FlatShuffler.FlatPlan
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Image

@[expose] public section

/-!
# Slot and operation encoding

These are the conversions used by both the review statements and the bridge proofs.
A variable or literal uses all 48 slot bits as its model identity. The native spill
buffer uses only the 32 payload bits. The input assumptions therefore require two
variables with the same payload to have the same slot encoding.

The order of the tests in `decodeStackSlot` is part of the encoding. In particular,
a constant opcode is decoded before a function return label is considered.
-/

namespace ShufflerBridge.Emission

open Shuffler

-- Pack the payload, kind, and opcode into the model's 48-bit identity.
def stackSlotIdentity (s : FlatShuffler.StackSlot) : Nat :=
  s.payload.toNat + 2 ^ 32 * s.kind.toNat + 2 ^ 40 * s.valueOpcode.toNat

def stackSlotFromIdentity (n : Nat) : FlatShuffler.StackSlot :=
  ⟨.ofNat 32 n, .ofNat 8 (n / 2 ^ 32), .ofNat 8 (n / 2 ^ 40)⟩

-- The canonical encoding of a function return label.
def functionReturnLabelSlot : FlatShuffler.StackSlot := ⟨0, FlatShuffler.FunctionReturnLabel, FlatShuffler.Unreachable⟩

-- The value of a slot: a junk slot is a wildcard, a literal or a function call
-- return label is a literal, a function return label is a function return
-- label, and each other slot is a variable. The packed identity of the slot is the
-- literal or the variable id.
def decodeStackSlot (s : FlatShuffler.StackSlot) : Value :=
  if s.kind = FlatShuffler.Junk then .Wildcard
  else if s.valueOpcode = FlatShuffler.Const ∨ s.kind = FlatShuffler.FunctionCallReturnLabel then
    .Lit (Fin.ofNat _ (stackSlotIdentity s))
  else if s.kind = FlatShuffler.FunctionReturnLabel then .FunctionReturnLabel
  else .Var ⟨stackSlotIdentity s⟩

def encodeStackSlot : Value → FlatShuffler.StackSlot
  | .Wildcard => .junk
  | .FunctionReturnLabel => functionReturnLabelSlot
  | .Var id => stackSlotFromIdentity id.val
  | .Lit w => stackSlotFromIdentity w.val

-- The flat model compares encoded slots. The Lean planner compares decoded values.
-- Junk and function return labels must therefore use their canonical encodings.
def StackSlotHasCanonicalEncoding (s : FlatShuffler.StackSlot) : Prop :=
  (s.kind = FlatShuffler.Junk → s = .junk) ∧ (s.kind = FlatShuffler.FunctionReturnLabel → s = functionReturnLabelSlot)

-- Decode the active target slots of the list model.
abbrev decodedTargetStack (e : FlatShuffler.Env) : Stack := e.target.map decodeStackSlot

-- Include spilled variables from the active source and target only. The native
-- spill bytes use the payload as their index. Equal variable payloads must identify
-- equal slot encodings; repeated occurrences of that slot are permitted.
def spilledVariables (e : FlatShuffler.Env) (source : Stack) : SpillSet :=
  ((Finset.range (2 ^ 48)).filter (fun i => FlatShuffler.isSpilled e (stackSlotFromIdentity i) = true ∧
    Value.Var ⟨i⟩ ∈ source ++ decodedTargetStack e)).image VarId.mk

-- One operation of a model trace.
inductive TraceOperation where
  | swap (depth : Nat)
  | dup (depth : Nat)
  | pop
  | push (v : Value)
  | load (id : VarId)

-- The ops of a trace, in order of application.
def traceOperations {spills : SpillSet} {source result : Stack} : Trace spills source result → List TraceOperation
  | .Lit _ => []
  | .Swap idx _ _ _ t => traceOperations t ++ [.swap idx]
  | .Dup idx _ _ _ _ t => traceOperations t ++ [.dup idx]
  | .Pop _ t => traceOperations t ++ [.pop]
  | .Push v _ t => traceOperations t ++ [.push v]
  | .Load id _ t => traceOperations t ++ [.load id]

-- Encode one trace operation. `Op.push` selects Load for a nonconstant Value slot,
-- and Push otherwise.
-- Operation kind 2 is Pop.
def encodeTraceOperation : TraceOperation → FlatShuffler.Op
  | .swap d => .swap d
  | .dup d => .dup d
  | .push v => .push (encodeStackSlot v)
  | .load id => .push (encodeStackSlot (.Var id))
  | .pop => ⟨2, 0, .junk⟩
-- A source index uses all-one bits to represent an absent source.
def decodeOptionalSourceIndex (index : FlatShuffler.Word) : Option Nat :=
  if index = FlatShuffler.Flat.NONE then none else some index.toNat

end ShufflerBridge.Emission
