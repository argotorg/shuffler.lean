module

public import Lift.Pilot.Slot
public import Lift.Pilot.IsRetainedSpec

@[expose] public section

/-! The L3 specification of `Emission.pop` (`shuffler.zig`, `noinline fn pop(self: *Emission)
AssertionError!void`), with the functions that it inlines:

    noinline fn pop(self: *Emission) AssertionError!void {
        const top = self.stack.topOffset();         // size -% 1
        try self.stack.pop();
        self.mapping.pop(top);
    }
    inline fn pop(self: *Stack) AssertionError!void {       // Stack
        try assert(self.size != 0);
        self.size -= 1;
        try self.record(.pop, 0, .junk);
    }
    inline fn record(self: *Stack, kind, depth, slot) AssertionError!void {
        try assert(self.trace_size < max_trace_size);
        const op = &self.trace[self.trace_size];
        op.kind = kind;
        op.depth = @truncate(depth);
        op.slot = slot;
        self.trace_size += 1;
    }
    inline fn pop(self: *Mapping, top: usize) void {        // Mapping
        if (self.destination_of[top].unwrap()) |destination| self.position_of[destination] = .none;
    }

The assembly `.Lshuffler.Emission.pop` (`Lift/Level3/data/pilot.s`) stores `size - 1` before it tests
`trace_size`, so the error of a full trace leaves `size` one lower. `run` has this state. -/

namespace Lift.Pilot.PopSpec

open Lift.Pilot
open Lift.Pilot.IsRetainedSpec (none64)

/-- `ShuffleOp` (`shuffler.zig` line 144, `extern struct`, 12 bytes, types.json `shuffler.ShuffleOp`):
`kind: u8` at 0, `depth: u8` at 1, 2 bytes of padding, `slot: StackSlot` at 4. The padding `pad` is
memory that the function does not write. A `kind` is any byte: memory can hold each bit pattern. -/
structure ShuffleOp where
  kind : BitVec 8
  depth : BitVec 8
  pad : BitVec 16
  slot : Slot
deriving DecidableEq, Inhabited

/-- `StackSlot.junk` (`shuffler.zig` line 94): payload 0, kind `junk` (1), opcode 5, padding 0. -/
def junk : Slot := ⟨0, 1, 5, 0⟩

/-- The result `AssertionError!void`: `ok`, or the error `AssertionFailed`. -/
inductive Assert where
  | ok
  | failed
deriving DecidableEq

/-- The memory that the function reads and writes. `size`, `traceSize` are the fields `stack.size`,
`stack.trace_size` of the `Emission`. `trace` is `*stack.trace`, the array `[10240]ShuffleOp`.
`dest`, `pos` are `mapping.destination_of` and `mapping.position_of`, the arrays `[1024]usize` of the
`Mapping` at `mapping`; an entry is an `OptionalOffset`, a word whose `none` is all ones
(`IsRetainedSpec.none64`). The function reads `dest` and writes `pos`. -/
structure In where
  size : BitVec 64
  traceSize : BitVec 64
  trace : Vector ShuffleOp 10240
  dest : Vector (BitVec 64) 1024
  pos : Vector (BitVec 64) 1024

/-- The result and the memory after the call: the fields and arrays that the function writes. -/
structure Out where
  res : Assert
  size : BitVec 64
  traceSize : BitVec 64
  trace : Vector ShuffleOp 10240
  pos : Vector (BitVec 64) 1024

/-- L3. With `size = 0`: `failed`, no change. Else `size` is lowered by one; with
`traceSize ≥ 10240`: `failed`, nothing else changes. Else the element `trace[traceSize]` gets kind
2 (`pop`), depth 0 and the junk slot (its padding stays), `traceSize` is raised by one, and, if
`dest[size - 1]` is a destination `d`, `pos[d]` is `none`; the result is `ok`. The result is `none`
(no value) only outside the contract: where the code would read `dest` or write `pos` outside its
1024 entries. -/
def run (x : In) : Option Out :=
  if x.size = 0 then some ⟨.failed, x.size, x.traceSize, x.trace, x.pos⟩
  else if h : x.traceSize.toNat < 10240 then
    let trace := x.trace.set x.traceSize.toNat
      { x.trace[x.traceSize.toNat] with kind := 2, depth := 0, slot := junk } h
    if hs : (x.size - 1).toNat < 1024 then
      let d := x.dest[(x.size - 1).toNat]
      if d = none64 then some ⟨.ok, x.size - 1, x.traceSize + 1, trace, x.pos⟩
      else if hd : d.toNat < 1024 then
        some ⟨.ok, x.size - 1, x.traceSize + 1, trace, x.pos.set d.toNat none64 hd⟩
      else none
    else none
  else some ⟨.failed, x.size - 1, x.traceSize, x.trace, x.pos⟩

/-- The contract. When the code goes on to `Mapping.pop` (`size ≠ 0` and `traceSize < 10240`), the
release build has no bounds check, so: `size ≤ 1024` (else `destination_of[size - 1]` is outside the
array), and `destination_of[size - 1]` is `none` or a position below 1024 (else
`position_of[destination]` is outside the array). The code tests the other cases itself. -/
def C (x : In) : Prop :=
  x.size ≠ 0 → x.traceSize.toNat < 10240 →
    x.size.toNat ≤ 1024 ∧ ∀ h : (x.size - 1).toNat < 1024,
      x.dest[(x.size - 1).toNat] = none64 ∨ x.dest[(x.size - 1).toNat].toNat < 1024

theorem total : ∀ x, C x → ∃ y, run x = some y := by
  intro x hC
  by_cases hz : x.size = 0
  · simp only [run, hz, ↓reduceIte, Option.some.injEq, exists_eq']
  by_cases ht : x.traceSize.toNat < 10240
  · obtain ⟨hs, hd⟩ := hC hz ht
    have hs' : (x.size - 1).toNat < 1024 := by bv_omega
    have hd' := hd hs'
    by_cases hn : x.dest[(x.size - 1).toNat] = none64
    · simp only [run, hz, ht, hs', hn, ↓reduceIte, ↓reduceDIte, Option.some.injEq, exists_eq']
    · have hlt : x.dest[(x.size - 1).toNat].toNat < 1024 := hd'.resolve_left hn
      simp only [run, hz, ht, hs', hn, hlt, ↓reduceIte, ↓reduceDIte, Option.some.injEq, exists_eq']
  · simp only [run, hz, ht, ↓reduceIte, ↓reduceDIte, Option.some.injEq, exists_eq']

end Lift.Pilot.PopSpec
