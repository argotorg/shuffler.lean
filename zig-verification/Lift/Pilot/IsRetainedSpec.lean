module

@[expose] public section

/-! The L3 specification of `Planner.isRetained` (`shuffler.zig`, `noinline fn isRetained(mapping:
*const Mapping, source_offset: usize) bool`, whose body is `mapping.destinationOf(source_offset) !=
.none`). The L3 inputs are the table `destination_of` of the mapping and the index. The assembly
`.Lshuffler.Planner.isRetained` (`Lift/Level3/data/pilot.s`) is `cmpq $-1, (%rdi,%rsi,8); setne %al;
retq`: one 8-byte read at `rdi + 8 * rsi`, and the result is the byte `al`. -/

namespace Lift.Pilot.IsRetainedSpec

/-- `OptionalOffset.none`: the `usize` `maxInt`, the 64-bit word of all ones, which is `-1` as a
signed word (`shuffler.zig` line 132: `none = std.math.maxInt(usize)`). -/
def none64 : BitVec 64 := BitVec.allOnes 64

/-- L3: `isRetained` of the table `dest` at the index `i`: whether the entry `dest[i]` is not `none`.
The entry is a word, so each entry is a value of `OptionalOffset` (`shuffler.zig` line 131: the enum
is `enum(usize)` with the value `none` and `_`, so each word is a valid value). The result is `none`
only outside the contract, where the index is not in the table. -/
def run (dest : Vector (BitVec 64) 1024) (i : Nat) : Option Bool :=
  if h : i < 1024 then some (decide (dest[i] ≠ none64)) else none

/-- The contract: the index is below 1024. `destination_of` has 1024 entries (`shuffler.zig` line
180 `destination_of: [max_stack_size]OptionalOffset`, and line 53 `max_stack_size = 1024`), and the
machine code reads `rdi + 8 * rsi` with no test of `rsi` (`cmpq $-1, (%rdi,%rsi,8)`, the first
instruction of the function). No other fact is needed: the table has no invariant (see `run`). -/
def C (_ : Vector (BitVec 64) 1024) (i : Nat) : Prop := i < 1024

theorem total : ∀ dest i, C dest i → ∃ y, run dest i = some y := by
  intro dest i h
  have hi : i < 1024 := h
  exact ⟨decide (dest[i] ≠ none64), by simp [run, hi]⟩

end Lift.Pilot.IsRetainedSpec
