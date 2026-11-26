module

public import Lift.Pilot.Slot
public import Lift.Pilot.IsRetainedSpec
public import Lift.Pilot.ShallowestSpec
public import Lift.Pilot.MapSpec

@[expose] public section

/-! The L3 specification of `MappingBuilder.mapInPlace` (`shuffler.zig`, lines 385 to 391), with the
functions that it inlines:

    noinline fn mapInPlace(self: *MappingBuilder) AssertionError!void {
        for (0..self.commonSize()) |j| {
            if (self.sourceAt(j).eql(self.targetAt(j)) and self.mappable(j)) {
                try self.map(j, j);
            }
        }
    }
    inline fn commonSize(self) usize { return @min(self.source_size, self.target_size); }
    inline fn mappable(self, s) bool { return self.dropped[s] == 0 and self.mapping.destinationOf(s) == .none; }

The call `map(j, j)` is `MapSpec.run`. The L3 inputs are the source slots `src` (`source[0 ..
source_size]`), the target slots `tgt` (`target[0 .. target_size]`), the array `dropped`, and the two
tables `destination_of` and `position_of` of the mapping. The result is the error code of
`AssertionError!void` (`0` for `ok`, `1` for `AssertionFailed`) and the two tables after the call.
The assembly `.Lshuffler.MappingBuilder.mapInPlace` (`Lift/Level3/data/pilot.s`) reads `source_size`
and `target_size` once, then in each iteration the pointers `source`, `target`, the slots `source[j]`
and `target[j]` as 8-byte words, and then `dropped[j]` and `destination_of[j]`; it calls
`.Lshuffler.MappingBuilder.map` with `rsi = rdx = j` and returns 1 if the result is not 0. The code
does not call `closestCopy`. -/

namespace Lift.Pilot.MapInPlaceSpec

open Lift.Pilot
open Lift.Pilot.IsRetainedSpec (none64)
open Lift.Pilot.ShallowestSpec (eql)

/-- The contract: `min source_size target_size ≤ 1024`. The code reads `dropped[j]` and
`destination_of[j]` for each `j` below the minimum, and `map(j, j)` reads `position_of[j]`, with no
test of `j` (`pilot.s`: `cmpb $0, (%rax,%r14)`, `cmpq $-1, (%rax,%r14,8)`), and the three arrays have
1024 entries (`shuffler.zig` line 53 `max_stack_size = 1024`, line 306 `dropped: *const
[max_stack_size]u8`, line 180 `destination_of: [max_stack_size]OptionalOffset`, and `position_of` the
same). No other fact is needed: the source and the target hold at least the minimum number of slots
by their sizes. -/
def C (src tgt : List Slot) : Prop :=
  min src.length tgt.length ≤ 1024

instance (src tgt : List Slot) : Decidable (C src tgt) := by
  unfold C; infer_instance

/-- The loop of `mapInPlace` over the triples `(j, src[j], tgt[j])`, with the tables `dest` and
`pos` as they are at the start of the iteration. A slot in place (`eql`) that is mappable (not dropped
and without a destination) is mapped by `MapSpec.run`, which gives the code and the new tables; a code
that is not 0 ends the loop with its result and tables (`try`). The end of the list is `ok`. -/
def loop (dropped : Vector (BitVec 8) 1024) :
    List (Fin 1024 × Slot × Slot) → Vector (BitVec 64) 1024 → Vector (BitVec 64) 1024 →
      Option (BitVec 16 × Vector (BitVec 64) 1024 × Vector (BitVec 64) 1024)
  | [], dest, pos => some (0, dest, pos)
  | (j, s, u) :: rest, dest, pos =>
    if eql s u ∧ dropped[j] = 0 ∧ dest[j] = none64 then
      (MapSpec.run dropped dest pos j j).bind fun y =>
        if y.1 = 0 then loop dropped rest y.2.1 y.2.2 else some y
    else loop dropped rest dest pos

/-- L3: `mapInPlace` with the array `dropped` and the tables `dest` (`destination_of`) and `pos`
(`position_of`). It maps each source offset `j` below the minimum of the two sizes in order. The list
`(List.finRange 1024).zip (src.zip tgt)` is the triples `(j, src[j], tgt[j])`, each `j` below the
minimum, which is at most 1024 in `C`. The result is the error code and the two tables after the
call. The result is `none` (no value) outside `C`. -/
def run (src tgt : List Slot) (dropped : Vector (BitVec 8) 1024)
    (dest pos : Vector (BitVec 64) 1024) :
    Option (BitVec 16 × Vector (BitVec 64) 1024 × Vector (BitVec 64) 1024) :=
  if C src tgt then
    loop dropped ((List.finRange 1024).zip (src.zip tgt)) dest pos
  else none

/-- `loop` gives a value for each list: each index `j` is below 1024, so `MapSpec.run` gives a value. -/
theorem loop_total (dropped : Vector (BitVec 8) 1024) :
    ∀ (l : List (Fin 1024 × Slot × Slot)) (dest pos : Vector (BitVec 64) 1024),
      ∃ y, loop dropped l dest pos = some y
  | [], dest, pos => ⟨(0, dest, pos), by simp only [loop]⟩
  | (j, s, u) :: rest, dest, pos => by
    simp only [loop]
    split
    · obtain ⟨y, hy⟩ := MapSpec.total dropped dest pos j j ⟨j.2, j.2⟩
      rw [hy]
      simp only [Option.bind_some]
      split
      · exact loop_total dropped rest y.2.1 y.2.2
      · exact ⟨y, rfl⟩
    · exact loop_total dropped rest dest pos

/-- Each admitted input: `run` gives a value. -/
theorem total (src tgt : List Slot) (dropped : Vector (BitVec 8) 1024)
    (dest pos : Vector (BitVec 64) 1024) (h : C src tgt) :
    ∃ y, run src tgt dropped dest pos = some y := by
  simp only [run, h, ↓reduceIte]
  exact loop_total dropped _ dest pos

end Lift.Pilot.MapInPlaceSpec
