module

public import Lift.Pilot.Slot
public import Lift.Pilot.IsRetainedSpec
public import Lift.Pilot.ShallowestSpec
public import Lift.Pilot.PopSpec

@[expose] public section

/-! The L3 specification of `MappingBuilder.closestCopy` (`shuffler.zig`, lines 365 to 383), with the
functions that it inlines:

    noinline fn closestCopy(self: *const MappingBuilder, target_offset: usize,
                            location: CopyLocation) OptionalOffset {
        const in_wildcard_slots = location == .in_wildcard_slots;
        var best: OptionalOffset = .none;
        for (0..self.source_size) |i| {
            if (self.sourceAt(i).eql(self.targetAt(target_offset)) and
                self.mappable(i) and
                self.inWildcardSlot(i) == in_wildcard_slots)
            {
                if (best == .none or absDiff(i, target_offset) <= absDiff(@backingInt(best), target_offset))
                    best = .some(i);
            }
        }
        return best;
    }
    inline fn mappable(self, s) bool { return self.dropped[s] == 0 and self.mapping.destinationOf(s) == .none; }
    inline fn inWildcardSlot(self, s) bool { return s < self.target_size and self.isWildcardTarget(s); }
    inline fn isWildcardTarget(self, t) bool { return self.targetAt(t).isJunk(); }

The L3 inputs are the source slots `src` (the slice `source[0 .. source_size]`), the target slots `tgt`
(`target[0 .. target_size]`), the array `dropped`, the table `destination_of` of the mapping, the target
offset `t` and the location byte. The assembly `.Lshuffler.MappingBuilder.closestCopy`
(`Lift/Level3/data/pilot.s`) reads `source_size` once, then in each iteration the pointers `source`,
`target`, the slots `target[t]` and `source[i]` as 8-byte words, and then `dropped[i]`,
`destination_of[i]`, `target_size` and the `kind` byte of `target[i]`. -/

namespace Lift.Pilot.ClosestCopySpec

open Lift.Pilot
open Lift.Pilot.IsRetainedSpec (none64)
open Lift.Pilot.ShallowestSpec (eql)
open Lift.Pilot.PopSpec (junk)

/-- The contract. `source_size ≤ 1024`: the code reads `dropped[i]` and `destination_of[i]` for each
`i` below `source_size` that passes the tests before, with no test of `i` (`pilot.s`, the loads
`cmpb $0, (%r14,%r9)` and `cmpq $-1, (%r14,%r9,8)`), and both arrays have 1024 entries
(`shuffler.zig` line 53 `max_stack_size = 1024`, line 306 `dropped: *const [max_stack_size]u8`, line
180 `destination_of: [max_stack_size]OptionalOffset`). The target offset is below `target_size` unless
the source is empty: the code reads `target[t]` in each iteration with no test. -/
def C (src tgt : List Slot) (t : Nat) : Prop :=
  src.length ≤ 1024 ∧ (src = [] ∨ t < tgt.length)

instance (src tgt : List Slot) (t : Nat) : Decidable (C src tgt t) := by
  unfold C; infer_instance

/-- `absDiff` (`shuffler.zig` line 346). -/
def absDiff (a b : Nat) : Nat := if a > b then a - b else b - a

/-- `inWildcardSlot` (`shuffler.zig` line 342): the offset `i` is below `target_size` and the target
slot at `i` is junk. The list access `tgt[i]?` is `none` for `i ≥ target_size`. -/
def inWildcardSlot (tgt : List Slot) (i : Nat) : Bool :=
  tgt[i]?.any fun u => u.kind == junk.kind

/-- L3: `closestCopy` of the target offset `t` at the location `loc`. The scan takes, over the source
offsets `i` in increasing order, each slot that is `eql` to `tgt[t]`, is mappable (not dropped and
without a destination) and has `inWildcardSlot` equal to `loc ≠ 0`; it keeps the first such `i`, then
each later `i` that is at most as far from `t` as the one kept. The result is the offset kept, or
`none` (`IsRetainedSpec.none64`). The code reads `loc` as the byte `dl` and tests `loc ≠ 0` (`testb
%dl,%dl; setne`), so each byte is accepted; for the values 0 and 1 of `CopyLocation` this is
`location == .in_wildcard_slots`. The result is `none` (no value) outside `C`. The list
`(List.finRange 1024).zip src` is the pairs `(i, src[i])`, each `i` below `source_size`. -/
def run (src tgt : List Slot) (dropped : Vector (BitVec 8) 1024)
    (dest : Vector (BitVec 64) 1024) (t : Nat) (loc : BitVec 8) : Option (BitVec 64) :=
  if C src tgt t then
    some (((List.finRange 1024).zip src).foldl (fun best (i, s) =>
      if tgt[t]?.any (eql s) ∧ dropped[i] = 0 ∧ dest[i] = none64 ∧
          inWildcardSlot tgt i = decide (loc ≠ 0) then
        if best = none64 ∨ absDiff i t ≤ absDiff best.toNat t then BitVec.ofNat 64 i else best
      else best) none64)
  else none

/-- Each admitted input: `run` gives a value. -/
theorem total (src tgt : List Slot) (dropped : Vector (BitVec 8) 1024)
    (dest : Vector (BitVec 64) 1024) (t : Nat) (loc : BitVec 8) (h : C src tgt t) :
    ∃ y, run src tgt dropped dest t loc = some y := by
  simp only [run, h, ↓reduceIte, Option.some.injEq, exists_eq']

end Lift.Pilot.ClosestCopySpec
