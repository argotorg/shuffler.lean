module

public import Lift.Pilot.Call
public import Lift.Trusted.Encode
public import Lift.Pilot.Encode
public import Lift.Pilot.Slot
public import Lift.Shuffler.Spec
public import Lift.Shuffler.Code

@[expose] public section

/-! The trusted statement of the Zig entry function `shuffle` (`solidity_shuffler_shuffle`, Z:1363-1369;
Z is `Lift/LLVM/data/shuffler/src/shuffler.zig`), task K4. Not proved. L3 is `Lift.Shuffler.Spec.run`.
Decisions: D27 (the workspace is one object), D25 and D31 (the writable objects are apart from the other
objects), D38 (`Fn.CallB`), D42 and D44 (the conditions K1 to K5).

The code is `Lift.Shuffler.Code.code`: the whole `Lift/LLVM/data/shuffler/shuffler.s` (31 functions),
made by `Lift/P1/Test/shuffler_layout.py`. The record `Shuffle` (Z:1241-1263, types.json type 52,
96 bytes, alignment 8), as the code reads and writes it:

    offset  field                    access of the code (shuffler.s)
    0       source                   read 8
    8       source_size              read 8 (cmpq $1024,8(%rdi), line 19)
    16      target                   read 8
    24      target_size              read 8 (line 21)
    32      spills                   read 8
    40      workspace                read 8
    48      reachable_stack_depth    read 8 (cmpq $1,48(%rdi), line 16)
    56      spilling_allowed, pad 7  read 1 (movb 56(%rbx),%al; andb $1,%al, lines 37-38)
    64      stack                    write 8 after Done (lines 281, 315)
    72      trace                    write 8 after Done (lines 283, 317)
    80      trace_size               write 8 after Done (lines 285, 319)
    88      sources                  write 8 after Done (lines 286, 321)

The result is the `Status` (`enum(u32)`, types.json type 60) in `eax` (`movl %ebp,%eax`, line 325). -/

namespace Lift.Shuffler.Statement

open Lift.P2.Total Lift.Trusted Lift.Pilot Lift.Shuffler.Spec

/-- `shuffle` in `Lift.Shuffler.Code.code`: the entry `0x100000` (label `solidity_shuffler_shuffle`,
the first instruction of the code), the room 416 and the result in `eax`, 32 bits. The room is the
deepest stack of the call tree, below the return word, measured on each path of the control flow of
each function (pushes, pops, `subq` and `addq` of `rsp`; the code has no other write of `rsp`, no
access below `rsp`, no indirect jump and no recursion). The deepest chain, with the bytes of the
caller at the call and the return word: `shuffle` 88 (6 pushes, `subq $24`, 2 pushes; line 91) and 8;
`Planner.run` 72 (6 pushes, `subq $24`; line 583) and 8; `Planner.resolve` 104 (6 pushes, `subq $56`;
line 710) and 8; `Planner.classify` 56 (7 pushes; line 1919) and 8;
`Planner.hasOtherRetainedCopy` 56 (7 pushes; line 2067) and 8; `Planner.isRetained` 0. So
96 + 80 + 112 + 64 + 64 = 416. The lines are those of `shuffler.s`. -/
def shuffle : Fn := ⟨Lift.Shuffler.Code.code, 0x100000, 416, .W32⟩

/-- The entry is the label `solidity_shuffler_shuffle`. -/
theorem shuffle_entry :
    Lift.Shuffler.Code.code.labels.label "solidity_shuffler_shuffle" = shuffle.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The number of bytes of the `Workspace` (types.json type 54; `solidity_shuffler_workspaceSize`). -/
def workspaceSize : Nat := 357672

/-- The addresses and the bytes of a call that `In` does not give. -/
structure Setup where
  /-- The address of the record `Shuffle`, the argument in `rdi`. -/
  self : BitVec 64
  /-- `source`: the address of the source words. -/
  src : BitVec 64
  /-- `target`: the address of the target words. -/
  tgt : BitVec 64
  /-- `spills`: the address of the spill buffer. -/
  spills : BitVec 64
  /-- `workspace`: the address of the `Workspace`. -/
  ws : BitVec 64
  /-- The word at offset 56: `spilling_allowed` in its low byte, the padding (not initialised by C++) in
  the 7 bytes above. -/
  flags : BitVec 64
  /-- The words at offsets 64 to 95 before the call: `stack`, `trace`, `trace_size`, `sources` (any
  value; they are outputs). -/
  outs : Vector (BitVec 64) 4
  /-- The content of the workspace before the call, as words (any value: it needs no initial value,
  Z:1225). -/
  wsWords : Vector (BitVec 64) (workspaceSize / 8)

/-- The words of a list of slots, with their padding. -/
def words (l : List Slot) : List (BitVec 64) := l.map Slot.word

/-- The objects of the call: the 64 input bytes of the record (read-only), its 32 output bytes
(writable), the source and the target words (read-only; each a list of `source_size` and
`target_size` words), the spill buffer (writable) and the workspace (writable). `Separate` of
`Fn.Entry` keeps each writable object apart from each other object; the source, the target and the
input bytes of the record may overlap. `Mem.has` of the source object gives
`src + 8 * source.length ≤ 2^64`, so the word `source_size` is the length; the same for the target. -/
def objects (x : In) (l : Setup) : List Object :=
  [ ⟨l.self, Encode.encode [l.src, BitVec.ofNat 64 x.source.length, l.tgt,
      BitVec.ofNat 64 x.target.length, l.spills, l.ws, x.reach, l.flags], false⟩,
    ⟨l.self + 64, Encode.encode l.outs, true⟩,
    ⟨l.src, Encode.encode (words x.source), false⟩,
    ⟨l.tgt, Encode.encode (words x.target), false⟩,
    ⟨l.spills, Encode.encode x.spills, true⟩,
    ⟨l.ws, Encode.encode l.wsWords, true⟩ ]

/-- The condition of a call that `Fn.Entry` and `objects` do not state. There is no alignment
condition: `readRam` has no alignment check, so one would only narrow the precondition. -/
structure Pre (x : In) (l : Setup) : Prop where
  /-- `spilling_allowed` is bit 0 of the byte at offset 56 (`andb $1`, line 38). -/
  allowed : x.spillingAllowed = l.flags.getLsbD 0

/-- The `Status` code of a result (Z:75): Done 0, Blocked 1, assertion failed 2. -/
def status : Result → BitVec 32
  | .done _ => 0
  | .blocked => 1
  | .assertionFailed => 2

/-- The bytes `[a, a + n)` are in `[b, b + k)`. -/
def Inside (a : BitVec 64) (n : Nat) (b : BitVec 64) (k : Nat) : Prop :=
  b.toNat ≤ a.toNat ∧ a.toNat + n ≤ b.toNat + k

/-- The bytes of the operations `ops` of a trace at `tr` that the caller reads: of operation `i`, at
`tr + 12 i`, the bytes 0 (`kind`) and 1 (`depth`) and the 8 bytes 4 to 11 (`slot`, with its padding);
not the 2 padding bytes 2 and 3 (`ShuffleOp`, Z:144-152, types.json type 32). -/
def opObjects (tr : BitVec 64) (ops : List Op) : List Object :=
  (ops.mapIdx fun i o =>
    [⟨tr + BitVec.ofNat 64 (12 * i), [⟨.W8, o.kind⟩, ⟨.W8, o.depth⟩], false⟩,
      ⟨tr + BitVec.ofNat 64 (12 * i + 4), [⟨.W64, o.slot.word⟩], false⟩]).flatten

/-- The plan `p` after Done, as the caller reads it: the record has at offsets 64 to 95 the pointers
`stack`, `trace`, the length of the trace and the pointer `sources`; at these pointers are the words of
the stack (with their padding), the operations of the trace (`opObjects`) and the source offsets; the
three arrays are inside the workspace. -/
def PlanAt (l : Setup) (p : Plan) (policy : CpuPolicy) (m : DataMem) : Prop :=
  ∃ st tr so : BitVec 64,
    -- the record: `stack`, `trace`, `trace_size`, `sources`
    Mem.has policy m ⟨l.self + 64, Encode.encode [st, tr, BitVec.ofNat 64 p.trace.length, so], false⟩ ∧
    -- `stack[0 .. target_size)`
    Mem.has policy m ⟨st, Encode.encode (words p.stack), false⟩ ∧
    -- `trace[0 .. trace_size)`, bytes 0, 1 and 4 to 11 of each operation
    (∀ o ∈ opObjects tr p.trace, Mem.has policy m o) ∧
    -- `sources[0 .. target_size)`
    Mem.has policy m ⟨so, Encode.encode p.sources, false⟩ ∧
    -- the three arrays are in the workspace
    Inside st (8 * p.stack.length) l.ws workspaceSize ∧
    Inside tr (12 * p.trace.length) l.ws workspaceSize ∧
    Inside so (8 * p.sources.length) l.ws workspaceSize

/-- At the return, for some content `w₁`, `w₂` of the scratch of the attempts (decision D44, K1), L3
gives `y`: the result field is the status of `y`, the spill buffer has the bytes of `y`, and after Done
the record and the workspace have the plan of `y`. -/
def post (x : In) (l : Setup) (policy : CpuPolicy) (r : Field) (m : DataMem) : Prop :=
  ∃ w₁ w₂ y, run x w₁ w₂ = some y ∧
    -- the status in `eax`
    r = ⟨.W32, status y.result⟩ ∧
    -- the spill buffer after the call
    Mem.has policy m ⟨l.spills, Encode.encode y.spills, false⟩ ∧
    -- the plan, only after Done
    ∀ p, y.result = .done p → PlanAt l p policy m

/-- For each input `x` in the contract and each layout `l` that satisfies `Pre`, the call
`shuffle(l.self)` ends and returns the status, the spill bytes and, after Done, the plan of L3. -/
def ShuffleStatement : Prop :=
  ∀ x, C x → ∀ l : Setup, Pre x l →
    shuffle.CallB [⟨.W64, l.self⟩] (objects x l) (post x l)

end Lift.Shuffler.Statement
