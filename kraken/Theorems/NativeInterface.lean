module

public import FlatShuffler.Unit.Plan.Defs
import all FlatShuffler.Unit.Plan.Defs

@[expose] public section

/-!
# Native planner object and call memory

These are the memory records used by the assembly proofs and the review contract.
They describe caller-owned memory, not the function's local variables.

The object record follows the C++ members: `src` and `tgt` are addresses, `sourceSize` and
`targetSize` are slot counts, `spl` is the spill-byte address, `allowed` is the spilling
policy byte, `drp` is the dropped-byte address, and `saw` is the wildcard-copy byte.
`sw` and `tw` are the active source and target words at those addresses.

The call record adds the output-buffer addresses and contents. Its `p` field is
the object record. `ops` contains every operation-buffer record; `traceLength`
selects the prefix that belongs to the current trace. The memory views use `∗`,
so every owned region is disjoint. Padding bytes are outside these views.
-/

namespace FlatShuffler.Unit

open FlatShuffler.Sep

-- The members of a `Planner` and the words that `m_source` and `m_target` point to.
structure PlannerObjectMemory where
  src : Addr
  sourceSize : Word
  tgt : Addr
  targetSize : Word
  spl : Addr
  allowed : BitVec 8
  drp : Addr
  saw : BitVec 8
  sw : List Word
  tw : List Word

structure PlannerObjectMemory.Ok (p : PlannerObjectMemory) : Prop where
  sourceSizeFitsBuffer : p.sourceSize.toNat ≤ maxStackSize
  targetSizeFitsBuffer : p.targetSize.toNat ≤ maxStackSize
  sw : p.sw.length = p.sourceSize.toNat
  tw : p.tw.length = p.targetSize.toNat

def plannerObjectOwnedMemory (P : Addr) (p : PlannerObjectMemory) : MProp 64 :=
  Wd P p.src ∗ Wd (P + 8#64) p.sourceSize ∗ Wd (P + 16#64) p.tgt ∗ Wd (P + 24#64) p.targetSize
    ∗ Wd (P + 32#64) p.spl ∗ B8 (P + 40#64) p.allowed ∗ Wd (P + 48#64) p.drp ∗ B8 (P + 56#64) p.saw
    ∗ Arr p.src p.sw ∗ Arr p.tgt p.tw

-- The flat `Planner`.
def PlannerObjectMemory.fl (p : PlannerObjectMemory) : Flat.Planner :=
  ⟨vec (p.sw.map StackSlot.ofWord), p.sourceSize, vec (p.tw.map StackSlot.ofWord), p.targetSize, p.allowed != 0#8⟩


structure PlannerCallMemory where
  p : PlannerObjectMemory
  dataPtr : Addr
  opsPtr : Addr
  sourcesPtr : Addr
  countPtr : Addr
  spillCount : Nat
  spills : BitVec 32 → BitVec 8
  dropped : Vector (BitVec 8) maxStackSize
  data : Vector Word maxStackSize
  ops : List OpR
  traceLength : Nat
  sources : Vector Word maxStackSize
  count : Word

def PlannerCallMemory.dataCapacity (g : PlannerCallMemory) : Nat :=
  max g.p.sourceSize.toNat g.p.targetSize.toNat

structure PlannerCallMemory.Ok (g : PlannerCallMemory) : Prop where
  planner : g.p.Ok
  spillCount : g.spillCount ≤ 2 ^ 32
  sourceIds : ∀ i ∈ splIds g.p.sw, i < g.spillCount
  targetIds : ∀ i ∈ splIds g.p.tw, i < g.spillCount
  ops : g.ops.length = 6 * g.p.targetSize.toNat + 4 * g.p.sourceSize.toNat
  traceLength : g.traceLength ≤ g.ops.length

def plannerCallOwnedMemory (P : Addr) (g : PlannerCallMemory) : MProp 64 :=
  plannerObjectOwnedMemory P g.p ∗ Spl g.p.spl g.spills (List.range g.spillCount)
    ∗ Bs g.p.drp (g.dropped.toList.take g.p.sourceSize.toNat)
    ∗ Arr g.dataPtr (g.data.toList.take g.dataCapacity)
    ∗ Ops g.opsPtr 0 g.ops ∗ Arr g.sourcesPtr (g.sources.toList.take g.p.targetSize.toNat)
    ∗ Wd g.countPtr g.count

def PlannerCallMemory.state (g : PlannerCallMemory) : Flat.PSt :=
  ⟨g.spills, g.dropped, g.p.saw != 0#8, g.data.map StackSlot.ofWord,
    (g.ops.take g.traceLength).map OpR.op, g.sources⟩


end FlatShuffler.Unit
