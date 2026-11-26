module

public import Lift.P2.Total.PointerGraph

@[expose] public section

namespace Lift.P2.Total.PointerReach

/-- Values reached from input roots by successful reads of pointer fields.
Zero values and cycles are allowed. No read is required to succeed. -/
inductive Reach (memory : DataMem) (roots links : List (BitVec 64)) : BitVec 64 → Prop where
  | root {node : BitVec 64} (member : node ∈ roots) : Reach memory roots links node
  | next {node child offset : BitVec 64} (parent : Reach memory roots links node)
      (member : offset ∈ links)
      (loaded : PointerChain.pointerAt memory (node + offset) = some child) :
      Reach memory roots links child

/-- Every listed field of each reachable node is outside the private frame. -/
structure Guard (privateByte : BitVec 64 → Bool) (memory : DataMem)
    (roots links : List (BitVec 64)) (fields : List PointerChain.Field) : Prop where
  node : ∀ address, Reach memory roots links address →
    ∀ field ∈ fields, PointerChain.PublicRead privateByte (address + field.offset) field.width

theorem Guard.read_field {privateByte : BitVec 64 → Bool} {memory other : DataMem}
    {roots links : List (BitVec 64)} {fields : List PointerChain.Field}
    (guard : Guard privateByte memory roots links fields)
    (visible : hideRam privateByte other = hideRam privateByte memory)
    {address : BitVec 64} (reachable : Reach memory roots links address)
    (field : PointerChain.Field) (member : field ∈ fields) (policy : CpuPolicy) :
    readRam policy (hideRam privateByte memory) (address + field.offset) field.width =
      (readRam policy other (address + field.offset) field.width).mapError
        (fun failure => (failure.1, hideRam privateByte failure.2)) := by
  rw [← visible]
  exact (guard.node address reachable field member).readRam policy other

theorem Guard.next_read {privateByte : BitVec 64 → Bool} {memory other : DataMem}
    {roots links : List (BitVec 64)} {fields : List PointerChain.Field}
    (guard : Guard privateByte memory roots links fields)
    (visible : hideRam privateByte other = hideRam privateByte memory)
    {address child offset : BitVec 64} (reachable : Reach memory roots links address)
    (link : offset ∈ links) (field : PointerChain.Field.mk offset .W64 ∈ fields)
    (policy : CpuPolicy)
    (loaded : readRam policy other (address + offset) .W64 = .ok child) :
    Reach memory roots links child := by
  apply Reach.next reachable link
  rw [← (guard.node address reachable _ field).pointer_eq visible]
  exact PointerChain.pointerAt_of_readRam policy other (address + offset) child loaded

theorem Guard.next_projected {privateByte : BitVec 64 → Bool} {memory : DataMem}
    {roots links : List (BitVec 64)} {fields : List PointerChain.Field}
    (guard : Guard privateByte memory roots links fields)
    {address child offset : BitVec 64} (reachable : Reach memory roots links address)
    (link : offset ∈ links) (field : PointerChain.Field.mk offset .W64 ∈ fields)
    (policy : CpuPolicy)
    (loaded : readRam policy (hideRam privateByte memory) (address + offset) .W64 = .ok child) :
    Reach memory roots links child :=
  guard.next_read (hideRam_idempotent privateByte memory) reachable link field policy loaded

end Lift.P2.Total.PointerReach
