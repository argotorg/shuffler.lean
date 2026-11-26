module

public import Lift.Trusted.Call
public import Lift.Trusted.Encode
public import Lift.Toys.WalkSpec
public import Lift.Toys.Code

@[expose] public section

/-! The trusted statement of `toyWalk` (`Lift/Toys/data/toy.zig`, `callconv(.c)`). Not proved.

    const Node = extern struct { val: u64, next: ?*const Node };
    export fn toyWalk(head: ?*const Node) u64 {
        var n: u64 = 0;
        var p = head;
        while (p) |q| : (p = q.next) n +%= 1;
        return n;
    }
-/

namespace Lift.Toys.WalkStatement

open Lift.P2.Total Lift.Trusted Lift.Toys.WalkSpec

/-- The record `Node`: 16 bytes, `val` at offset 0, `next` at offset 8. -/
structure Node where
  val : BitVec 64
  next : BitVec 64
deriving DecidableEq

instance : Encode Node where
  encode n := Encode.encode n.val ++ Encode.encode n.next
  decode
    | [a, b] => do return ⟨(← Encode.decode [a]), (← Encode.decode [b])⟩
    | _ => none

/-- `toyWalk` in `Code.code`: the entry `0x1000c5`, no stack room (a leaf with no push), and the
64-bit result in `rax`. -/
def toyWalk : Fn := ⟨Code.code, 0x1000c5, 0, .W64⟩

/-- The entry is the label `toyWalk`. -/
theorem toyWalk_entry : Code.code.labels.label "toyWalk" = toyWalk.entry := by
  unfold Executable.labels
  rw [Lift.P1.withAddresses_eq]
  decide +kernel

/-- The address of the first node of the addresses `ps`; 0 (the null pointer) for no node. -/
def head : List (BitVec 64) → BitVec 64
  | [] => 0
  | p :: _ => p

/-- The node objects, read-only: the node `k` is at `ps[k]`, has the value `vs[k]` and points to
the node `k + 1`; the last node points to 0. -/
def nodes : List (BitVec 64) → List (BitVec 64) → List Object
  | v :: vs, p :: ps => ⟨p, Encode.encode (Node.mk v (head ps)), false⟩ :: nodes vs ps
  | _, _ => []

/-- At the return, the result is the result of L3. The memory is not in `post`: the frame clause
of `Fn.Return` keeps each byte, because no object is writable and the room is empty. -/
def post (x : In) (_ : CpuPolicy) (r : Field) (_ : DataMem) : Prop :=
  ∃ y, run x = some y ∧ Encode.encode y = [r]

/-- For each input `x` in the contract and each list `ps` of nonzero node addresses, one for each
value, each call `toyWalk(head ps)` returns the result of L3. -/
def WalkStatement : Prop :=
  ∀ x, C x → ∀ ps : List (BitVec 64), ps.length = x.length → (∀ p ∈ ps, p ≠ 0) →
    toyWalk.Call [⟨.W64, head ps⟩] (nodes x ps) (post x)

end Lift.Toys.WalkStatement
