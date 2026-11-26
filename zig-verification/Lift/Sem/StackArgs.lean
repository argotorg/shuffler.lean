module

public import Lift.Sem.HeapBytes

@[expose] public section

namespace Lift.Sem.StackArgs

/-- Read an argument word from current heap bytes, with entry bytes where the heap has no byte.
Addresses use 64-bit addition, including wrap at the end of the address space. -/
def overlay (heap : Heap) (addr original : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 8).foldl (init := 0) fun value i =>
    let byte := match heap.loadB (addr + BitVec.ofNat 64 i) .W8 with
      | .ok b => b.toNat
      | _ => (original.toNat / 2 ^ (8 * i)) % 256
    value + byte * 2 ^ (8 * i))

end Lift.Sem.StackArgs
