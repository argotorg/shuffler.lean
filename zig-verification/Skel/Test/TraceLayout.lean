import Skel.IntQ.Refute

/-! Check the production trace encoding against the 12-byte ShuffleOp layout. -/

namespace TraceLayoutTests

open Lift.Trusted Lift.Shuffler.Zig Lift.Shuffler.Internal.Proposed
open Skel.IntQ

def checks (seed cases : Nat) : List (String × Bool) :=
  let state := (Refute.draw (Coordinator.Dst.Rng.ofSeed seed) : St × _).1
  let env := (Refute.env (Coordinator.Dst.Rng.ofSeed seed)).1
  let encoded (pad : BitVec 16) :=
    let op : OpP := ⟨⟨3, 0x5a, ⟨0x11223344, 0x77, 0x88⟩⟩, pad⟩
    let object := Layout.trace env { state with trace := [op] } true
    Refute.objBytes { object with fields := object.fields.take 4 }
  let expected (pad : BitVec 16) : List UInt8 :=
    [3, 0x5a, 0, 0, 0x44, 0x33, 0x22, 0x11, 0x77, 0x88,
      UInt8.ofNat pad.toNat, UInt8.ofNat (pad.toNat / 256)]
  let pads : List (BitVec 16) := [0, 1, 0x8000, 0xffff, 0xbbaa]
  [ ("slot padding occupies bytes 10 and 11", pads.all fun pad => encoded pad == expected pad),
    ("alignment bytes 2 and 3 do not contain slot padding",
      pads.all fun pad => ((encoded pad).drop 2).take 2 == [0, 0]),
    ("negative: slot padding cannot be moved to alignment bytes",
      encoded 0xbbaa != [3, 0x5a, 0xaa, 0xbb, 0x44, 0x33, 0x22, 0x11, 0x77, 0x88, 0, 0]),
    ("trace objects retain their address, size and write permission",
      let object := Layout.trace env { state with trace := [] } true
      object.addr == env.trace && object.size == 12 * maxTraceSize && object.writable),
    ("generated slot padding values use the machine byte positions",
      (List.range cases).all fun i =>
        let g := Coordinator.Dst.Rng.stream (Coordinator.Dst.Rng.ofSeed seed) i
        let pad := BitVec.ofNat 16 (g.nat 65536).1
        encoded pad == expected pad) ]

def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "tracelayout" then return 0
  let results := checks seed cases
  for (name, ok) in results do
    unless ok do IO.println s!"FAIL  tracelayout: {name}"
  return results.countP (! ·.2)

end TraceLayoutTests
