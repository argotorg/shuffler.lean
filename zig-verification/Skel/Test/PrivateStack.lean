import Lift.Sem.PrivateStack

namespace PrivateStackTests

open Lift.Sem

private def loaded {w : Width} (r : Res w.type) (v : w.type) : Bool :=
  match r with | .ok x => x == v | _ => false

private def stuck {α : Type} (r : Res α) : Bool :=
  match r with | .stuck _ => true | _ => false

private def roundTrips : Bool :=
  [Width.W8, .W16, .W32, .W64].all fun w =>
    ([-65, -16, -1, 0, 1, 64] : List Int).all fun offset =>
      ([0, 1, 255, 256, 65535, 65536, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 64 - 1] : List Nat).all fun n =>
        let v := BitVec.ofNat w.bits n
        loaded (PrivateStack.load (PrivateStack.store PrivateStack.empty w offset v) w offset) v

def checks : List (String × Bool) :=
  let wide := PrivateStack.store PrivateStack.empty .W64 (-16) 0x8877665544332211
  let narrow := PrivateStack.store wide .W16 (-14) 0xbbaa
  let one := PrivateStack.store PrivateStack.empty .W8 (-1) 0xff
  [ ("round trips cover each width, signed offsets, and value boundaries", roundTrips),
    ("empty reads are stuck at each width", ([Width.W8, .W16, .W32, .W64].all fun w => stuck (PrivateStack.load PrivateStack.empty w (-8)))),
    ("64-bit values round trip at a negative offset", loaded (PrivateStack.load wide .W64 (-16)) 0x8877665544332211),
    ("bytes are little endian", loaded (PrivateStack.load wide .W8 (-16)) 0x11 && loaded (PrivateStack.load wide .W8 (-9)) 0x88),
    ("16-bit reads use adjacent bytes", loaded (PrivateStack.load wide .W16 (-15)) 0x3322),
    ("32-bit reads use adjacent bytes", loaded (PrivateStack.load wide .W32 (-12)) 0x88776655),
    ("overlapping stores replace only their bytes", loaded (PrivateStack.load narrow .W64 (-16)) 0x88776655bbaa2211),
    ("a byte store does not initialize its next byte", loaded (PrivateStack.load one .W8 (-1)) 0xff && stuck (PrivateStack.load one .W16 (-1))),
    ("a missing first byte stops a read", stuck (PrivateStack.load one .W16 (-2))),
    ("disjoint bytes stay absent after a store", stuck (PrivateStack.load wide .W8 (-17)) && stuck (PrivateStack.load wide .W8 (-8))),
    ("stores keep the prior map unchanged", stuck (PrivateStack.load PrivateStack.empty .W8 (-16))),
    ("16-bit stores round trip", loaded (PrivateStack.load (PrivateStack.store PrivateStack.empty .W16 (-2) 0xffff) .W16 (-2)) 0xffff),
    ("32-bit stores round trip", loaded (PrivateStack.load (PrivateStack.store PrivateStack.empty .W32 0 0xdeadbeef) .W32 0) 0xdeadbeef),
    ("zero values define bytes", loaded (PrivateStack.load (PrivateStack.store PrivateStack.empty .W64 (-8) 0) .W64 (-8)) 0),
    ("signed offsets do not wrap at 64 bits", stuck (PrivateStack.load (PrivateStack.store PrivateStack.empty .W8 (-(2 ^ 64)) 7) .W8 0)) ]

def run (_seed _cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "privatestack" then return 0
  let failed := checks.filter (!·.2)
  for (name, _) in failed do IO.println s!"FAIL privatestack: {name}"
  IO.println s!"privatestack: {checks.length} checks, {failed.length} failed"
  return failed.length

end PrivateStackTests
