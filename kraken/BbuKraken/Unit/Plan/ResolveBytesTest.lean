module

public import BbuKraken.Unit.Plan.ResolveBytes
import all BbuKraken.Unit.Plan.ResolveBytes

@[expose] public section

open Bbu Bbu.Unit.ResolveU

example : wordBytes 0 = List.replicate 8 0 := by decide +kernel
example : wordBytes 0xffffffffffffffff = List.replicate 8 0xff := by decide +kernel
example : wordBytes 0x0123456789abcdef = [0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01] :=
  by decide +kernel
example : wordBytes 0x8000000000000000 = [0, 0, 0, 0, 0, 0, 0, 0x80] := by decide +kernel
