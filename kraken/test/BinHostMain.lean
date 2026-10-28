import BbuKraken.Bin
import Kraken.X64.PrintATT

/-!
Print the program of `Bbu.binHost`, one directive on each line: the address in hex
and the size from the layout of the host, then the directive in AT&T syntax.
`test/bin_check.sh` compares this with the disassembly of `c/bbu_harness`:

  lake env lean --run test/BinHostMain.lean
-/

open Bbu

def main : IO Unit :=
  for d in Host.prog, i in [0:Host.prog.length] do
    let addr := String.ofList (Nat.toDigits 16 (Host.addrOf i).toUInt64.toNat)
    IO.println s!"{addr} {Kraken.Layout.size Directive i} {Kraken.X64.ATT.directive d}"
