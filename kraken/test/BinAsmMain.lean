import BbuKraken.Asm
import PermuteKraken.Asm
import Kraken.X64.PrintATT

/-!
Print `bbuAsm ++ State.permuteAsm` in AT&T syntax, one directive on each line.
`test/bin_layout.sh` reads this to make `BbuKraken/BinLayout.lean`:

  lake env lean --run test/BinAsmMain.lean
-/

def main : IO Unit :=
  for d in Bbu.bbuAsm ++ State.permuteAsm do
    IO.println (Kraken.X64.ATT.directive d)
