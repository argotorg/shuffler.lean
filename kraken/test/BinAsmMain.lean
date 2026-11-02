import FlatShuffler.Asm
import Kraken.X64.PrintATT

/-!
Print `bbuAsm` in AT&T syntax, one directive on each line.
`test/bin_layout.sh` reads this to make `FlatShuffler/BinLayout.lean`:

  lake env lean --run test/BinAsmMain.lean
-/

def main : IO Unit :=
  for d in FlatShuffler.bbuAsm do
    IO.println (Kraken.X64.ATT.directive d)
