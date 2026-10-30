import BbuKraken.Unit.Defs
import BbuKraken.Top

/-!
# `build_bottom_up`

`c/bbu/build_bottom_up.S`: the guard, `subq $16472` (the struct and 8 bytes), the constructor
of `Emission`, the call of `buildBottomUp`, and the map of the `Status` to the result.

The precondition of the call (`Sep.Pre S g F loopA 2068`): `S` is the struct at `rsp`, and the
ghost `g` has the header of the constructor, the `n` words of `data` and of `target`, the `6n`
records of `ops`, and `spl := topSpill s`. `G.Ok` holds by the guard and `nops = 0`. For
`G.Ok.spl`: `topSpill s` reads the memory, a spilled byte in the target is a byte of the target
word (`Sep.Wd.rdb_byte`), and an id is less than `2 ^ 32`, so
`(BitVec.ofNat 32 i).setWidth 64 = BitVec.ofNat 64 i`. `TopMem` gives that the atoms of the
view are disjoint: the `Spl` atoms are only for the ids whose byte is not in the target
(`Sep.splOut`). `TopMem` also gives that `Dests` holds for the destinations (`loopA`, with
`dests := flatDest s`, and `u` the content of the frame before the constructor). `F` is the rest
of the memory.

After the call, `loopQ` gives the flat state of `g'` and the `Status` in `al`. The word at
`rsp + 8` is not in `data` or in the ops buffer (`disj_blkp`). Its bytes are in `F` or in the
atoms of the target and of the spilled bytes, and the call does not change these (`Keep`), so the
load after the call gives `blkArg s`. With the stores to `blocked` this is `FlatOut` for
`Flat.build_bottom_up`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit

theorem buildBottomUp_unit [Host] [FunDecls]
    (hloop : Sep.Spec Names.buildBottomUp loopA 2068 loopQ) :
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ TopPre s ⦄ buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ TopFlatPost s t ∧ (topMod s).Agree s t ⦄ := by
  sorry

end Bbu.Unit
