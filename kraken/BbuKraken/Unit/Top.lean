import BbuKraken.Unit.Defs
import BbuKraken.Top

/-!
# `build_bottom_up`

`c/bbu/build_bottom_up.S`: the guard, `subq $16472` (the struct and 8 bytes), the constructor
of `Emission`, the call of `buildBottomUp`, and the map of the `Status` to the result.

The precondition of the call (`Sep.Pre S g F loopA 2068`): `S` is the struct at `rsp`, and the
ghost `g` has the header of the constructor, the `n` words of `data` and of `target`, the `6n`
records of `ops`, and `spl := topSpill s`. `G.Ok` holds by the guard and `nops = 0`. `TopMem`
gives that the atoms of the view are disjoint and that `Dests` holds for the destinations
(`loopA`, with `dests := flatDest s`, and `u` the content of the frame before the constructor).
`F` is the rest of the memory, with the two argument words at `rsp`.

After the call, `loopQ` gives the flat state of `g'` and the `Status` in `al`; with the stores to
`blocked` this is `FlatOut` for `Flat.build_bottom_up`.
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
