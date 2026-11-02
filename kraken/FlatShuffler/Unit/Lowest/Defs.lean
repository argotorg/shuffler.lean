module

public import FlatShuffler.Unit.ExitDefs
import all FlatShuffler.Unit.ExitDefs
public import FlatShuffler.FlatLowest
import all FlatShuffler.FlatLowest

@[expose] public section

/-!
# `permuteAtLowestHeight`: the contract

`Names.permuteAtLowestHeight` in `build/kraken/c/build_bottom_up.S`: `subq $24584`, so 3073 words: the arrays `parked` (at
`rsp`), `holes` (at `rsp + 8192`) and `permutation` (at `rsp + 16384`) and one word. Then the call
of `permute` takes one word for its return address and 1034 words. So `lowestD` is
`3073 + 1 + 1034`.

The member `m_plannedMapping` (`Fld.plannedMapping`) is not in `View`: it points to a `Mapping` out
of the struct. `Planned` holds the pointer and the `m_positionOf` array of that `Mapping`. The
function reads them and does not write them.

`lowestA` gives the preconditions of `permute`: the room in the trace, `DestOk` and the bijection
(`Flat.LowOk`, the formula of `Bij`). The arrays have no initial value: the result holds for the
content `l` of the arrays that the function finds (`lowestQ`).
-/

namespace FlatShuffler.Unit

open FlatShuffler.Sep (G)

-- The pointer `m_plannedMapping` to the planned mapping at `PM`, and its `m_positionOf` array.
def Planned (S PM : Addr) (planned : Vector Word MAX_N) : MProp 64 :=
  Sep.Wd (Fld.plannedMapping S) PM ∗ Sep.Arr (PM + 8192#64) planned.toList

-- `permuteAtLowestHeight()`
def lowestA (planned : Vector Word MAX_N) (g : G) (_s : MachineData) : Prop :=
  g.h.nops.toNat + 2 * g.h.len.toNat ≤ 6 * g.h.n.toNat + g.xo ∧ DestOk (flat g)
    ∧ Flat.LowOk planned (flat g)
def lowestQ (planned : Vector Word MAX_N) (g g' : G) (_s t : MachineData) : Prop :=
  ∃ l, NormalResult (Flat.permuteAtLowestHeight planned l) g g' t

def lowestX (planned : Vector Word MAX_N) (g g' : G) (_s _t : MachineData) : Prop :=
  ∃ l, ExitRes (Flat.permuteAtLowestHeight planned l) g g'

abbrev lowestD : Nat := 3073 + 1 + 1034

-- The unit theorem of `permuteAtLowestHeight`: `Planned` is in the frame.
abbrev LowestThm [Host] [FunDecls] (prog : Program) : Prop :=
  ∀ S PM planned g F,
    Sep.BodyWithExit prog (Sep.Pre S g (Planned S PM planned ∗ F) (lowestA planned) lowestD)
      (fun s t => Sep.Post S (Planned S PM planned ∗ F) lowestD
        (fun g' t => lowestQ planned g g' s t) s t)
      (fun s t => Sep.Post S (Planned S PM planned ∗ F) lowestD
        (fun g' t => lowestX planned g g' s t) s t)

end FlatShuffler.Unit
