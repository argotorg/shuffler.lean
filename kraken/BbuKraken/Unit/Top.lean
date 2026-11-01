module

public import BbuKraken.Unit.TopFill
import all BbuKraken.Unit.TopFill
public import BbuKraken.Unit.TopBind
import all BbuKraken.Unit.TopBind
public import BbuKraken.Unit.TopHdr
import all BbuKraken.Unit.TopHdr
public import BbuKraken.Unit.TopPos
import all BbuKraken.Unit.TopPos
public import BbuKraken.Unit.TopInvoke
import all BbuKraken.Unit.TopInvoke
public import BbuKraken.Unit.TopExit
import all BbuKraken.Unit.TopExit

@[expose] public section

/-!
# `build_bottom_up`

`c/bbu/build_bottom_up.S`: the guard, `subq $32872` (the struct, `m_plannedMapping`, a pad and
the local planned mapping), the loops of the constructor of `Emission`, the call of
`buildBottomUp`, and the map of the `Status` to the result.

`Program.WP.cfg` with `Top.LInv` and `Top.V` (`Unit/TopInv.lean`) and one block lemma for each
label of `Top.labels`. The block lemmas are in `TopFill`, `TopBind`, `TopHdr`, `TopPos`,
`TopInvoke` and `TopExit`.

The precondition of the call (`Sep.Pre S g F loopA 2068`): `S` is the struct at `rsp`, and the
ghost `g` has the header of the constructor, the `n` words of `data` and of `target`, the `6n`
records of `ops`, and `spl := topSpill s`. `F` is the locals `Lc` and the rest of the memory
(`Top.FL`). After the call, `loopQ` gives the flat state of `g'` and the `Status` in `al`. With
the stores to `blocked` this is `FlatOut` for `Flat.build_bottom_up`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit
open ProofKit Bbu.Sep Top

theorem buildBottomUp_unit [Host] [FunDecls]
    (hloop : Sep.Spec Names.buildBottomUp loopA 2068 loopQ) :
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ TopPre s ⦄ buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ TopFlatPost s t ∧ (topMod s).Agree s t ⦄ := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (LInv s ra) V ?_ rfl
  refine Permute.forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry s ra
  · exact b_fn s ra hpre
  · exact b_0 s ra hpre
  · exact b_1 s ra hpre
  · exact b_2 s ra hpre
  · exact b_3 s ra hpre
  · exact b_4 s ra hpre
  · exact b_5 s ra hpre
  · exact b_6 s ra hpre
  · exact b_7 s ra hpre
  · exact b_8 s ra hpre
  · exact b_9 s ra hpre
  · exact b_10 s ra hpre
  · exact b_11 s ra hpre
  · exact b_12 s ra hpre
  · exact b_13 s ra hpre
  · exact b_14 s ra hpre
  · exact b_15 s ra hpre
  · exact b_16 s ra hpre hloop
  · exact b_17 s ra hpre
  · exact b_18 s ra hpre
  · exact b_19 s ra hpre

end Bbu.Unit
