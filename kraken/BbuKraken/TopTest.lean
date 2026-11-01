module

public import BbuKraken.Top
import all BbuKraken.Top

@[expose] public section

/-!
Tests of `Top.lean`. `TopMem` is the `TopMem` of commit 12cb0e8 (`OldTopMem`) and two facts on
`blocked`: the region `blocked` and the word `blocked` at `rsp + 8` are disjoint from `data` and
the ops buffer. Thus the precondition of the final theorems excludes no other inputs.
-/

namespace Bbu.TopTest

open Bbu

variable (s : MachineData)

-- `TopMem` of 12cb0e8.
structure OldTopMem : Prop where
  dests : Dests (nArg s) (topDests s)
  mapped : Mem.Mapped (topOut s ++ topIn s) s.dmem
  data_lt : (dataArg s).toNat + 8 * nArg s ≤ 2 ^ 64
  tgt_lt : (tgtArg s).toNat + 8 * nArg s ≤ 2 ^ 64
  ops_lt : (opsArg s).toNat + 72 * nArg s ≤ 2 ^ 64
  blk_lt : (blkArg s).toNat + 16 ≤ 2 ^ 64
  disj_frame : Mem.Blocks.Disjoint [frame topF s] (topOut s ++ (dstArg s, 8 * mArg s) :: topRd s)
  disj_data : Mem.Blocks.Disjoint [(dataArg s, 8 * nArg s)] ((opsArg s, 72 * nArg s) :: topRd s)
  disj_ops : Mem.Blocks.Disjoint [(opsArg s, 72 * nArg s)] (topRd s)

theorem topMem_iff : TopMem s ↔ OldTopMem s
    ∧ Mem.Blocks.Disjoint [(blkArg s, 16)] [(dataArg s, 8 * nArg s), (opsArg s, 72 * nArg s)]
    ∧ Mem.Blocks.Disjoint [(rsp s + 8#64, 8)] [(dataArg s, 8 * nArg s), (opsArg s, 72 * nArg s)] :=
  ⟨fun h => ⟨⟨h.dests, h.mapped, h.data_lt, h.tgt_lt, h.ops_lt, h.blk_lt, h.disj_frame, h.disj_data,
      h.disj_ops⟩, h.disj_blk, h.disj_blkp⟩,
    fun ⟨h, hb, hp⟩ => ⟨h.dests, h.mapped, h.data_lt, h.tgt_lt, h.ops_lt, h.blk_lt, h.disj_frame,
      h.disj_data, h.disj_ops, hb, hp⟩⟩

end Bbu.TopTest
