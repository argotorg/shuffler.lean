import BbuKraken.Unit.Plan.EntryDefs
import BbuKraken.Unit.Plan.PlannerRunMem

namespace Bbu.Unit.EntryValidU.Test
open Bbu.Sep

-- Empty inputs require no dropped, data, sources, or operation buffer cells.
example (g : EG) (hok : g.Ok) (hm : g.r.p.m = 0#64) (hn : g.r.p.n = 0#64) :
    Buffers g = Spl g.r.p.spl g.r.spills (List.range g.r.spillCount) ∗
      B8 g.sawPtr g.saw := by
  have hsw : g.r.p.sw = [] := List.eq_nil_iff_length_eq_zero.mpr (by rw [hok.sw, hm]; rfl)
  have htw : g.r.p.tw = [] := List.eq_nil_iff_length_eq_zero.mpr (by rw [hok.tw, hn]; rfl)
  have hops : g.r.ops = [] := List.eq_nil_iff_length_eq_zero.mpr (by rw [hok.ops, hm, hn]; rfl)
  simp only [Buffers, hsw, htw, hops, PlannerRunG.dataCapacity, hm, hn,
    BitVec.toNat_ofNat, Nat.zero_mod, Nat.max_self, List.take_zero, Arr, Bs, Ops,
    MProp.emp_sep]

-- Data uses the larger size; dropped bytes and sources use their own sizes.
example (g : EG) (hm : g.r.p.m = 1#64) (hn : g.r.p.n = 2#64) :
    Buffers g =
      Arr g.r.p.src g.r.p.sw ∗ Arr g.r.p.tgt g.r.p.tw ∗
        Spl g.r.p.spl g.r.spills (List.range g.r.spillCount) ∗
        Bs g.r.p.drp (g.r.dropped.toList.take 1) ∗
        Arr g.r.dataPtr (g.r.data.toList.take 2) ∗ Ops g.r.opsPtr 0 g.r.ops ∗
        Arr g.r.sourcesPtr (g.r.sources.toList.take 2) ∗ B8 g.sawPtr g.saw := by
  simp only [Buffers, PlannerRunG.dataCapacity, hm, hn]
  rfl

example (g : EG) (hm : g.r.p.m = 2#64) (hn : g.r.p.n = 1#64) :
    Buffers g =
      Arr g.r.p.src g.r.p.sw ∗ Arr g.r.p.tgt g.r.p.tw ∗
        Spl g.r.p.spl g.r.spills (List.range g.r.spillCount) ∗
        Bs g.r.p.drp (g.r.dropped.toList.take 2) ∗
        Arr g.r.dataPtr (g.r.data.toList.take 2) ∗ Ops g.r.opsPtr 0 g.r.ops ∗
        Arr g.r.sourcesPtr (g.r.sources.toList.take 1) ∗ B8 g.sawPtr g.saw := by
  simp only [Buffers, PlannerRunG.dataCapacity, hm, hn]
  rfl

-- At MAX_N, each physical prefix is the full vector.
example (g : EG) (hm : g.r.p.m = BitVec.ofNat 64 MAX_N)
    (hn : g.r.p.n = BitVec.ofNat 64 MAX_N) :
    Buffers g =
      Arr g.r.p.src g.r.p.sw ∗ Arr g.r.p.tgt g.r.p.tw ∗
        Spl g.r.p.spl g.r.spills (List.range g.r.spillCount) ∗
        Bs g.r.p.drp g.r.dropped.toList ∗ Arr g.r.dataPtr g.r.data.toList ∗
        Ops g.r.opsPtr 0 g.r.ops ∗ Arr g.r.sourcesPtr g.r.sources.toList ∗
        B8 g.sawPtr g.saw := by
  have hword : (BitVec.ofNat 64 MAX_N).toNat = MAX_N := by decide +kernel
  simp only [Buffers, PlannerRunG.dataCapacity, hm, hn, hword, Nat.max_self]
  simp only [List.take_of_length_le (Nat.le_of_eq Vector.length_toList)]

section
variable {P : Addr} {g : PlannerRunG} {F : MProp 64} {mem : Mem 64} (w : Word)
  (h : (PlannerRunView P g ∗ F).get mem)
  (hm : g.p.m = 2#64) (hn : g.p.n = 1#64)

-- The second data cell is owned even when the target has only one slot.
example :
    (PlannerRunView P {g with data := Flat.put g.data 1#64 w} ∗ F).get
      (mem.storeInt (slotAt g.dataPtr 1) 8 w.toInt) := by
  apply PlannerRunU.store_data h (by decide +kernel)
  simp only [PlannerRunG.dataCapacity, hm, hn]
  decide +kernel

-- The data store rule rejects the first cell past max(m,n).
example :
    (PlannerRunView P {g with data := Flat.put g.data 2#64 w} ∗ F).get
      (mem.storeInt (slotAt g.dataPtr 2) 8 w.toInt) ∨ True := by
  fail_if_success
    left
    apply PlannerRunU.store_data h
    · decide +kernel
    · simp only [PlannerRunG.dataCapacity, hm, hn]
      decide +kernel
    done
  exact Or.inr trivial

-- Sources stop at n, even when the data buffer has another cell.
example :
    (PlannerRunView P {g with sources := Flat.put g.sources 1#64 w} ∗ F).get
      (mem.storeInt (slotAt g.sourcesPtr 1) 8 w.toInt) ∨ True := by
  fail_if_success
    left
    apply PlannerRunU.store_sources h
    · decide +kernel
    · simp only [hn]
      decide +kernel
    done
  exact Or.inr trivial

end

-- The data store rule rejects every cell of an empty prefix.
example {P : Addr} {g : PlannerRunG} {F : MProp 64} {mem : Mem 64} (w : Word)
    (_h : (PlannerRunView P g ∗ F).get mem)
    (_hm : g.p.m = 0#64) (_hn : g.p.n = 0#64) :
    (PlannerRunView P {g with data := Flat.put g.data 0#64 w} ∗ F).get
      (mem.storeInt (slotAt g.dataPtr 0) 8 w.toInt) ∨ True := by
  fail_if_success
    left
    apply PlannerRunU.store_data _h
    · decide +kernel
    · simp only [PlannerRunG.dataCapacity, _hm, _hn]
      decide +kernel
    done
  exact Or.inr trivial

end Bbu.Unit.EntryValidU.Test
