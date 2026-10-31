import BbuKraken.Unit.Plan.PlannerRunBuilderCall
import BbuKraken.Unit.Plan.ResolveMem

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat
set_option maxRecDepth 4096

def localCurrentMapping (locals : List Word) (hl : locals.length = 4121) : Flat.Mapping where
  dest := ⟨((locals.drop 2067).take 1024).toArray, by simp [hl, MAX_N]⟩
  pos := ⟨((locals.drop 3091).take 1024).toArray, by simp [hl, MAX_N]⟩

theorem current_partition (locals : List Word) :
    locals.drop 2060 = (locals.drop 2060).take 7 ++ (locals.drop 2067).take 1024 ++
      (locals.drop 3091).take 1024 ++ locals.drop 4115 := by
  have h1 : (locals.drop 2060).drop 7 = locals.drop 2067 := by rw [List.drop_drop]
  have h2 : (locals.drop 2067).drop 1024 = locals.drop 3091 := by rw [List.drop_drop]
  have h3 : (locals.drop 3091).drop 1024 = locals.drop 4115 := by rw [List.drop_drop]
  rw [← h3, ← h2, ← h1, List.append_assoc, List.append_assoc,
    List.take_append_drop, List.take_append_drop, List.take_append_drop]

theorem local_current_mapping (sp : Addr) (locals : List Word) (hl : locals.length = 4121)
    (sv : List Word) :
    Arr (sp + 16480#64) (locals.drop 2060 ++ sv) =
      MapM (sp + 16536#64) (localCurrentMapping locals hl) ∗
        Arr (sp + 16480#64) ((locals.drop 2060).take 7) ∗
        Arr (sp + 32920#64) (locals.drop 4115 ++ sv) := by
  have hh : ((locals.drop 2060).take 7).length = 7 := by simp [hl]
  have hd : ((locals.drop 2067).take 1024).length = 1024 := by simp [hl]
  have hp : ((locals.drop 3091).take 1024).length = 1024 := by simp [hl]
  conv => lhs; rw [current_partition locals]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, Arr.append, hh,
    Arr.append, hd, Arr.append, hp]
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, MapM, localCurrentMapping]
  ecancel

def withResolve (g : PlannerRunG) (spills : BitVec 32 → BitVec 8)
    (dropped : Vector (BitVec 8) MAX_N) : PlannerRunG :=
  {g with spills := spills, dropped := dropped}

def plannerResolve (g : PlannerRunG) (sp : Addr) (M current : Flat.Mapping) : RG where
  p := g.p
  mp := sp + 96#64
  M := M
  currentPtr := sp + 16536#64
  current := current
  spillCount := g.spillCount
  spills := g.spills
  dropped := g.dropped

theorem resolve_call_frame (P : Addr) (g : PlannerRunG) (s : MachineData) (ra : Int64)
    (locals : List Word) (hl : locals.length = 4121) (F : MProp 64) :
    let sp := rsp s - 8#64 - 33016#64
    ∃ CF, ∀ (lo : List Word) (w : Word) (spills : BitVec 32 → BitVec 8)
        (dropped : Vector (BitVec 8) MAX_N),
      let g' := withResolve g spills dropped
      Stk (rsp s) (lo ++ w :: (locals ++ saved s)) ra.toBitVec ∗
          (PlannerRunView P g' ∗ F) =
        Stk sp lo w ∗ (RView P (plannerResolve g' sp
          (localMapping locals hl) (localCurrentMapping locals hl)) ∗ CF) := by
  dsimp
  let sp := rsp s - 8#64 - 33016#64
  refine ⟨Arr sp (locals.take 12) ∗ Arr (sp + 16480#64) ((locals.drop 2060).take 7) ∗
    Arr (sp + 32920#64) (locals.drop 4115 ++ saved s) ∗
    Arr g.dataPtr (g.data.toList.take g.dataCapacity) ∗ Ops g.opsPtr 0 g.ops ∗
    Arr g.sourcesPtr (g.sources.toList.take g.p.n.toNat) ∗ Wd g.countPtr g.count ∗
    Wd (rsp s - 8#64) ra.toBitVec ∗ F, ?_⟩
  intro lo w spills dropped
  rw [Stk.callee]
  simp only [List.length_append, hl, saved, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul]
  change Stk sp lo w ∗ (PlannerRunView P (withResolve g spills dropped) ∗
    (Arr sp (locals ++ saved s) ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)) = _
  rw [local_mapping sp locals hl, local_current_mapping sp locals hl]
  simp only [PlannerRunG.dataCapacity, PlannerRunView, RView, plannerResolve, withResolve]
  simp only [sp, rsp, saved, Reg64s.get64_rsp]
  ecancel

end Bbu.Unit.PlannerRunU
