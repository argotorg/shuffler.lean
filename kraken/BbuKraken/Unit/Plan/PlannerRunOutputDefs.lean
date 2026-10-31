import BbuKraken.Unit.Plan.PlannerRunBuilderFrame
import BbuKraken.Unit.Plan.PlannerRunStore

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

structure PostEmitLI (P : Addr) (g : PlannerRunG) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (lo locals : List Word) (t : MachineData) : Prop
    extends LoopLI P g F s ra lo locals t where
  count : locals[3]? = some g.countPtr
  nops : locals[2066]? = some (BitVec.ofNat 64 g.traceLength)
  mappingEq : ∀ hl : locals.length = 4121, localMapping locals hl = M
  ok : g.Ok
  r13 : t.regs.r13.toBitVec = t.regs.rsp.toBitVec + 32#64

section
variable {P : Addr} {g : PlannerRunG} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}

theorem PostEmitLI.next (h : PostEmitLI P g M F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) :
    PostEmitLI P g M F s ra lo locals u :=
  ⟨⟨h.toBd.next hm hsp, hbx ▸ h.rbx, h12 ▸ h.r12, h15 ▸ h.r15,
    h14 ▸ h.r14, h.sources⟩, h.count, h.nops, h.mappingEq, h.ok,
    by rw [h13, hsp]; exact h.r13⟩

theorem PostEmitLI.posRead (h : PostEmitLI P g M F s ra lo locals t)
    {i : Word} (hi : i.toNat < MAX_N) :
    rd t.dmem (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (1036 + i.toNat))) =
      get M.pos i := by
  have hidx : 1036 + i.toNat < 4121 := by change i.toNat < 1024 at hi; omega
  rw [h.localRead hidx, ← localMapping_pos locals h.localLength hi, h.mappingEq]

theorem PostEmitLI.storeSources (h : PostEmitLI P g M F s ra lo locals t)
    {i : Word} (hi : i.toNat < MAX_N) (hn : i.toNat < g.p.n.toNat) (w : Word)
    (hm : u.dmem = t.dmem.storeInt (slotAt g.sourcesPtr i.toNat) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) :
    PostEmitLI P {g with sources := put g.sources i w} M F s ra lo locals u := by
  have hnew := store_sources h.kb.vmem hi hn w
  refine ⟨⟨⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, h.localLength⟩,
    hbx ▸ h.rbx, h12 ▸ h.r12, h15 ▸ h.r15, h14 ▸ h.r14, h.sources⟩,
    h.count, h.nops, h.mappingEq,
    ⟨h.ok.planner, h.ok.spillCount, h.ok.sourceIds, h.ok.targetIds,
      h.ok.ops, h.ok.traceLength⟩, by rw [h13, hsp]; exact h.r13⟩
  rw [hm]
  exact (sep_lc _ _ _).symm ▸ hnew

theorem PostEmitLI.storeCount (h : PostEmitLI P g M F s ra lo locals t)
    (w : Word) (hm : u.dmem = t.dmem.storeInt g.countPtr 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp) :
    Bd P {g with count := w} F s ra lo locals u := by
  have hnew := store_count h.kb.vmem w
  refine ⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, h.localLength⟩
  rw [hm]
  exact (sep_lc _ _ _).symm ▸ hnew

end

def PostEmitHead (P : Addr) (g : PlannerRunG) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals, PostEmitLI P g M F s ra lo locals t

def SourcesHead (P : Addr) (g : PlannerRunG) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (wanted : Vector Word MAX_N) (t : MachineData) : Prop :=
  ∃ lo locals, PostEmitLI P g M F s ra lo locals t ∧
    t.regs.rbp.toBitVec = g.countPtr ∧ rdx t < g.p.n ∧
    Flat.sourcesFrom g.p.n (rdx t) M g.sources = wanted

def SourcesDone (P : Addr) (g : PlannerRunG) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals, PostEmitLI P g M F s ra lo locals t ∧
    t.regs.rbp.toBitVec = g.countPtr

end Bbu.Unit.PlannerRunU
