module

public import FlatShuffler.Unit.Plan.PlannerRunBuilderFrame
import all FlatShuffler.Unit.Plan.PlannerRunBuilderFrame
public import FlatShuffler.Unit.Plan.PlannerRunStore
import all FlatShuffler.Unit.Plan.PlannerRunStore
public import FlatShuffler.Unit.Plan.PlannerRunCtor
import all FlatShuffler.Unit.Plan.PlannerRunCtor

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

/-- The mapping words used by one planner attempt. -/
def MapCells (g : PlannerCallMemory) (M : Flat.Mapping) (locals : List Word) : Prop :=
  (∀ p, p < g.p.sourceSize → locals[12 + p.toNat]? = some (get M.dest p)) ∧
  (∀ p, p < g.p.targetSize → locals[1036 + p.toNat]? = some (get M.pos p))

structure AttemptLI (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (lo locals : List Word) (t : MachineData) : Prop
    extends LoopLI P g F s ra lo locals t where
  count : locals[3]? = some g.countPtr
  mapping : MapCells g M locals
  mappingEq : ∀ hl : locals.length = 4121, localMapping locals hl = M
  r15 : t.regs.r15.toBitVec = t.regs.rsp.toBitVec + 32#64

section
variable {P : Addr} {g : PlannerCallMemory} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}

theorem MapCells.localMapping (h : Bd P g F s ra lo locals t) (hok : g.Ok) :
    MapCells g (localMapping locals h.localLength) locals := by
  constructor
  · intro p hp
    rw [localMapping_dest locals h.localLength
      (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hok.planner.sourceSizeFitsBuffer)]
    exact List.getElem?_eq_getElem _
  · intro p hp
    rw [localMapping_pos locals h.localLength
      (Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hok.planner.targetSizeFitsBuffer)]
    exact List.getElem?_eq_getElem _

theorem localMapping_set_tail (hl : locals.length = 4121) (i : Nat) (hi : 2060 ≤ i)
    (w : Word) (hl' : (locals.set i w).length = 4121) :
    localMapping (locals.set i w) hl' = localMapping locals hl := by
  simp only [localMapping, List.drop_set, show ¬i < 12 by omega,
    show ¬i < 1036 by omega, ↓reduceIte,
    List.take_set_of_le (by omega : 1024 ≤ i - 12),
    List.take_set_of_le (by omega : 1024 ≤ i - 1036)]

theorem AttemptLI.next (h : AttemptLI P g M F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (hbp : u.regs.rbp = t.regs.rbp)
    (h12 : u.regs.r12 = t.regs.r12) (h15 : u.regs.r15 = t.regs.r15) :
    AttemptLI P g M F s ra lo locals u :=
  ⟨h.toLoopLI.next hm hsp hbx h14 h13 hbp h12, h.count, h.mapping, h.mappingEq,
    by simpa only [h15, hsp] using h.r15⟩

theorem AttemptLI.storeLocal (h : AttemptLI P g M F s ra lo locals t)
    (hok : g.Ok) {i : Nat} (hi : i < 4121) (hlo : 2060 ≤ i) (w : Word)
    (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (_h13 : u.regs.r13 = t.regs.r13) (_hbp : u.regs.rbp = t.regs.rbp)
    (_h12 : u.regs.r12 = t.regs.r12) (h15 : u.regs.r15 = t.regs.r15) :
    AttemptLI P g M F s ra lo (locals.set i w) u := by
  have unchanged (j : Nat) (hj : j < 2060) : (locals.set i w)[j]? = locals[j]? := by
    simp only [List.getElem?_set, show i ≠ j by omega, ↓reduceIte]
  refine ⟨⟨h.toBd.storeLocal hi w hm hsp, hbx ▸ h.rbx, h14 ▸ h.r14,
    ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [unchanged 1 (by decide)]
    exact h.ops
  · rw [unchanged 0 (by decide)]
    exact h.strategy
  · rw [unchanged 2 (by decide)]
    exact h.sources
  · rw [unchanged 3 (by decide)]
    exact h.count
  · intro p hp
    rw [unchanged (12 + p.toNat) (by
      have hpN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hok.planner.sourceSizeFitsBuffer
      change p.toNat < 1024 at hpN
      omega)]
    exact h.mapping.1 p hp
  · intro p hp
    rw [unchanged (1036 + p.toNat) (by
      have hpN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hok.planner.targetSizeFitsBuffer
      change p.toNat < 1024 at hpN
      omega)]
    exact h.mapping.2 p hp
  · intro hl'
    rw [localMapping_set_tail h.localLength i hlo w hl']
    exact h.mappingEq _
  · simpa only [h15, hsp] using h.r15

end

/-- The live words copied into the local emission mapping. -/
def WordPrefix (locals : List Word) (base : Nat) (v : Vector Word maxStackSize) (count : Nat) : Prop :=
  ∀ i, i < count → locals[base + i]? = some (get v (BitVec.ofNat 64 i))

theorem WordPrefix.zero (locals : List Word) (base : Nat) (v : Vector Word maxStackSize) :
    WordPrefix locals base v 0 := by
  intro i hi
  exact False.elim (Nat.not_lt_zero i hi)

theorem WordPrefix.step {locals : List Word} {base count : Nat} {v : Vector Word maxStackSize}
    (h : WordPrefix locals base v count) (hi : base + count < locals.length) :
    WordPrefix (locals.set (base + count) (get v (BitVec.ofNat 64 count)))
      base v (count + 1) := by
  intro i hi'
  by_cases he : i = count
  · subst i
    exact List.getElem?_set_self hi
  · simpa only [List.getElem?_set, show base + i ≠ base + count by omega,
      show base + count ≠ base + i by omega, ↓reduceIte] using h i (by omega)

theorem WordPrefix.set_outside {locals : List Word} {base count index : Nat}
    {v : Vector Word maxStackSize} (h : WordPrefix locals base v count)
    (hout : ∀ i, i < count → base + i ≠ index) (w : Word) :
    WordPrefix (locals.set index w) base v count := by
  intro i hi
  simpa only [List.getElem?_set, hout i hi, Ne.symm (hout i hi), ↓reduceIte]
    using h i hi

def CtorHeader (g : PlannerCallMemory) (locals : List Word) : Prop :=
  locals[2060]? = some g.p.tgt ∧ locals[2061]? = some g.p.targetSize ∧
  locals[2062]? = some g.p.spl ∧ locals[2063]? = some g.dataPtr ∧
  locals[2064]? = some g.p.sourceSize ∧ locals[2065]? = some g.opsPtr ∧
  locals[2066]? = some 0#64

theorem CtorHeader.set_tail {g : PlannerCallMemory} {locals : List Word}
    (h : CtorHeader g locals) {i : Nat} (hi : 2067 ≤ i) (w : Word) :
    CtorHeader g (locals.set i w) := by
  have unchanged (j : Nat) (hj : j < 2067) : (locals.set i w)[j]? = locals[j]? := by
    simp only [List.getElem?_set, show i ≠ j by omega, ↓reduceIte]
  simpa only [CtorHeader, unchanged 2060 (by decide), unchanged 2061 (by decide),
    unchanged 2062 (by decide), unchanged 2063 (by decide), unchanged 2064 (by decide),
    unchanged 2065 (by decide), unchanged 2066 (by decide)] using h

structure EmitLI (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (lo locals : List Word) (t : MachineData) : Prop
    extends AttemptLI P g M F s ra lo locals t where
  header : CtorHeader g locals

section
variable {P : Addr} {g : PlannerCallMemory} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}

theorem EmitLI.next (h : EmitLI P g M F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (hbp : u.regs.rbp = t.regs.rbp)
    (h12 : u.regs.r12 = t.regs.r12) (h15 : u.regs.r15 = t.regs.r15) :
    EmitLI P g M F s ra lo locals u :=
  ⟨h.toAttemptLI.next hm hsp hbx h14 h13 hbp h12 h15, h.header⟩

theorem EmitLI.storeLocal (h : EmitLI P g M F s ra lo locals t)
    (hok : g.Ok) {i : Nat} (hi : i < 4121) (hlo : 2067 ≤ i) (w : Word)
    (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (hbp : u.regs.rbp = t.regs.rbp)
    (h12 : u.regs.r12 = t.regs.r12) (h15 : u.regs.r15 = t.regs.r15) :
    EmitLI P g M F s ra lo (locals.set i w) u :=
  ⟨h.toAttemptLI.storeLocal hok hi (by omega) w hm hsp hbx h14 h13 hbp h12 h15,
    h.header.set_tail hlo w⟩

end

def EmitDestHead (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals, EmitLI P g M F s ra lo locals t ∧ rax t < g.p.sourceSize ∧
    rdx t = g.p.sourceSize ∧ rcx t = g.p.targetSize ∧ WordPrefix locals 2067 M.dest (rax t).toNat

def EmitDestDone (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals, EmitLI P g M F s ra lo locals t ∧
    rcx t = g.p.targetSize ∧ WordPrefix locals 2067 M.dest g.p.sourceSize.toNat

def EmitMapped (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals, EmitLI P g M F s ra lo locals t ∧
    WordPrefix locals 2067 M.dest g.p.sourceSize.toNat ∧ WordPrefix locals 3091 M.pos g.p.targetSize.toNat

def EmitPosHead (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals j, EmitLI P g M F s ra lo locals t ∧ j < g.p.targetSize ∧
    rax t = j * 8#64 ∧ rdx t = g.p.targetSize * 8#64 ∧
    t.regs.rsi.toBitVec = t.regs.rsp.toBitVec + 8288#64 ∧
    t.regs.rdi.toBitVec = t.regs.rsp.toBitVec + 24728#64 ∧
    WordPrefix locals 2067 M.dest g.p.sourceSize.toNat ∧ WordPrefix locals 3091 M.pos j.toNat

def countState (g : PlannerCallMemory) (M : Flat.Mapping) : Flat.St :=
  { target := g.p.fl.target, targetSize := g.p.targetSize, spills := g.spills,
    data := g.data.map StackSlot.ofWord, size := g.p.sourceSize, trace := [],
    dest := M.dest, pos := M.pos, pend := 0, blockedOffset := 0, blockedExcess := 0 }

structure EmitCountLI (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (lo locals : List Word) (t : MachineData) : Prop
    extends EmitLI P g M F s ra lo locals t where
  dest : WordPrefix locals 2067 M.dest g.p.sourceSize.toNat
  pos : WordPrefix locals 3091 M.pos g.p.targetSize.toNat
  original : locals[4118]? = some (t.regs.rsp.toBitVec + 96#64)

section
variable {P : Addr} {g : PlannerCallMemory} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}

theorem EmitCountLI.next (h : EmitCountLI P g M F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (hbp : u.regs.rbp = t.regs.rbp)
    (h12 : u.regs.r12 = t.regs.r12) (h15 : u.regs.r15 = t.regs.r15) :
    EmitCountLI P g M F s ra lo locals u :=
  ⟨h.toEmitLI.next hm hsp hbx h14 h13 hbp h12 h15, h.dest, h.pos, by simpa [hsp] using h.original⟩

theorem EmitCountLI.storePending (h : EmitCountLI P g M F s ra lo locals t)
    (hok : g.Ok) (w : Word)
    (hm : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 32920#64) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (hbp : u.regs.rbp = t.regs.rbp)
    (h12 : u.regs.r12 = t.regs.r12) (h15 : u.regs.r15 = t.regs.r15) :
    EmitCountLI P g M F s ra lo (locals.set 4115 w) u := by
  refine ⟨h.toEmitLI.storeLocal hok (by decide) (by decide) w hm hsp hbx h14 h13 hbp h12 h15,
    h.dest.set_outside ?_ w, h.pos.set_outside ?_ w, ?_⟩
  · intro i hi
    have hm := hok.planner.sourceSizeFitsBuffer
    change g.p.sourceSize.toNat ≤ 1024 at hm
    omega
  · intro i hi
    have hn := hok.planner.targetSizeFitsBuffer
    change g.p.targetSize.toNat ≤ 1024 at hn
    omega
  · simpa only [List.getElem?_set, show (4115:Nat) ≠ 4118 by decide,
      ↓reduceIte, hsp] using h.original

end

def EmitCountHead (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals j c, EmitCountLI P g M F s ra lo locals t ∧ j < g.p.targetSize ∧
    rax t = t.regs.rsp.toBitVec + 16480#64 + j * 8#64 ∧
    rdx t = t.regs.rsp.toBitVec + 16480#64 + g.p.targetSize * 8#64 ∧
    locals[4115]? = some c ∧
    Flat.unmappedFrom (countState g M) j c = Flat.unmappedFrom (countState g M) 0 0

def EmitCountNext (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals j c, EmitCountLI P g M F s ra lo locals t ∧ j < g.p.targetSize ∧
    rax t = t.regs.rsp.toBitVec + 16480#64 + j * 8#64 ∧
    rdx t = t.regs.rsp.toBitVec + 16480#64 + g.p.targetSize * 8#64 ∧
    locals[4115]? = some c ∧
    Flat.unmappedFrom (countState g M) (j + 1#64) c = Flat.unmappedFrom (countState g M) 0 0

def EmitReady (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals, EmitCountLI P g M F s ra lo locals t ∧
    locals[4115]? = some (Flat.unmappedFrom (countState g M) 0 0)

end FlatShuffler.Unit.PlannerRunU
