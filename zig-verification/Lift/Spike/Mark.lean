module

public import Lift.Sem.Sim
public import Lift.Sem.HeapLemmas
public import Lift.Spike.Sites.Mark

@[expose] public section

/-! T2 `toyMark` (`movb $1, (%rdi,%rsi) ; retq`): the chain `code ⇒ L2 ⇒ L2⁺ ⇒ L3`.

The source has no bounds check: L2 and L2⁺ store at `p + i` for each `i`; only L3 has the
condition `i < length`, as the contract `C`. -/

namespace Lift.Spike.Mark

open Lift.P2.Total Lift.Sem

/-- The state is at the entry of a call of `toyMark`. -/
abbrev Entry (policy : CpuPolicy) (s : MachineState) : Prop :=
  SysV.Entry policy toyJobPC toyEndPC toyMarkPC s

/-! ## L2: byte memory -/

/-- The L2 input: the policy, the memory, the arguments, and the private stack area `[lo, hi)`. -/
structure In2 where
  policy : CpuPolicy
  mem : DataMem
  p : UInt64
  i : UInt64
  lo : BitVec 64
  hi : BitVec 64

/-- L2: one block; the byte `1` at `p + i` if it is outside the private area, else `stuck`. -/
def blocks : Leaf Unit In2 DataMem where
  step _ x :=
    if InArea x.lo x.hi (x.p.toBitVec + x.i.toBitVec) then .stuck "store: private stack area"
    else match writeRam x.policy x.mem (x.p.toBitVec + x.i.toBitVec) .W8 1 with
      | .ok m => .ok (.ret m)
      | .error _ => .stuck "store"

def l2 : Model In2 DataMem where
  rep policy x s := x.policy = policy ∧ x.mem = s.data.dmem ∧ Entry policy s ∧
    s.data.regs.rdi = x.p ∧ s.data.regs.rsi = x.i ∧
    x.lo = s.data.regs.rsp.toBitVec ∧ x.hi = s.data.regs.rsp.toBitVec + 8
  returns x m := blocks.Returns noCall () x m
  post _ m s t := SysV.Exit s t ∧ t.data.dmem = m

/-! ## L2⁺: typed heap -/

/-- The L2⁺ input: the policy (for `Heap.Holds` in `post`), the heap, the arguments. -/
structure In2p where
  policy : CpuPolicy
  heap : Heap
  p : UInt64
  i : UInt64

/-- L2⁺: one block; the byte `1` at `p + i` in the heap. -/
def blocksP : Leaf Unit In2p Heap where
  step _ x := match x.heap.store (x.p.toBitVec + x.i.toBitVec) .W8 1 with
    | .ok h => .ok (.ret h)
    | .stuck why => .stuck why
    | .noFuel => .noFuel

def l2p : Model In2p Heap where
  rep policy x s := x.policy = policy ∧ x.heap.Holds policy s.data.dmem ∧ Entry policy s ∧
    s.data.regs.rdi = x.p ∧ s.data.regs.rsi = x.i ∧
    ∀ b, InArea s.data.regs.rsp.toBitVec (s.data.regs.rsp.toBitVec + 8) b → ¬ x.heap.Owned b
  returns x h := blocksP.Returns noCall () x h
  post x h s t := SysV.Exit s t ∧ h.Holds x.policy t.data.dmem ∧
    ∀ b, ¬ x.heap.Owned b → t.data.dmem.get? b = s.data.dmem.get? b

/-! ## L3: a list -/

/-- The L3 input: the bytes and the index. -/
abbrev In3 : Type := List (BitVec 8) × UInt64

/-- L3. -/
def run (x : In3) : Option (List (BitVec 8)) :=
  if x.2.toNat < x.1.length then some (x.1.set x.2.toNat 1) else none

/-- The contract: the index is in the list. -/
def C (x : In3) : Prop := x.2.toNat < x.1.length

theorem total : ∀ x, C x → ∃ y, run x = some y :=
  fun x hx => ⟨x.1.set x.2.toNat 1, by unfold C at hx; simp only [run, hx, ↓reduceIte]⟩

/-- The heap of the writable array `xs` at `p` and the frame. -/
def heapOf (p : BitVec 64) (frame : Heap) (xs : List (BitVec 8)) : Heap :=
  Obj.words p true .W8 xs :: frame

/-- L3 for the policy `pol`, the array at `p` and the other objects `frame`. -/
def l3 (pol : CpuPolicy) (p : BitVec 64) (frame : Heap) : Model In3 (List (BitVec 8)) where
  rep policy x s := policy = pol ∧ (heapOf p frame x.1).Holds policy s.data.dmem ∧
    Entry policy s ∧ s.data.regs.rdi.toBitVec = p ∧ s.data.regs.rsi = x.2 ∧
    ∀ b, InArea s.data.regs.rsp.toBitVec (s.data.regs.rsp.toBitVec + 8) b →
      ¬ (heapOf p frame x.1).Owned b
  returns x ys := run x = some ys
  post x ys s t := SysV.Exit s t ∧ (heapOf p frame ys).Holds pol t.data.dmem ∧
    ∀ b, ¬ (heapOf p frame x.1).Owned b → t.data.dmem.get? b = s.data.dmem.get? b

/-! ## The relations between the levels -/

/-- L2⁺ and L2 inputs: the same policy and arguments, the memory holds the heap, and no byte of
the private area is owned. -/
def SimIn (x : In2p) (y : In2) : Prop :=
  y.policy = x.policy ∧ x.heap.Holds x.policy y.mem ∧ y.p = x.p ∧ y.i = x.i ∧
    ∀ b, InArea y.lo y.hi b → ¬ x.heap.Owned b

/-- L2⁺ and L2 results: the memory holds the heap, and each byte that is not owned is the same. -/
def SimOut (x : In2p) (y : In2) (h : Heap) (m : DataMem) : Prop :=
  h.Holds x.policy m ∧ ∀ b, ¬ x.heap.Owned b → m.get? b = y.mem.get? b

/-- L3 and L2⁺ inputs: the heap is the array and the frame, some memory holds it, and the
arguments are the address and the index. -/
def SimIn3 (p : BitVec 64) (frame : Heap) (x : In3) (y : In2p) : Prop :=
  y.heap = heapOf p frame x.1 ∧ y.p.toBitVec = p ∧ y.i = x.2 ∧ ∃ m, y.heap.Holds y.policy m

/-- L3 and L2⁺ results: the input heap is the array and the frame; the result heap is the new
array and the frame. -/
def SimOut3 (p : BitVec 64) (frame : Heap) (x : In3) (y : In2p) (ys : List (BitVec 8))
    (h : Heap) : Prop :=
  y.heap = heapOf p frame x.1 ∧ h = heapOf p frame ys

/-! ## The chain -/

theorem decompiles_l2 : Decompiles L1.step l2 := by
  refine Decompiles.ofBlocks blocks noCallee (fun f => f.elim) () id
    (fun policy a s₀ _ x s => s = s₀ ∧ l2.rep policy a s ∧ x = a)
    (fun _ _ h => h) (fun _ _ _ h => ⟨rfl, h, rfl⟩) ?_
  rintro policy ⟨pol, mem, p, i, lo, hi⟩ s₀ ⟨⟩ x s ⟨rfl, ⟨rfl, rfl, he, rfl, rfl, rfl, rfl⟩, rfl⟩
    n hn
  simp only [blocks] at hn
  split at hn
  · cases hn
  · rename_i hout
    split at hn
    · rename_i m hw
      cases hn
      obtain ⟨ra, hra⟩ := he.ret
      have hread :=
        Sites.readRam_of_writeRam hw (disjoint_of_not_inArea hout) (Sites.readRet he hra)
      obtain ⟨d, pc⟩ := s
      obtain rfl : pc = toyMarkPC := he.pc
      exact Sites.Mark.block he.exec d m ra hw hread fun _ =>
        ⟨⟨hra, by simp [AbiRestored]⟩, rfl⟩
    · cases hn

theorem refines_l2p : Refines SimIn SimOut l2p.returns l2.returns := by
  intro xh xl h hs hr
  refine Blocks.Returns.sim (fun f => f.elim) (fun f => f.elim) (fun a b => a = xh ∧ b = xl)
    (SimOut xh xl) (fun f => f.elim) ?_ hr ⟨rfl, rfl⟩
  rintro ⟨⟩ x y n ⟨rfl, rfl⟩ hn
  obtain ⟨pol, heap, p, i⟩ := x
  obtain ⟨pol', mem, p', i', lo, hi⟩ := y
  obtain ⟨rfl, hh, rfl, rfl, harea⟩ := hs
  simp only [blocksP] at hn
  split at hn
  · rename_i h' hst
    cases hn
    obtain ⟨m, hw, hh', hfr⟩ := Heap.store_frame hh hst
    have hout : ¬ InArea lo hi (p'.toBitVec + i'.toBitVec) :=
      fun hin => harea _ hin (by simpa using owned_of_store hh hst 0 (width_bytes_pos _))
    exact ⟨m, by simp only [blocks, hout, ↓reduceIte, hw], hh', hfr⟩
  · cases hn
  · cases hn

theorem above_l2p : Above l2 l2p := by
  refine Above.ofRefines (fun _ _ => SimIn) (fun _ _ => SimOut) (fun _ _ => refines_l2p) ?_ ?_
  · rintro policy ⟨pol, heap, p, i⟩ s ⟨rfl, hh, he, hp, hi, harea⟩
    exact ⟨⟨pol, s.data.dmem, p, i, s.data.regs.rsp.toBitVec, s.data.regs.rsp.toBitVec + 8⟩,
      ⟨rfl, rfl, he, hp, hi, rfl, rfl⟩, rfl, hh, rfl, rfl, harea⟩
  · rintro policy a b s h m t - ⟨-, hm, -⟩ ⟨hh, hfr⟩ ⟨hex, rfl⟩
    exact ⟨hex, hh, fun c hc => (hfr c hc).trans (by rw [hm])⟩

theorem refines_l3 (p : BitVec 64) (frame : Heap) :
    Refines (SimIn3 p frame) (SimOut3 p frame) (fun x y => run x = some y) l2p.returns := by
  rintro ⟨xs, i⟩ ⟨pol, heap, q, j⟩ ys ⟨hheap, hq, hj, m, hh⟩ hr
  simp only at hheap hq hj hh
  subst hheap hq hj
  simp only [run] at hr
  split at hr
  · rename_i hi
    cases hr
    have hn := not_mem_of_holds hh rfl (by
      unfold Obj.size Obj.words; rw [words_bytes]; simp only [Width.bytes]; omega)
    obtain ⟨h', hs, hrep⟩ := Heap.store_words8 hh (List.mem_cons_self ..) hi 1
    refine ⟨h', .ret (by simp only [blocksP, hs]), rfl, ?_⟩
    cases hrep with
    | here ht => rw [replaces_eq_of_not_mem ht hn]; rfl
    | there hne _ => exact absurd rfl hne
  · cases hr

theorem above_l3 (pol : CpuPolicy) (p : BitVec 64) (frame : Heap) :
    Above l2p (l3 pol p frame) := by
  refine Above.ofRefines (fun _ _ => SimIn3 p frame) (fun _ _ => SimOut3 p frame)
    (fun _ _ => refines_l3 p frame) ?_ ?_
  · rintro policy ⟨xs, i⟩ s ⟨rfl, hh, he, hp, hi, harea⟩
    exact ⟨⟨policy, heapOf p frame xs, s.data.regs.rdi, i⟩, ⟨rfl, hh, he, rfl, hi, harea⟩,
      rfl, hp, rfl, _, hh⟩
  · rintro policy a b s ys h t ⟨rfl, -⟩ ⟨hpol, -⟩ ⟨hb, rfl⟩ ⟨hex, hh, hfr⟩
    rw [hpol] at hh
    rw [hb] at hfr
    exact ⟨hex, hh, hfr⟩

theorem decompiles : ∀ pol p frame, Decompiles L1.step (l3 pol p frame) :=
  fun pol p frame => (decompiles_l2.above above_l2p).above (above_l3 pol p frame)

/-- The same theorem for the Kraken step function. -/
theorem decompiles_code :
    ∀ pol p frame, Decompiles (fun s => Code.code.step s .done) (l3 pol p frame) :=
  fun pol p frame => (Sites.decompiles_l1Spec_iff Code.code L1.step L1.spec (l3 pol p frame)).mp
    (decompiles pol p frame)

/-- The end theorem: for each input in `C` and each entry state, the code returns a result of L3. -/
theorem contract (pol : CpuPolicy) (p : BitVec 64) (frame : Heap) :
    ∀ policy x s, (l3 pol p frame).rep policy x s → C x →
      Reaches (fun s => Code.code.step s .done) policy
        (fun t => ∃ ys, (l3 pol p frame).post x ys s t ∧ run x = some ys) s :=
  Decompiles.transfer (decompiles_code pol p frame) C (fun x y => run x = some y) total
    fun _ _ _ h => h

end Lift.Spike.Mark
