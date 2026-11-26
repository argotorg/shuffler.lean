module

public import Lift.Sem.Sim
public import Lift.Sem.StackRoom
public import Lift.Sem.HeapLemmas
public import Lift.Spike.Sites.Job
public import Lift.Spike.Sum
public import Lift.Spike.Mark
public import Lift.Spike.JobSpec

@[expose] public section

/-! T5 `toyJob(j)` (`len > limit` gives `too_long`, else `total := toySum(src, len)` and `done`):
the chain `code ⇒ L2 ⇒ L2⁺ ⇒ L3`.

The structure is that of `Lift/Spike/Two.lean` (a call and a stack room) and of
`Lift/Spike/Mark.lean` (a store into a heap object). The block lemmas are `Sites.Job.entry`,
`Sites.Job.tooLong`, `Sites.Job.callSum` and `Sites.Job.sumRet`. The proofs use only these facts
of `toySum`: the models `Sum.l2`, `Sum.l2p` (their `rep`, `post` and `returns`), `Sum.run`, the
input structures, and the theorems `Sum.decompiles_l2`, `Sum.refines_l2p`, `Sum.refines_l3`.

L2 has the pushes of the code as stores of its memory: the callee `Sum.l2` takes the memory of
the call state, and that memory has the pushed `rbx` and the return address. The private area of
L2 is the 16 bytes of room and the return word; the store of `total` is 8 bytes wide, and L2 is
`stuck` if one of the 8 bytes is in the private area. -/

namespace Lift.Spike.Job

open Lift.P2.Total Lift.Sem
open Lift.Spike.Sites.Job (tooLongPC callSumPC retSumPC)

/-- The state is at the entry of a call of `toyJob`. -/
abbrev Entry (policy : CpuPolicy) (s : MachineState) : Prop :=
  SysV.Entry policy toyJobPC toyEndPC toyJobPC s

/-- The byte `b` is in the private area of a call with the stack pointer `sp`: the 16 bytes of
room below `sp` and the return word at `sp`, modulo `2^64`. -/
abbrev Private (sp b : BitVec 64) : Prop := (b - (sp - 16)).toNat < 24

/-- No byte of the 8 bytes at `a` is in the private area. -/
abbrev Clear (sp a : BitVec 64) : Prop := ∀ i, i < 8 → ¬ Private sp (a + BitVec.ofNat 64 i)

/-! ## L2: byte memory -/

/-- The L2 input: the policy, the memory, the record pointer `j`, the stack pointer and the
`rbx` of the caller (the code pushes it). -/
structure In2 where
  policy : CpuPolicy
  mem : DataMem
  j : UInt64
  sp : BitVec 64
  rbx : UInt64

/-- The labels: one for each basic block of the code. -/
inductive Lbl where
  | entry
  | tooLong
  | callSum
  | sumRet

/-- An L2 block state: the input, `len`, the memory after the call, and the sum. -/
structure St where
  input : In2
  len : UInt64
  mem : DataMem
  acc : UInt64

def init (x : In2) : St := ⟨x, 0, x.mem, 0⟩

/-- L2: the loads of `len` and `limit`; `rax := 1` by a push; the push of `rbx`, the load of
`src`, the push of the return address and the call `toySum(src, len)`; the store of the sum to
`total` and `rax := 0`. -/
def blocks : Blocks Lbl St (UInt64 × DataMem) Unit (fun _ => Sum.In2) (fun _ => UInt64) where
  step
    | .entry, x =>
      match readRam x.input.policy x.input.mem (x.input.j.toBitVec + 8) .W64,
          readRam x.input.policy x.input.mem (x.input.j.toBitVec + 16) .W64 with
      | .ok len, .ok limit =>
        .ok (.goto (if UInt64.ofBitVec len ≤ UInt64.ofBitVec limit then .callSum else .tooLong)
          { x with len := UInt64.ofBitVec len })
      | _, _ => .stuck "load"
    | .tooLong, x =>
      match writeRam x.input.policy x.input.mem (x.input.sp - 8) .W64 1 with
      | .ok m => .ok (.ret (1, m))
      | .error _ => .stuck "push"
    | .callSum, x =>
      match writeRam x.input.policy x.input.mem (x.input.sp - 8) .W64 x.input.rbx.toBitVec with
      | .error _ => .stuck "push"
      | .ok m₁ => match readRam x.input.policy m₁ x.input.j.toBitVec .W64 with
        | .error _ => .stuck "load"
        | .ok src =>
          match writeRam x.input.policy m₁ (x.input.sp - 16) .W64 retSumPC.toBitVec with
          | .error _ => .stuck "call"
          | .ok m₂ => .ok (.call () ⟨x.input.policy, m₂, x.len, UInt64.ofBitVec src⟩
              fun r => (.sumRet, { x with mem := m₂, acc := r }))
    | .sumRet, x =>
      if Clear x.input.sp (x.input.j.toBitVec + 24) then
        match writeRam x.input.policy x.mem (x.input.j.toBitVec + 24) .W64 x.acc.toBitVec with
        | .ok m => .ok (.ret (0, m))
        | .error _ => .stuck "store"
      else .stuck "store: private stack area"

def l2 : Model In2 (UInt64 × DataMem) where
  rep policy x s := x.policy = policy ∧ x.mem = s.data.dmem ∧ Entry policy s ∧
    s.data.regs.rdi = x.j ∧ x.sp = s.data.regs.rsp.toBitVec ∧ s.data.regs.rbx = x.rbx ∧
    SysV.StackRoom policy s 16
  returns x r := blocks.Returns (fun _ => Sum.l2.returns) .entry (init x) r
  post _ r s t := SysV.Exit s t ∧ t.data.regs.rax = r.1 ∧ t.data.dmem = r.2

/-! ## L2⁺: typed heap -/

/-- The L2⁺ input: the policy (for `Heap.Holds` in `post`), the heap, the record pointer. -/
structure In2p where
  policy : CpuPolicy
  heap : Heap
  j : UInt64

/-- An L2⁺ block state: the input, `len`, and the sum. -/
structure StP where
  input : In2p
  len : UInt64
  acc : UInt64

def initP (x : In2p) : StP := ⟨x, 0, 0⟩

/-- L2⁺: the same blocks on the heap; the stack is not in the heap. -/
def blocksP : Blocks Lbl StP (UInt64 × Heap) Unit (fun _ => Sum.In2p) (fun _ => UInt64) where
  step
    | .entry, x =>
      match x.input.heap.load (x.input.j.toBitVec + 8) .W64,
          x.input.heap.load (x.input.j.toBitVec + 16) .W64 with
      | .ok len, .ok limit =>
        .ok (.goto (if UInt64.ofBitVec len ≤ UInt64.ofBitVec limit then .callSum else .tooLong)
          { x with len := UInt64.ofBitVec len })
      | _, _ => .stuck "load"
    | .tooLong, x => .ok (.ret (1, x.input.heap))
    | .callSum, x =>
      match x.input.heap.load x.input.j.toBitVec .W64 with
      | .ok src => .ok (.call () ⟨x.input.heap, UInt64.ofBitVec src, x.len⟩
          fun r => (.sumRet, { x with acc := r }))
      | _ => .stuck "load"
    | .sumRet, x =>
      match x.input.heap.store (x.input.j.toBitVec + 24) .W64 x.acc.toBitVec with
      | .ok h => .ok (.ret (0, h))
      | _ => .stuck "store"

def l2p : Model In2p (UInt64 × Heap) where
  rep policy x s := x.policy = policy ∧ x.heap.Holds policy s.data.dmem ∧ Entry policy s ∧
    s.data.regs.rdi = x.j ∧ SysV.StackRoom policy s 16 ∧
    ∀ b, Private s.data.regs.rsp.toBitVec b → ¬ Covered x.heap b
  returns x r := blocksP.Returns (fun _ => Sum.l2p.returns) .entry (initP x) r
  post x r s t := SysV.Exit s t ∧ t.data.regs.rax = r.1 ∧ r.2.Holds x.policy t.data.dmem ∧
    ∀ b, ¬ x.heap.Owned b → ¬ SysV.Below s.data.regs.rsp.toBitVec 16 b →
      t.data.dmem.get? b = s.data.dmem.get? b

/-! ## L3: `JobSpec.run` -/

/-- The status in `rax`. -/
def code : JobSpec.Status → UInt64
  | .done => 0
  | .tooLong => 1

/-- The record `*j` (writable): `src`, `len` (the length of the array), `limit`, `total`. -/
def record (j src : BitVec 64) (x : JobSpec.In) (total : BitVec 64) : Obj :=
  ⟨j, true, [⟨.W64, src⟩, ⟨.W64, BitVec.ofNat 64 x.src.length⟩, ⟨.W64, x.limit⟩, ⟨.W64, total⟩]⟩

/-- The heap: the record at `j` with `total`, the read-only array at `src`, the other objects. -/
def heapOf (j src : BitVec 64) (frame : Heap) (x : JobSpec.In) (total : BitVec 64) : Heap :=
  record j src x total :: Obj.words src false .W64 x.src :: frame

/-- L3 for the policy `pol`, the record at `j`, the array at `src` and the other objects. -/
def l3 (pol : CpuPolicy) (j src : BitVec 64) (frame : Heap) : Model JobSpec.In JobSpec.Out where
  rep policy x s := policy = pol ∧ (heapOf j src frame x x.total).Holds policy s.data.dmem ∧
    Entry policy s ∧ s.data.regs.rdi.toBitVec = j ∧ SysV.StackRoom policy s 16 ∧
    ∀ b, Private s.data.regs.rsp.toBitVec b → ¬ Covered (heapOf j src frame x x.total) b
  returns x y := JobSpec.run x = some y
  post x y s t := SysV.Exit s t ∧ t.data.regs.rax = code y.status ∧
    (heapOf j src frame x y.total).Holds pol t.data.dmem ∧
    ∀ b, ¬ (heapOf j src frame x x.total).Owned b →
      ¬ SysV.Below s.data.regs.rsp.toBitVec 16 b → t.data.dmem.get? b = s.data.dmem.get? b

/-! ## Stack helpers (they use the fixed room of 16 bytes) -/

/-- A byte of the room is in the private area. -/
theorem private_of_below {sp b : BitVec 64} (h : SysV.Below sp 16 b) : Private sp b := by
  have : (b - (sp - 16)).toNat < 16 := h
  omega

/-- The 8 bytes at `a` outside the private area do not meet a word at `b` in the area. -/
theorem Clear.disjoint {sp a b : BitVec 64} (h : Clear sp a) (hb : (b - (sp - 16)).toNat ≤ 16) :
    ByteDisjoint a 8 b 8 := by
  intro i hi l hl e
  apply h i hi
  show (a + BitVec.ofNat 64 i - (sp - 16)).toNat < 24
  rw [e]
  bv_omega

/-- A push to the word at `rsp - k` of the room keeps a heap with no byte in the private area,
and keeps each byte outside the room. -/
theorem push_keeps {policy : CpuPolicy} {s : MachineState} {h : Heap} {m : DataMem} {k : Nat}
    (hk8 : 8 ≤ k) (hk : k ≤ 16) (harea : ∀ b, Private s.data.regs.rsp.toBitVec b → ¬ Covered h b)
    (hh : h.Holds policy m) (hout : SysV.Outside s 16 m) (v : Int) :
    h.Holds policy (Mem.storeInt m (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) 8 v) ∧
      SysV.Outside s 16 (Mem.storeInt m (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 k) 8 v) := by
  refine ⟨holds_congr hh fun b hc => ?_, hout.storeInt hk8 hk v⟩
  rw [Mem.get?_storeInt_of_ne _ _ _ _ _ fun i hi e => harea b (private_of_below (by
    subst e; unfold SysV.Below; bv_omega)) hc]

/-! ## The machine state at each label -/

/-- The callee-saved registers that `toyJob` does not push: the call of `toySum` keeps them. -/
def Kept (s u : MachineState) : Prop :=
  u.data.regs.rbp = s.data.regs.rbp ∧ u.data.regs.r12 = s.data.regs.r12 ∧
    u.data.regs.r13 = s.data.regs.r13 ∧ u.data.regs.r14 = s.data.regs.r14 ∧
    u.data.regs.r15 = s.data.regs.r15

/-- The entry state `s₀` at `pc`, with `len` in `rsi` and any flags. -/
def Branch (s₀ : MachineState) (len : UInt64) (pc : Int64) (s : MachineState) : Prop :=
  ∃ f, s = ⟨{ s₀.data with regs := { s₀.data.regs with rsi := len }, status := f }, pc⟩

/-- The machine state at each label, relative to the entry state `s₀`. At `sumRet` the memory
of the block state is the memory of the machine, with the pushed `rbx` at `sp - 8` and the
return word of `s₀` at `sp`. -/
def at_ (policy : CpuPolicy) (a : In2) (s₀ : MachineState) : Lbl → St → MachineState → Prop
  | .entry, x, s => s = s₀ ∧ l2.rep policy a s ∧ x = init a
  | .tooLong, x, s => l2.rep policy a s₀ ∧ x.input = a ∧ Branch s₀ x.len tooLongPC s
  | .callSum, x, s => l2.rep policy a s₀ ∧ x.input = a ∧ Branch s₀ x.len callSumPC s
  | .sumRet, x, u => l2.rep policy a s₀ ∧ x.input = a ∧ u.pc = retSumPC ∧
      u.data.regs.rax = x.acc ∧ u.data.regs.rbx = a.j ∧
      u.data.regs.rsp = s₀.data.regs.rsp - 8 ∧ Kept s₀ u ∧ u.data.dmem = x.mem ∧
      readRam policy x.mem (a.sp - 8) .W64 = .ok s₀.data.regs.rbx.toBitVec ∧
      ∃ ra, SysV.retAddr s₀ = some ra ∧ readRam policy x.mem a.sp .W64 = .ok ra.toBitVec

/-! ## The blocks -/

/-- The entry block: the code gets to `callSum` if `len ≤ limit`, else to `tooLong`. -/
theorem entry_code {policy : CpuPolicy} {a : In2} {s₀ : MachineState} {len limit : BitVec 64}
    (hrep : l2.rep policy a s₀)
    (hl : readRam a.policy a.mem (a.j.toBitVec + 8) .W64 = .ok len)
    (hm : readRam a.policy a.mem (a.j.toBitVec + 16) .W64 = .ok limit) :
    Reaches L1.step policy (at_ policy a s₀
      (if UInt64.ofBitVec len ≤ UInt64.ofBitVec limit then .callSum else .tooLong)
      { init a with len := UInt64.ofBitVec len }) s₀ := by
  obtain ⟨pol, mem, j, sp, rbx⟩ := a
  have h := hrep
  obtain ⟨rfl, rfl, he, rfl, rfl, rfl, -⟩ := h
  obtain ⟨d, pc⟩ := s₀
  obtain rfl : pc = toyJobPC := he.pc
  refine Sites.Job.entry he.exec d (len := UInt64.ofBitVec len) (limit := UInt64.ofBitVec limit)
    hl hm (fun hle f => ?_) (fun hgt f => ?_)
  · simp only [hle, ↓reduceIte]
    exact ⟨hrep, rfl, f, rfl⟩
  · simp only [UInt64.not_le.mpr hgt, ↓reduceIte]
    exact ⟨hrep, rfl, f, rfl⟩

/-- The block `tooLong`: the push of `1`, the pop to `rax`, the return. -/
theorem tooLong_code {policy : CpuPolicy} {a : In2} {s₀ s : MachineState} {x : St} {m : DataMem}
    (hat : at_ policy a s₀ .tooLong x s)
    (hw : writeRam x.input.policy x.input.mem (x.input.sp - 8) .W64 1 = .ok m) :
    Reaches L1.step policy (l2.post a (1, m) s₀) s := by
  obtain ⟨hrep, rfl, f, rfl⟩ := hat
  obtain ⟨⟨pol, mem, j, sp, rbx⟩, len, xm, acc⟩ := x
  obtain ⟨rfl, rfl, he, -, rfl, -, room⟩ := hrep
  obtain ⟨ra, hra⟩ := he.ret
  refine Sites.Job.tooLong he.exec _ hw
    (Sites.Stack.readRam_writeRam hw (room 8 (by decide) (by decide) (by decide)).2.1)
    (Sites.readRam_of_writeRam hw (SysV.ret_disjoint _ (by decide) (by decide))
      (Sites.readRet he hra)) fun _ => ⟨⟨hra, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- The block `callSum`: the code gets to the entry of `toySum(src, len)` with the memory `m₂`,
and from each return of it to `sumRet`. -/
theorem callSum_code {policy : CpuPolicy} {a : In2} {s₀ s : MachineState} {x : St}
    {m₁ m₂ : DataMem} {src : BitVec 64} (hat : at_ policy a s₀ .callSum x s)
    (hw₁ : writeRam x.input.policy x.input.mem (x.input.sp - 8) .W64 x.input.rbx.toBitVec =
      .ok m₁)
    (hr : readRam x.input.policy m₁ x.input.j.toBitVec .W64 = .ok src)
    (hw₂ : writeRam x.input.policy m₁ (x.input.sp - 16) .W64 retSumPC.toBitVec = .ok m₂) :
    Reaches L1.step policy (fun t =>
      Sum.l2.rep policy ⟨x.input.policy, m₂, x.len, UInt64.ofBitVec src⟩ t ∧
      ∀ z u, Sum.l2.post (⟨x.input.policy, m₂, x.len, UInt64.ofBitVec src⟩ : Sum.In2) z t u →
        at_ policy a s₀ .sumRet { x with mem := m₂, acc := z } u) s := by
  obtain ⟨hrep, rfl, f, rfl⟩ := hat
  obtain ⟨⟨pol, mem, j, sp, rbx⟩, len, xm, acc⟩ := x
  have h := hrep
  obtain ⟨rfl, rfl, he, rfl, rfl, rfl, room⟩ := h
  obtain ⟨ra, hra⟩ := he.ret
  refine Sites.Job.callSum he.exec _ (src := UInt64.ofBitVec src) hw₁ hr hw₂ fun f' =>
    ⟨⟨rfl, rfl, ⟨rfl, he.exec, ?_, retSumPC, Sites.Job.callSum_retAddr _ (src := UInt64.ofBitVec src) hw₂ f'⟩, rfl, rfl⟩, ?_⟩
  · rw [UInt64.toBitVec_sub]
    exact (room 16 (by decide) (by decide) (by decide)).2.1
  rintro z u ⟨⟨hpc, hsp, hbx, hbp, h12, h13, h14, h15⟩, hmem, hz⟩
  have hpc' : u.pc = retSumPC :=
    Option.some.inj (hpc.symm.trans (Sites.Job.callSum_retAddr _ (src := UInt64.ofBitVec src) hw₂ f'))
  have e : s₀.data.regs.rsp - 16 + 8 = s₀.data.regs.rsp - 8 := by bv_decide
  refine ⟨hrep, rfl, hpc', hz, hbx, hsp.trans e, ⟨hbp, h12, h13, h14, h15⟩, hmem, ?_, ra, hra,
    ?_⟩
  · exact Sites.readRam_of_writeRam hw₂ (SysV.slot_disjoint _ (by decide) (by decide))
      (Sites.Stack.readRam_writeRam hw₁ (room 8 (by decide) (by decide) (by decide)).2.1)
  · exact Sites.readRam_of_writeRam hw₂ (SysV.ret_disjoint _ (by decide) (by decide))
      (Sites.readRam_of_writeRam hw₁ (SysV.ret_disjoint _ (by decide) (by decide))
        (Sites.readRet he hra))

/-- The block `sumRet`: the store of the sum to `total`, `rax := 0`, the pop of `rbx`, the
return. -/
theorem sumRet_code {policy : CpuPolicy} {a : In2} {s₀ u : MachineState} {x : St} {m : DataMem}
    (hat : at_ policy a s₀ .sumRet x u) (hc : Clear x.input.sp (x.input.j.toBitVec + 24))
    (hw : writeRam x.input.policy x.mem (x.input.j.toBitVec + 24) .W64 x.acc.toBitVec = .ok m) :
    Reaches L1.step policy (l2.post a (0, m) s₀) u := by
  obtain ⟨d, pc⟩ := u
  obtain ⟨hrep, rfl, rfl, hax, hbx, hsp, ⟨hbp, h12, h13, h14, h15⟩, hmem, hsaved, ra, hra, hret⟩ :=
    hat
  obtain ⟨⟨pol, mem, j, sp, rbx⟩, len, xm, acc⟩ := x
  obtain ⟨hp, rfl, he, -, rfl, -, -⟩ := hrep
  simp only at hp
  subst pol
  have e₀ : d.regs.rsp.toBitVec = s₀.data.regs.rsp.toBitVec - 8 := by rw [hsp]; bv_decide
  have e₈ : d.regs.rsp.toBitVec + 8 = s₀.data.regs.rsp.toBitVec := by rw [hsp]; bv_decide
  have e₁₆ : d.regs.rsp + 16 = s₀.data.regs.rsp + 8 := by rw [hsp]; bv_decide
  have h₁ : writeRam policy d.dmem (d.regs.rbx.toBitVec + 24) .W64 d.regs.rax.toBitVec = .ok m := by
    rw [hmem, hbx, hax]
    exact hw
  have h₂ : readRam policy m d.regs.rsp.toBitVec .W64 = .ok s₀.data.regs.rbx.toBitVec := by
    rw [e₀]
    exact Sites.readRam_of_writeRam hw (hc.disjoint (by bv_omega)) hsaved
  have h₃ : readRam policy m (d.regs.rsp.toBitVec + 8) .W64 = .ok ra.toBitVec := by
    rw [e₈]
    exact Sites.readRam_of_writeRam hw (hc.disjoint (by bv_omega)) hret
  exact Sites.Job.sumRet he.exec d h₁ h₂ h₃ fun _ =>
    ⟨⟨hra, e₁₆, rfl, hbp, h12, h13, h14, h15⟩, rfl, rfl⟩

/-! ## The chain -/

theorem decompiles_l2 : Decompiles L1.step l2 := by
  refine Decompiles.ofBlocks blocks (fun _ => Sum.l2) (fun _ => Sum.decompiles_l2) .entry init at_
    (fun _ _ h => h) (fun _ _ _ h => ⟨rfl, h, rfl⟩) ?_
  rintro policy a s₀ (_ | _ | _ | _) x s hat n hn <;> simp only [blocks] at hn
  · obtain ⟨rfl, hrep, rfl⟩ := hat
    split at hn
    · rename_i hl hm
      cases hn
      exact entry_code hrep hl hm
    · cases hn
  · split at hn
    · rename_i hw
      cases hn
      exact tooLong_code hat hw
    · cases hn
  · split at hn
    · cases hn
    · rename_i hw₁
      split at hn
      · cases hn
      · rename_i hr
        split at hn
        · cases hn
        · rename_i hw₂
          cases hn
          exact callSum_code hat hw₁ hr hw₂
  · split at hn
    · rename_i hc
      split at hn
      · rename_i hw
        cases hn
        exact sumRet_code hat hc hw
      · cases hn
    · cases hn

/-! ## The relations between the levels -/

/-- L2⁺ and L2 inputs at the entry state `s`: the same policy and record pointer; the memory and
the stack pointer of `s`; the stack room; the memory holds the heap; no byte of the private area
is a byte of an object. -/
def SimIn (s : MachineState) (x : In2p) (y : In2) : Prop :=
  y.policy = x.policy ∧ y.mem = s.data.dmem ∧ y.sp = s.data.regs.rsp.toBitVec ∧ y.j = x.j ∧
    SysV.StackRoom x.policy s 16 ∧ x.heap.Holds x.policy y.mem ∧
    ∀ b, Private y.sp b → ¬ Covered x.heap b

/-- L2⁺ and L2 results: the same `rax`; the memory holds the heap; each byte that is not owned
and not in the room is the same. -/
def SimOut (x : In2p) (y : In2) (r : UInt64 × Heap) (r' : UInt64 × DataMem) : Prop :=
  r'.1 = r.1 ∧ r.2.Holds x.policy r'.2 ∧
    ∀ b, ¬ x.heap.Owned b → ¬ SysV.Below y.sp 16 b → r'.2.get? b = y.mem.get? b

/-- L2⁺ and L2 block states of the inputs `x` and `y`: the same `len` and sum; the memory of
the L2 state holds the heap and has the bytes of the input memory outside the room. -/
def SimSt (x : In2p) (y : In2) (u : StP) (v : St) : Prop :=
  u.input = x ∧ v.input = y ∧ v.len = u.len ∧ v.acc = u.acc ∧ x.heap.Holds x.policy v.mem ∧
    ∀ b, ¬ SysV.Below y.sp 16 b → v.mem.get? b = y.mem.get? b

/-- L3 and L2⁺ inputs: the heap is the record at `j`, the array at `src` and the frame; the
record pointer is `j`; some memory holds the heap. -/
def SimIn3 (j src : BitVec 64) (frame : Heap) (x : JobSpec.In) (y : In2p) : Prop :=
  y.heap = heapOf j src frame x x.total ∧ y.j.toBitVec = j ∧ ∃ m, y.heap.Holds y.policy m

/-- L3 and L2⁺ results: the status code in `rax`; the heap with the new total. -/
def SimOut3 (j src : BitVec 64) (frame : Heap) (x : JobSpec.In) (y : In2p) (out : JobSpec.Out)
    (r : UInt64 × Heap) : Prop :=
  y.heap = heapOf j src frame x x.total ∧ r.1 = code out.status ∧
    r.2 = heapOf j src frame x out.total

/-! ## The chain, from L2 -/

theorem refines_l2p (s : MachineState) : Refines (SimIn s) SimOut l2p.returns l2.returns := by
  intro xh xl r hs h
  refine Blocks.Returns.sim (fun _ => Sum.SimIn) (fun _ _ _ => Eq) (SimSt xh xl) (SimOut xh xl)
    (fun _ => Sum.refines_l2p) ?_ h ⟨rfl, rfl, rfl, rfl, hs.2.2.2.2.2.1, fun _ _ => rfl⟩
  obtain ⟨pol, heap, j⟩ := xh
  obtain ⟨pol', mem, j', sp, rbx⟩ := xl
  obtain ⟨rfl, rfl, rfl, rfl, room, hh₀, harea⟩ := hs
  have m8 := (room 8 (by decide) (by decide) (by decide)).2.2
  have m16 := (room 16 (by decide) (by decide) (by decide)).2.2
  rintro (_ | _ | _ | _) ⟨_, len, acc⟩ ⟨_, len', ym, acc'⟩ n ⟨rfl, rfl, rfl, rfl, hh, hout⟩ hn <;>
    simp only [blocksP] at hn
  · split at hn
    · rename_i lv mv hl hm
      cases hn
      refine ⟨⟨⟨pol', s.data.dmem, j', s.data.regs.rsp.toBitVec, rbx⟩, UInt64.ofBitVec lv, ym, acc'⟩,
        ?_, rfl, rfl, rfl, rfl, hh, hout⟩
      simp only [blocks, Heap.load_sound hh₀ hl, Heap.load_sound hh₀ hm]
    · cases hn
  · cases hn
    have hw : writeRam pol' s.data.dmem (s.data.regs.rsp.toBitVec - 8) .W64 1 = .ok _ :=
      room.writeRam (by decide) (by decide) (by decide) m8 _
    obtain ⟨hh', hout'⟩ := push_keeps (k := 8) (by decide) (by decide) harea hh₀ (SysV.Outside.rfl s 16)
      (1 : BitVec 64).toInt
    exact ⟨(1, Mem.storeInt s.data.dmem (s.data.regs.rsp.toBitVec - 8) 8 (1 : BitVec 64).toInt),
      by simp only [blocks, hw]; rfl, rfl, hh', fun b _ hb => hout' b hb⟩
  · split at hn
    · rename_i src hl
      cases hn
      have hw₁ : writeRam pol' s.data.dmem (s.data.regs.rsp.toBitVec - 8) .W64 rbx.toBitVec =
          .ok _ := room.writeRam (by decide) (by decide) (by decide) m8 _
      obtain ⟨hh₁, hout₁⟩ := push_keeps (k := 8) (by decide) (by decide) harea hh₀ (SysV.Outside.rfl s 16)
        rbx.toBitVec.toInt
      have hr := Heap.load_sound hh₁ hl
      have hw₂ : writeRam pol' (Mem.storeInt s.data.dmem (s.data.regs.rsp.toBitVec - 8#64) 8
          rbx.toBitVec.toInt) (s.data.regs.rsp.toBitVec - 16) .W64 retSumPC.toBitVec = .ok _ :=
        room.writeRam (k := 16) (by decide) (by decide) (by decide)
        (SysV.mapped_storeInt_of_disjoint
          (SysV.slot_disjoint (j := 8) (k := 16) _ (by decide) (by decide)).symm m16)
        retSumPC.toBitVec
      obtain ⟨hh₂, hout₂⟩ := push_keeps (k := 16) (by decide) (by decide) harea hh₁ hout₁
        retSumPC.toBitVec.toInt
      generalize Mem.storeInt (Mem.storeInt s.data.dmem (s.data.regs.rsp.toBitVec - 8#64) 8
        rbx.toBitVec.toInt) (s.data.regs.rsp.toBitVec - 16#64) 8 retSumPC.toBitVec.toInt = m₂
        at hw₂ hh₂ hout₂
      refine ⟨⟨pol', m₂, len', UInt64.ofBitVec src⟩, fun r =>
        (.sumRet, ⟨⟨pol', s.data.dmem, j', s.data.regs.rsp.toBitVec, rbx⟩, len', m₂, r⟩), ?_,
        ⟨rfl, rfl, hh₂⟩, ?_⟩
      · simp only [blocks, hw₁, hr, hw₂]
      · rintro y _ rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, hh₂, hout₂⟩
    · cases hn
  · split at hn
    · rename_i h' hst
      cases hn
      obtain ⟨m', hw, hh', hfr⟩ := Heap.store_frame hh hst
      have hc : Clear s.data.regs.rsp.toBitVec (j'.toBitVec + 24) := fun i hi hp =>
        harea _ hp (covered_of_owned (owned_of_store hh hst i hi))
      exact ⟨(0, m'), by simp only [blocks, eq_true hc, ↓reduceIte, hw], rfl, hh',
        fun b hb hr => (hfr b hb).trans (hout b hr)⟩
    · cases hn

theorem above_l2p : Above l2 l2p := by
  refine Above.ofRefines (fun _ s => SimIn s) (fun _ _ => SimOut) (fun _ s => refines_l2p s) ?_ ?_
  · rintro policy ⟨pol, heap, j⟩ s ⟨rfl, hh, he, hj, room, harea⟩
    exact ⟨⟨pol, s.data.dmem, j, s.data.regs.rsp.toBitVec, s.data.regs.rbx⟩,
      ⟨rfl, rfl, he, hj, rfl, rfl, room⟩, rfl, rfl, rfl, rfl, room, hh, harea⟩
  · rintro policy a b s r r' t - ⟨-, hm, -, -, hsp, -, -⟩ ⟨h1, hh, hfr⟩ ⟨hex, hax, hmem⟩
    refine ⟨hex, hax.trans h1, hmem ▸ hh, fun c hc hb => ?_⟩
    rw [hmem, hfr c hc (hsp ▸ hb), hm]

/-- The cells of the record. -/
theorem record_cell (j src : BitVec 64) (x : JobSpec.In) (total : BitVec 64) :
    (0, (⟨.W64, src⟩ : Cell)) ∈ offsets 0 (record j src x total).cells ∧
      (8, (⟨.W64, BitVec.ofNat 64 x.src.length⟩ : Cell)) ∈ offsets 0 (record j src x total).cells ∧
      (16, (⟨.W64, x.limit⟩ : Cell)) ∈ offsets 0 (record j src x total).cells := by
  simp [record, offsets, Width.bytes]

theorem refines_l3 (j src : BitVec 64) (frame : Heap) :
    Refines (SimIn3 j src frame) (SimOut3 j src frame) (fun x y => JobSpec.run x = some y)
      l2p.returns := by
  rintro x ⟨pol, heap, jj⟩ out ⟨hheap, hj, m, hh⟩ hr
  simp only at hheap hj hh
  subst hheap hj
  simp only [JobSpec.run] at hr
  split at hr
  · rename_i hlen
    cases hr
    have hO : record jj.toBitVec src x x.total ∈ heapOf jj.toBitVec src frame x x.total :=
      List.mem_cons_self ..
    obtain ⟨c0, c8, c16⟩ := record_cell jj.toBitVec src x x.total
    have hl : (heapOf jj.toBitVec src frame x x.total).load (jj.toBitVec + 8) .W64 =
        .ok (BitVec.ofNat 64 x.src.length) := Heap.load_cell hh hO c8
    have hm : (heapOf jj.toBitVec src frame x x.total).load (jj.toBitVec + 16) .W64 =
        .ok x.limit := Heap.load_cell hh hO c16
    have hle : UInt64.ofBitVec (BitVec.ofNat 64 x.src.length) ≤ UInt64.ofBitVec x.limit ↔
        ¬ x.limit.toNat < x.src.length := by
      rw [UInt64.le_iff_toNat_le]
      simp only [UInt64.toNat_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
      omega
    by_cases hlt : x.limit.toNat < x.src.length
    · simp only [hlt, ↓reduceIte]
      refine ⟨_, .goto (l' := .tooLong)
        (s' := ⟨⟨pol, heapOf jj.toBitVec src frame x x.total, jj⟩,
          UInt64.ofBitVec (BitVec.ofNat 64 x.src.length), 0⟩) ?_ (.ret rfl),
        rfl, rfl, rfl⟩
      simp only [blocksP, initP, hl, hm, mt hle.mp (not_not_intro hlt), ↓reduceIte]
    · simp only [hlt, ↓reduceIte]
      have hs : (heapOf jj.toBitVec src frame x x.total).load jj.toBitVec .W64 = .ok src := by
        have := Heap.load_cell hh hO c0
        rw [BitVec.add_zero] at this
        exact this
      obtain ⟨y, hy, hyv⟩ := Sum.refines_l3 x.src
        ⟨heapOf jj.toBitVec src frame x x.total, UInt64.ofBitVec src,
          UInt64.ofBitVec (BitVec.ofNat 64 x.src.length)⟩ x.src.sum
        ⟨⟨false, List.mem_cons_of_mem _ List.mem_cons_self⟩,
          by simp only [UInt64.toNat_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen],
          pol, m, hh⟩ rfl
      obtain ⟨h', hst, hrep⟩ := Heap.store_field hh hO rfl 3 (by simp [record]) .W64 rfl y.toBitVec
      have hst' : (heapOf jj.toBitVec src frame x x.total).store (jj.toBitVec + 24) .W64
          y.toBitVec = .ok h' := hst
      have hn := not_mem_of_holds hh rfl (by simp [record, Obj.size, Width.bytes])
      have e : h' = heapOf jj.toBitVec src frame x x.src.sum := by
        cases hrep with
        | here ht =>
          rw [replaces_eq_of_not_mem ht hn, hyv]
          rfl
        | there hne _ => exact absurd rfl hne
      have e₁ : blocksP.step .entry (initP ⟨pol, heapOf jj.toBitVec src frame x x.total, jj⟩) =
          .ok (.goto .callSum ⟨⟨pol, heapOf jj.toBitVec src frame x x.total, jj⟩,
            UInt64.ofBitVec (BitVec.ofNat 64 x.src.length), 0⟩) := by
        simp only [blocksP, initP, hl, hm, hle.mpr hlt, ↓reduceIte]
      have e₂ : blocksP.step .callSum ⟨⟨pol, heapOf jj.toBitVec src frame x x.total, jj⟩,
          UInt64.ofBitVec (BitVec.ofNat 64 x.src.length), 0⟩ =
          .ok (.call () ⟨heapOf jj.toBitVec src frame x x.total, UInt64.ofBitVec src,
            UInt64.ofBitVec (BitVec.ofNat 64 x.src.length)⟩ fun r =>
              (.sumRet, ⟨⟨pol, heapOf jj.toBitVec src frame x x.total, jj⟩,
                UInt64.ofBitVec (BitVec.ofNat 64 x.src.length), r⟩)) := by
        simp only [blocksP, hs]
      have e₃ : blocksP.step .sumRet ⟨⟨pol, heapOf jj.toBitVec src frame x x.total, jj⟩,
          UInt64.ofBitVec (BitVec.ofNat 64 x.src.length), y⟩ = .ok (.ret (0, h')) := by
        simp only [blocksP, hst']
      exact ⟨_, .goto e₁ (.call e₂ hy (.ret e₃)), rfl, rfl, e⟩
  · cases hr

theorem above_l3 (pol : CpuPolicy) (j src : BitVec 64) (frame : Heap) :
    Above l2p (l3 pol j src frame) := by
  refine Above.ofRefines (fun _ _ => SimIn3 j src frame) (fun _ _ => SimOut3 j src frame)
    (fun _ _ => refines_l3 j src frame) ?_ ?_
  · rintro policy x s ⟨rfl, hh, he, hj, room, harea⟩
    exact ⟨⟨policy, heapOf j src frame x x.total, s.data.regs.rdi⟩, ⟨rfl, hh, he, rfl, room, harea⟩,
      rfl, hj, _, hh⟩
  · rintro policy x b s out r t ⟨rfl, -⟩ ⟨hpol, -⟩ ⟨hb, h1, h2⟩ ⟨hex, hax, hh, hfr⟩
    rw [hpol, h2] at hh
    rw [hb] at hfr
    exact ⟨hex, hax.trans h1, hh, hfr⟩

theorem decompiles : ∀ pol j src frame, Decompiles L1.step (l3 pol j src frame) :=
  fun pol j src frame => (decompiles_l2.above above_l2p).above (above_l3 pol j src frame)

/-- The same theorem for the Kraken step function. -/
theorem decompiles_code :
    ∀ pol j src frame, Decompiles (fun s => Code.code.step s .done) (l3 pol j src frame) :=
  fun pol j src frame =>
    (Sites.decompiles_l1Spec_iff Code.code L1.step L1.spec (l3 pol j src frame)).mp
      (decompiles pol j src frame)

/-- The end theorem: for each input in `C` and each entry state, the code returns a result of
L3. -/
theorem contract (pol : CpuPolicy) (j src : BitVec 64) (frame : Heap) :
    ∀ policy x s, (l3 pol j src frame).rep policy x s → JobSpec.C x →
      Reaches (fun s => Code.code.step s .done) policy
        (fun t => ∃ y, (l3 pol j src frame).post x y s t ∧ JobSpec.run x = some y) s :=
  Decompiles.transfer (decompiles_code pol j src frame) JobSpec.C (fun x y => JobSpec.run x = some y)
    JobSpec.total fun _ _ _ h => h

end Lift.Spike.Job
