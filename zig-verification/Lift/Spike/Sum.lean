module

public import Lift.Sem.Sim
public import Lift.Sem.Heap
public import Lift.Spike.Sites.Sum

@[expose] public section

/-! T3 `toySum` (a loop that sums a read-only array of `u64`): the chain `code ⇒ L2 ⇒ L2⁺ ⇒ L3`.

L2 and L2⁺ have one block for each basic block of the assembly; each block proof uses one block
lemma of `Lift/Spike/Sites/Sum.lean`. The loop invariant and the measure are only in
`refines_l3`. The words of L2 and L2⁺ are `UInt64` (the registers); the words of L3 are
`BitVec 64` (the heap cells). -/

namespace Lift.Spike.Sum

open Lift.P2.Total Lift.Sem

/-! ## The models -/

/-- The L2 input: the policy, the memory, the pointer `rdi` and the count `rsi`. -/
structure In2 where
  policy : CpuPolicy
  mem : DataMem
  rsi : UInt64
  rdi : UInt64

/-- The L2⁺ input: the heap, the pointer `rdi` and the count `rsi`. -/
structure In2p where
  heap : Heap
  rdi : UInt64
  rsi : UInt64

/-- The basic blocks of the assembly. -/
inductive Lbl where
  | entry
  | LBB1_1
  | o9
  | LBB1_3

/-- A block state: the input, the index (`rcx`) and the sum (`rax`). -/
structure St (I : Type) where
  input : I
  rax : UInt64
  rcx : UInt64

/-- The state at the entry; the entry block sets the index and the sum. -/
def init {I : Type} (a : I) : St I := ⟨a, 0, 0⟩

/-- L2: the body reads the element with `readRam`. -/
def blocks : Leaf Lbl (St In2) UInt64 where
  step
    | .entry, x => .ok (.goto .LBB1_1 { x with rcx := 0, rax := 0 })
    | .LBB1_1, x => .ok (if x.input.rsi = x.rcx then .goto .LBB1_3 x else .goto .o9 x)
    | .o9, x =>
      match readRam x.input.policy x.input.mem (x.input.rdi.toBitVec + x.rcx.toBitVec * 8) .W64 with
      | .ok v => .ok (.goto .LBB1_1 { x with rcx := x.rcx + 1, rax := x.rax + UInt64.ofBitVec v })
      | .error _ => .stuck "read"
    | .LBB1_3, x => .ok (.ret x.rax)

/-- L2⁺: the body loads the element from the heap. -/
def blocksP : Leaf Lbl (St In2p) UInt64 where
  step
    | .entry, x => .ok (.goto .LBB1_1 { x with rcx := 0, rax := 0 })
    | .LBB1_1, x => .ok (if x.input.rsi = x.rcx then .goto .LBB1_3 x else .goto .o9 x)
    | .o9, x =>
      match x.input.heap.load (x.input.rdi.toBitVec + x.rcx.toBitVec * 8) .W64 with
      | .ok v => .ok (.goto .LBB1_1 { x with rcx := x.rcx + 1, rax := x.rax + UInt64.ofBitVec v })
      | .stuck why => .stuck why
      | .noFuel => .noFuel
    | .LBB1_3, x => .ok (.ret x.rax)

/-- The return of L2 and L2⁺: `r` in `rax`; the memory is unchanged. -/
def post {A : Type} (_ : A) (r : UInt64) (s t : MachineState) : Prop :=
  SysV.Exit s t ∧ t.data.dmem = s.data.dmem ∧ t.data.regs.rax = r

def l2 : Model In2 UInt64 where
  rep policy a s := a.policy = policy ∧ a.mem = s.data.dmem ∧
    SysV.Entry policy toyJobPC toyEndPC toySumPC s ∧ s.data.regs.rsi = a.rsi ∧ s.data.regs.rdi = a.rdi
  returns a r := blocks.Returns noCall .entry (init a) r
  post := post

def l2p : Model In2p UInt64 where
  rep policy a s := a.heap.Holds policy s.data.dmem ∧
    SysV.Entry policy toyJobPC toyEndPC toySumPC s ∧ s.data.regs.rdi = a.rdi ∧ s.data.regs.rsi = a.rsi
  returns a r := blocksP.Returns noCall .entry (init a) r
  post := post

/-- L3: the wrapping sum. -/
def run (xs : List (BitVec 64)) : Option (BitVec 64) := some xs.sum

/-- The contract: the inputs on which L3 must return. -/
def C (_ : List (BitVec 64)) : Prop := True

theorem total : ∀ xs, C xs → ∃ y, run xs = some y :=
  fun xs _ => ⟨xs.sum, rfl⟩

/-- L3 for an array at `p` (writable if `wr`) in a heap with the other objects `frame`. -/
def l3 (p : BitVec 64) (wr : Bool) (frame : Heap) : Model (List (BitVec 64)) (BitVec 64) where
  rep policy xs s := Heap.Holds policy (Obj.words p wr .W64 xs :: frame) s.data.dmem ∧
    SysV.Entry policy toyJobPC toyEndPC toySumPC s ∧ s.data.regs.rdi.toBitVec = p ∧
    s.data.regs.rsi.toNat = xs.length
  returns xs y := run xs = some y
  post _ y s t := SysV.Exit s t ∧ t.data.dmem = s.data.dmem ∧ t.data.regs.rax.toBitVec = y

/-! ## The relations -/

/-- The call state `s₀` at `pc`, with the sum in `rax`, the index in `rcx` and any flags. -/
def Loop (s₀ : MachineState) (x : St In2) (pc : Int64) (s : MachineState) : Prop :=
  ∃ f, s = ⟨{ s₀.data with regs := { s₀.data.regs with rax := x.rax, rcx := x.rcx }, status := f },
    pc⟩

/-- The machine state at each block of L2, relative to the call state `s₀`. -/
def At (s₀ : MachineState) : Lbl → St In2 → MachineState → Prop
  | .entry, _, s => s = s₀
  | .LBB1_1, x, s => Loop s₀ x Sites.Sum.headPC s
  | .o9, x, s => Loop s₀ x Sites.Sum.bodyPC s
  | .LBB1_3, x, s => Loop s₀ x Sites.Sum.exitPC s

/-- The L2⁺ input and the L2 input: the same arguments; the memory and the policy hold the
heap. -/
def SimIn (a : In2p) (b : In2) : Prop := a.rdi = b.rdi ∧ a.rsi = b.rsi ∧ a.heap.Holds b.policy b.mem

/-- The L3 input and the L2⁺ input: the array `xs` is an object of the heap at `p` and `n` is its
length; a memory holds the heap. -/
def SimArr (xs : List (BitVec 64)) (a : In2p) : Prop :=
  (∃ wr, Obj.words a.rdi.toBitVec wr .W64 xs ∈ a.heap) ∧ a.rsi.toNat = xs.length ∧
    ∃ policy m, a.heap.Holds policy m

/-! ## The chain -/

theorem decompiles_l2 : Decompiles L1.step l2 := by
  refine Decompiles.ofBlocks blocks noCallee (fun f => f.elim) .entry init
    (fun policy a s₀ l x s => l2.rep policy a s₀ ∧ x.input = a ∧ At s₀ l x s)
    (fun _ _ h => h) (fun _ _ _ h => ⟨h, rfl, rfl⟩) ?_
  rintro policy a s₀ l x s ⟨hrep, rfl, hat⟩ n hn
  have ⟨hpol, hmem, he, hn', hp⟩ := hrep
  obtain ⟨ra, hra⟩ := he.ret
  have hx := he.exec
  cases l with
  | entry =>
    cases hat
    simp only [blocks, Res.ok.injEq] at hn
    subst hn
    obtain ⟨d, pc⟩ := s₀
    obtain rfl : pc = toySumPC := he.pc
    exact Sites.Sum.entry hx d fun f => ⟨hrep, rfl, f, rfl⟩
  | LBB1_1 =>
    obtain ⟨f, rfl⟩ := hat
    simp only [blocks] at hn
    refine Sites.Sum.head hx _ (fun h f' => ?_) (fun h f' => ?_)
    · have e : x.input.rsi = x.rcx := by rw [← hn']; exact h
      simp only [e, ↓reduceIte, Res.ok.injEq] at hn
      subst hn
      exact ⟨hrep, rfl, f', rfl⟩
    · have e : x.input.rsi ≠ x.rcx := by rw [← hn']; exact h
      simp only [e, ↓reduceIte, Res.ok.injEq] at hn
      subst hn
      exact ⟨hrep, rfl, f', rfl⟩
  | o9 =>
    obtain ⟨f, rfl⟩ := hat
    simp only [blocks] at hn
    split at hn
    · rename_i v hv
      simp only [Res.ok.injEq] at hn
      subst hn
      rw [hpol, hmem, ← hp] at hv
      exact Sites.Sum.body hx _ (UInt64.ofBitVec v) hv fun f' => ⟨hrep, rfl, f', rfl⟩
    · cases hn
  | LBB1_3 =>
    obtain ⟨f, rfl⟩ := hat
    simp only [blocks, Res.ok.injEq] at hn
    subst hn
    refine Sites.Sum.exit hx _ ra ?_ fun _ => ⟨⟨hra, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
    exact Sites.readRet he hra

/-- The block states of L2⁺ and L2: related inputs, the same index and the same sum. -/
def SimSt (x : St In2p) (y : St In2) : Prop := SimIn x.input y.input ∧ x.rcx = y.rcx ∧ x.rax = y.rax

theorem refines_l2p : Refines SimIn (fun _ _ => Eq) l2p.returns l2.returns := by
  intro a b r hs h
  refine Blocks.Returns.sim (fun f => f.elim) (fun f => f.elim) SimSt Eq (fun f => f.elim) ?_ h
    ⟨hs, rfl, rfl⟩
  rintro l x y n ⟨⟨hp, hn, hh⟩, hi, hacc⟩ hstep
  cases l with
  | entry =>
    simp only [blocksP, Res.ok.injEq] at hstep
    subst hstep
    exact ⟨_, rfl, ⟨hp, hn, hh⟩, rfl, rfl⟩
  | LBB1_1 =>
    simp only [blocksP, Res.ok.injEq] at hstep
    subst hstep
    by_cases hc : x.input.rsi = x.rcx <;> simp only [hc, ↓reduceIte] <;>
      exact ⟨y, by simp only [blocks, ← hn, ← hi, hc, ↓reduceIte], ⟨hp, hn, hh⟩, hi, hacc⟩
  | o9 =>
    simp only [blocksP] at hstep
    split at hstep
    · rename_i v hv
      simp only [Res.ok.injEq] at hstep
      subst hstep
      have hr := Heap.load_sound hh hv
      rw [hp, hi] at hr
      refine ⟨{ y with rcx := y.rcx + 1, rax := y.rax + UInt64.ofBitVec v }, ?_, ⟨hp, hn, hh⟩,
        by simp [hi], by simp [hacc]⟩
      simp only [blocks, hr]
    · cases hstep
    · cases hstep
  | LBB1_3 =>
    simp only [blocksP, Res.ok.injEq] at hstep
    subst hstep
    exact ⟨y.rax, rfl, hacc⟩

theorem refines_l3 :
    Refines SimArr (fun _ _ y r => r.toBitVec = y) (fun xs y => run xs = some y) l2p.returns := by
  rintro xs a y ⟨⟨wr, ho⟩, hn, policy, m, hh⟩ hy
  simp only [run, Option.some.injEq] at hy
  subst hy
  -- The invariant: at the head, the sum and the sum of the elements from the index give the sum.
  have loop : ∀ x : St In2p, x.input = a ∧ x.rcx.toNat ≤ xs.length →
      blocksP.Returns noCall .LBB1_1 x (x.rax + UInt64.ofBitVec (xs.drop x.rcx.toNat).sum) := by
    refine Blocks.Returns.loop _ (fun x : St In2p => xs.length - x.rcx.toNat)
      (fun x : St In2p => x.rax + UInt64.ofBitVec (xs.drop x.rcx.toNat).sum) ?_
    rintro x ⟨rfl, hle⟩ ih
    by_cases hc : x.rcx.toNat = xs.length
    · have e : x.input.rsi = x.rcx := UInt64.toNat_inj.mp (hn.trans hc.symm)
      refine .goto (l' := .LBB1_3) (s' := x) (by simp only [blocksP, e, ↓reduceIte]) (.ret ?_)
      simp [blocksP, hc]
    · have hlt : x.rcx.toNat < xs.length := by omega
      have e : x.input.rsi ≠ x.rcx := fun e => hc (by rw [← hn, e])
      have hl := Heap.load_words64 hh ho hlt
      rw [BitVec.mul_comm] at hl
      have hi : (x.rcx + 1).toNat = x.rcx.toNat + 1 := by
        have := x.input.rsi.toNat_lt
        rw [UInt64.toNat_add]
        exact Nat.mod_eq_of_lt (by simp; omega)
      let x' : St In2p := { x with rcx := x.rcx + 1, rax := x.rax + UInt64.ofBitVec xs[x.rcx.toNat] }
      have h3 := ih x' ⟨rfl, by simp only [x', hi]; omega⟩ (by simp only [x', hi]; omega)
      refine .goto (l' := .o9) (s' := x) (by simp only [blocksP, e, ↓reduceIte])
        (.goto (l' := .LBB1_1) (s' := x') (by simp only [blocksP, hl]; rfl) ?_)
      simp only [x', hi] at h3
      rw [List.drop_eq_getElem_cons hlt, List.sum_cons, UInt64.ofBitVec_add, ← UInt64.add_assoc]
      exact h3
  exact ⟨_, .goto rfl (loop ⟨a, 0, 0⟩ ⟨rfl, Nat.zero_le _⟩), by simp⟩

theorem above_l2p : Above l2 l2p := by
  refine Above.ofRefines (fun _ _ => SimIn) (fun _ _ _ _ => Eq) (fun _ _ => refines_l2p) ?_ ?_
  · rintro policy a s ⟨hh, he, hp, hn⟩
    exact ⟨⟨policy, s.data.dmem, a.rsi, a.rdi⟩, ⟨rfl, rfl, he, hn, hp⟩, rfl, rfl, hh⟩
  · rintro _ _ _ _ _ _ _ _ _ rfl ht
    exact ht

theorem above_l3 (p : BitVec 64) (wr : Bool) (frame : Heap) : Above l2p (l3 p wr frame) := by
  refine Above.ofRefines (fun _ _ => SimArr) (fun _ _ _ _ y r => r.toBitVec = y)
    (fun _ _ => refines_l3) ?_ ?_
  · rintro policy xs s ⟨hh, he, hp, hn⟩
    refine ⟨⟨Obj.words p wr .W64 xs :: frame, s.data.regs.rdi, s.data.regs.rsi⟩, ⟨hh, he, rfl, rfl⟩,
      ⟨wr, ?_⟩, hn, policy, _, hh⟩
    rw [hp]
    exact List.mem_cons_self
  · rintro _ _ _ _ _ _ _ _ _ hr ⟨hx, hm, ht⟩
    exact ⟨hx, hm, by rw [ht, hr]⟩

theorem decompiles : ∀ p wr frame, Decompiles L1.step (l3 p wr frame) :=
  fun p wr frame => (decompiles_l2.above above_l2p).above (above_l3 p wr frame)

/-- The same theorem for the Kraken step function. -/
theorem decompiles_code :
    ∀ p wr frame, Decompiles (fun s => Code.code.step s .done) (l3 p wr frame) :=
  fun p wr frame => (Sites.decompiles_l1Spec_iff Code.code L1.step L1.spec (l3 p wr frame)).mp
    (decompiles p wr frame)

/-- The end theorem: for each array in `C` and each entry state, the code returns the sum. -/
theorem contract : ∀ p wr frame policy xs s, (l3 p wr frame).rep policy xs s → C xs →
    Reaches (fun s => Code.code.step s .done) policy
      (fun t => ∃ y, (l3 p wr frame).post xs y s t ∧ run xs = some y) s :=
  fun p wr frame => Decompiles.transfer (decompiles_code p wr frame) C (fun xs y => run xs = some y)
    total fun _ _ _ h => h

end Lift.Spike.Sum
