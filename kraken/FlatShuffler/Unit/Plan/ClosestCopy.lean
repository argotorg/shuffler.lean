module

public import FlatShuffler.Unit.Plan.Frame
import all FlatShuffler.Unit.Plan.Frame
public import FlatShuffler.Unit.Plan.Specs
import all FlatShuffler.Unit.Plan.Specs
public import FlatShuffler.Unit.ShallowestCopy
import all FlatShuffler.Unit.ShallowestCopy
public import FlatShuffler.Asm
import all FlatShuffler.Asm
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

/-!
# `MappingBuilder::closestCopy`

`Names.closestCopy` in `build/kraken/c/build_bottom_up.S`: no call, no store. If `m = 0` it returns `-1` at once. Else it
pushes `r15`, `r14`, `rbp`, `rbx` and runs the loop over the source positions `rax < m`. `r11`
is the best position so far. Each turn of the loop is one unfold of `Flat.closestFrom`.
`t` is `rsi`, the `CopyLocation` is `dl`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit

open FlatShuffler.Sep

def closestA (b : BG) (s : MachineData) : Prop := (rsi s).toNat < b.n.toNat

-- `cmpb $1, %dl`: the `CopyLocation` is `InWildcardSlot`.
abbrev closestW (s : MachineData) : Bool := (rdx s).setWidth 8 == 1#8

def closestQ (b b' : BG) (s t : MachineData) : Prop :=
  b' = b ∧ rax t = Flat.closestCopy b.fl b.M (rsi s) (closestW s)

namespace ClosestU

-- The saved registers, in the order of the stack words from low to high.
def fr (s : MachineData) : List Word :=
  [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]

-- The registers in the loop.
structure CI (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop where
  kb : Kb (BView B b ∗ F) s ra (fr s) 32#64 t
  rdi : t.regs.rdi.toBitVec = B
  rsi : t.regs.rsi.toBitVec = b.m
  r10 : t.regs.r10.toBitVec = s.regs.rsi.toBitVec
  rbx : t.regs.rbx.toBitVec = b.tgt
  r9 : t.regs.r9.toBitVec = b.src
  r8 : StackSlot.ofWord t.regs.r8.toBitVec = Flat.get b.fl.target s.regs.rsi.toBitVec
  rcx : t.regs.rcx.toBitVec = t.regs.rax.toBitVec - s.regs.rsi.toBitVec
  bpl : t.regs.rbp.toBitVec.setWidth 8 = BitVec.ofNat 8 (closestW s).toNat
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  lt : t.regs.rax.toBitVec.toNat < b.m.toNat

-- Position `rax` holds a copy of the target slot that `map` can take.
def Cand (b : BG) (s t : MachineData) : Prop :=
  Flat.get b.fl.source t.regs.rax.toBitVec = Flat.get b.fl.target s.regs.rsi.toBitVec
    ∧ Flat.mappable b.fl b.M t.regs.rax.toBitVec = true

-- The rest of the loop from position `i` with the best position `r11`.
abbrev Rest (b : BG) (s t : MachineData) (i : Word) : Prop :=
  Flat.closestFrom b.fl b.M s.regs.rsi.toBitVec (closestW s) i t.regs.r11.toBitVec
    = Flat.closestCopy b.fl b.M s.regs.rsi.toBitVec (closestW s)

/-! ### One turn of the loop -/

section
variable {fb : Flat.Builder} {M : Flat.Mapping} {p inW : Bool} {t i best : Word}

theorem from_ge (h : ¬ i < fb.m) : Flat.closestFrom fb M t inW i best = best := by
  rw [Flat.closestFrom, dite_eq_right h]

theorem from_lt (h : i < fb.m) : Flat.closestFrom fb M t inW i best
    = Flat.closestFrom fb M t inW (i + 1)
      (if Flat.get fb.source i = Flat.get fb.target t && Flat.mappable fb M i
          && Flat.inWildcardSlot fb i == inW then
        if best = Flat.NONE || Flat.absDiff i t ≤ Flat.absDiff best t then i else best
      else best) := by
  rw [Flat.closestFrom, dite_eq_left h]

-- Position `i` is not a candidate: the best position does not change.
theorem from_skip (h : i < fb.m)
    (hc : (Flat.get fb.source i = Flat.get fb.target t && Flat.mappable fb M i
      && Flat.inWildcardSlot fb i == inW) = false) :
    Flat.closestFrom fb M t inW i best = Flat.closestFrom fb M t inW (i + 1) best := by
  rw [from_lt h, hc]; rfl

-- Position `i` is a candidate.
theorem from_take (h : i < fb.m) (hs : Flat.get fb.source i = Flat.get fb.target t)
    (hm : Flat.mappable fb M i = true) (hw : (Flat.inWildcardSlot fb i == inW) = true) :
    Flat.closestFrom fb M t inW i best = Flat.closestFrom fb M t inW (i + 1)
      (if best = Flat.NONE || Flat.absDiff i t ≤ Flat.absDiff best t then i else best) := by
  rw [from_lt h]; simp [hs, hm, hw]
end

/-! ### Flags -/

-- `cmpb $1, %dl; sete %bpl`.
theorem cmp1_byte (x : Word) :
    (BitVec.extractLsb' 0 8 x - 1#8 == BitVec.zero 8) = (x.setWidth 8 == 1#8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor <;> intro h <;> bv_decide

-- `cmpb %dl, %bpl`: the `CopyLocation` of position `rax` is the `CopyLocation` of the call.
theorem wild_flag {x y : Word} {a c : Bool} (hx : x.setWidth 8 = BitVec.ofNat 8 a.toNat)
    (hy : y.setWidth 8 = BitVec.ofNat 8 c.toNat) :
    (BitVec.extractLsb' 0 8 x - BitVec.extractLsb' 0 8 y == BitVec.zero 8) = (c == a) := by
  have ex : BitVec.extractLsb' 0 8 x = x.setWidth 8 := by bv_decide
  have ey : BitVec.extractLsb' 0 8 y = y.setWidth 8 := by bv_decide
  rw [ex, ey, hx, hy]
  cases a <;> cases c <;> decide

-- `cmpq 24(%rdi), %rax; jnb`: the carry flag.
theorem nb_true {a c : Word}
    (h : (!(((a - c).toNat : Int) != (a.toNat : Int) - (c.toNat : Int))) = true) :
    c.toNat ≤ a.toNat := by
  rw [Bool.not_eq_true', bne_eq_false_iff_eq] at h
  rw [BitVec.toNat_sub] at h
  have := a.isLt; have := c.isLt
  omega

theorem nb_false {a c : Word}
    (h : (!(((a - c).toNat : Int) != (a.toNat : Int) - (c.toNat : Int))) = false) :
    a.toNat < c.toNat := by
  rw [Bool.not_eq_false', bne_iff_ne] at h
  rw [BitVec.toNat_sub] at h
  have := a.isLt; have := c.isLt
  omega

-- The carry flag of `cmpq y, x` in a `cmovb`.
theorem bor_iff (x y : Word) :
    ((((x - y).toNat : Int) != (x.toNat : Int) - (y.toNat : Int)) = true) ↔ x < y := by
  rw [bne_iff_ne, BitVec.toNat_sub, BitVec.lt_def]
  have := x.isLt; have := y.isLt
  constructor <;> intro h <;> omega

-- The carry flag of `cmpq y, x` in a `cmovnb`.
theorem nb_iff (x y : Word) :
    ((!(((x - y).toNat : Int) != (x.toNat : Int) - (y.toNat : Int))) = true) ↔ y ≤ x := by
  rw [Bool.not_eq_true', bne_eq_false_iff_eq, BitVec.toNat_sub, BitVec.le_def]
  have := x.isLt; have := y.isLt
  constructor <;> intro h <;> omega

-- `movq %r10, %rdx; subq %rax, %rdx; cmpq %rax, %r10; cmovb %rcx, %rdx` with `rcx = rax - r10`.
theorem absD_i (i t : Word) : (if t < i then i - t else t - i) = Flat.absDiff i t := by
  unfold Flat.absDiff; rfl

-- `movq %r11, %r14; subq %r10, %r14; …; cmpq %r11, %r10; cmovnb %r15, %r14`.
theorem absD_r (r t : Word) : (if r ≤ t then t - r else r - t) = Flat.absDiff r t := by
  unfold Flat.absDiff
  by_cases h : r ≤ t
  · simp only [h, ↓reduceIte, show ¬ r > t by bv_omega]
  · simp only [h, ↓reduceIte, show r > t by bv_omega]

-- `cmpb $0, (%rdx,%rax)`.
theorem byte_ne0 (x : BitVec 8) : (!(x - 0#8 == BitVec.zero 8)) = !(x == 0) := by
  simp

theorem slot_ne {a y : Word} {X Y : StackSlot} (h8 : StackSlot.ofWord a = X)
    (hy : StackSlot.ofWord y = Y) (h : StackSlot.ofWord a ≠ StackSlot.ofWord y) : X ≠ Y :=
  h8 ▸ hy ▸ h

theorem slot_eq {a y : Word} {X Y : StackSlot} (h8 : StackSlot.ofWord a = X)
    (hy : StackSlot.ofWord y = Y) (h : StackSlot.ofWord a = StackSlot.ofWord y) : X = Y :=
  h8 ▸ hy ▸ h

section
variable {fb : Flat.Builder} {M : Flat.Mapping} {inW : Bool} {t i best : Word}

theorem skip_slot (h : i < fb.m) (hs : Flat.get fb.target t ≠ Flat.get fb.source i) :
    Flat.closestFrom fb M t inW i best = Flat.closestFrom fb M t inW (i + 1) best :=
  from_skip h (by simp [Ne.symm hs])

theorem skip_drop (h : i < fb.m) (hd : (!(Flat.get fb.dropped i == 0)) = true) :
    Flat.closestFrom fb M t inW i best = Flat.closestFrom fb M t inW (i + 1) best := by
  rw [Bool.not_eq_true'] at hd
  exact from_skip h (by simp only [Flat.mappable, hd, Bool.false_and, Bool.and_false])

theorem skip_dest (h : i < fb.m) (hd : (!(Flat.get M.dest i == Flat.NONE)) = true) :
    Flat.closestFrom fb M t inW i best = Flat.closestFrom fb M t inW (i + 1) best := by
  rw [Bool.not_eq_true'] at hd
  exact from_skip h (by simp only [Flat.mappable, hd, Bool.false_and, Bool.and_false])

theorem mappable_of (hd : (!(Flat.get fb.dropped i == 0)) = false)
    (hm : (!(Flat.get M.dest i == Flat.NONE)) = false) : Flat.mappable fb M i = true := by
  rw [Bool.not_eq_false'] at hd hm
  simp only [Flat.mappable, hd, hm, Bool.and_self]

theorem inWS_ge (h : fb.n.toNat ≤ i.toNat) : Flat.inWildcardSlot fb i = false := by
  simp [Flat.inWildcardSlot, BitVec.lt_def, Nat.not_lt.2 h]

-- `cmpb $1, 4(%rbx,%rax,8)`: the kind of target slot `i` is `Junk`.
theorem kind_flag {x : BitVec 8} (hn : i.toNat < fb.n.toNat)
    (hk : x = (Flat.get fb.target i).kind) :
    (x - 1#8 == BitVec.zero 8) = Flat.inWildcardSlot fb i := by
  have e : (x - 1#8 == BitVec.zero 8) = (x == Junk) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    unfold Junk
    constructor <;> intro h <;> bv_decide
  rw [e, hk]
  simp [Flat.inWildcardSlot, Flat.isWildcardTarget, isJunk, BitVec.lt_def, hn]

-- `movl $0, %edx` and `jnb`.
theorem rdx_ge (h : fb.n.toNat ≤ i.toNat) :
    BitVec.setWidth 8 (0#64) = BitVec.ofNat 8 (Flat.inWildcardSlot fb i).toNat := by
  rw [inWS_ge h]; rfl

-- `movl $0, %edx` and `sete %dl`.
theorem rdx_kind {x : BitVec 8} (hn : i.toNat < fb.n.toNat) (hk : x = (Flat.get fb.target i).kind) :
    BitVec.setWidth 8 ((0#64).replaceLow (BitVec.ofNat 8 (x - 1#8 == BitVec.zero 8).toNat))
      = BitVec.ofNat 8 (Flat.inWildcardSlot fb i).toNat := by
  rw [IsSpilled.setWidth_replaceLow, kind_flag hn hk]
end

section
variable {B : Addr} {b : BG} {F : MProp 64} {s t t' : MachineData} {ra : Int64}

-- A step that writes only the flags.
theorem CI.flags {st} (h : CI B b F s ra t) : CI B b F s ra { t with status := st } :=
  ⟨h.kb.next rfl rfl, h.rdi, h.rsi, h.r10, h.rbx, h.r9, h.r8, h.rcx, h.bpl, h.r12, h.r13, h.lt⟩

-- A step that keeps the memory and the registers of `CI`.
theorem CI.same (h : CI B b F s ra t) (hm : t'.dmem = t.dmem) (hsp : t'.regs.rsp = t.regs.rsp)
    (hdi : t'.regs.rdi = t.regs.rdi) (hsi : t'.regs.rsi = t.regs.rsi)
    (h10 : t'.regs.r10 = t.regs.r10) (hbx : t'.regs.rbx = t.regs.rbx)
    (h9 : t'.regs.r9 = t.regs.r9) (h8 : t'.regs.r8 = t.regs.r8) (hcx : t'.regs.rcx = t.regs.rcx)
    (hax : t'.regs.rax = t.regs.rax) (hbp : t'.regs.rbp = t.regs.rbp)
    (h12 : t'.regs.r12 = t.regs.r12) (h13 : t'.regs.r13 = t.regs.r13) : CI B b F s ra t' :=
  ⟨h.kb.next hm hsp, by rw [hdi]; exact h.rdi, by rw [hsi]; exact h.rsi, by rw [h10]; exact h.r10,
    by rw [hbx]; exact h.rbx, by rw [h9]; exact h.r9, by rw [h8]; exact h.r8,
    by rw [hcx, hax]; exact h.rcx, by rw [hbp]; exact h.bpl, by rw [h12]; exact h.r12,
    by rw [h13]; exact h.r13, by rw [hax]; exact h.lt⟩

-- A step that keeps the memory and `rsp` stays at or below the frame of the call.
theorem CI.stk (h : CI B b F s ra t) (hm : t'.dmem = t.dmem) (hsp : t'.regs.rsp = t.regs.rsp) :
    t'.StackAtOrBelow (s.pushRa ra) :=
  (h.kb.next hm hsp).stack (by decide)
end

/-! ### The exit -/

-- The addresses of `popq %rbx; popq %rbp; popq %r14; popq %r15`.
theorem pop_addr (a : Word) :
    a = a + BitVec.ofNat 64 (8 * 0) ∧ a + 8#64 = a + BitVec.ofNat 64 (8 * 1)
      ∧ a + 8#64 + 8#64 = a + BitVec.ofNat 64 (8 * 2)
      ∧ a + 8#64 + 8#64 + 8#64 = a + BitVec.ofNat 64 (8 * 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

section
variable {P : MProp 64} {s t : MachineData} {ra : Int64}

theorem pop_isSome (h : Kb P s ra (fr s) 32#64 t) :
    (t.dmem.loadInt t.regs.rsp.toBitVec 8).isSome = true
      ∧ (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome = true
      ∧ (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64 + 8#64) 8).isSome = true
      ∧ (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64) 8).isSome = true := by
  obtain ⟨e0, e1, e2, e3⟩ := pop_addr t.regs.rsp.toBitVec
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0]; exact h.isSome_fr rfl (by simp [fr])
  · rw [e1]; exact h.isSome_fr rfl (by simp [fr])
  · rw [e2]; exact h.isSome_fr rfl (by simp [fr])
  · rw [e3]; exact h.isSome_fr rfl (by simp [fr])

-- The state after the pops.
theorem pop_kg (h : Kb P s ra (fr s) 32#64 t) (h12 : t.regs.r12 = s.regs.r12)
    (h13 : t.regs.r13 = s.regs.r13) :
    Kg P s ra (fr s)
      { regs :=
          { rax := t.regs.r11, rbx := { toBitVec := rd t.dmem t.regs.rsp.toBitVec },
            rcx := t.regs.rcx, rdx := t.regs.rdx, rsi := t.regs.rsi, rdi := t.regs.rdi,
            rsp := { toBitVec := t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 },
            rbp := { toBitVec := rd t.dmem (t.regs.rsp.toBitVec + 8#64) },
            r8 := t.regs.r8, r9 := t.regs.r9, r10 := t.regs.r10, r11 := t.regs.r11,
            r12 := t.regs.r12, r13 := t.regs.r13,
            r14 := { toBitVec := rd t.dmem (t.regs.rsp.toBitVec + 8#64 + 8#64) },
            r15 := { toBitVec := rd t.dmem (t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64) } },
        zmms := t.zmms, status := t.status, dmem := t.dmem } := by
  obtain ⟨e0, e1, e2, e3⟩ := pop_addr t.regs.rsp.toBitVec
  refine h.kg rfl ?_ ?_ ?_ h12 h13 ?_ ?_ <;> (try apply UInt64.toBitVec_inj.mp) <;> dsimp only
  · rw [h.sp]; bv_omega
  · rw [e0]; exact h.rd_fr rfl (by simp [fr])
  · rw [e1]; exact h.rd_fr rfl (by simp [fr])
  · rw [e2]; exact h.rd_fr rfl (by simp [fr])
  · rw [e3]; exact h.rd_fr rfl (by simp [fr])
end


/-! ### The invariant, the variant and the obligation of a block -/

-- The invariant of each label. `fr₀` is the frame of the caller.
def Inv (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) (fr₀ : List Word) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.closestCopy then t = s.pushRa ra
    else if l = ".LB.MappingBuilder.closestCopy.0" then CI B b F s ra t ∧ Cand b s t
      ∧ t.regs.rdx.toBitVec.setWidth 8
        = BitVec.ofNat 8 (Flat.inWildcardSlot b.fl t.regs.rax.toBitVec).toNat
      ∧ Rest b s t t.regs.rax.toBitVec
    else if l = ".LB.MappingBuilder.closestCopy.1" then
      CI B b F s ra t ∧ Rest b s t (t.regs.rax.toBitVec + 1#64)
    else if l = ".LB.MappingBuilder.closestCopy.2" then
      CI B b F s ra t ∧ Rest b s t t.regs.rax.toBitVec
    else if l = ".LB.MappingBuilder.closestCopy.3" then CI B b F s ra t ∧ Cand b s t
      ∧ (Flat.inWildcardSlot b.fl t.regs.rax.toBitVec == closestW s) = true
      ∧ Rest b s t t.regs.rax.toBitVec
    else if l = ".LB.MappingBuilder.closestCopy.4" then CI B b F s ra t ∧ Cand b s t
      ∧ (Flat.inWildcardSlot b.fl t.regs.rax.toBitVec == closestW s) = true
      ∧ Rest b s t t.regs.rax.toBitVec ∧ t.regs.r11.toBitVec = Flat.NONE
    else if l = ".LB.MappingBuilder.closestCopy.5" then Kg (BView B b ∗ F) s ra fr₀ t
      ∧ Flat.closestCopy b.fl b.M s.regs.rsi.toBitVec (closestW s) = Flat.NONE
    else if l = ".LB.MappingBuilder.closestCopy.6" then Kb (BView B b ∗ F) s ra (fr s) 32#64 t
      ∧ t.regs.r12 = s.regs.r12 ∧ t.regs.r13 = s.regs.r13
      ∧ t.regs.r11.toBitVec = Flat.closestCopy b.fl b.M s.regs.rsi.toBitVec (closestW s)
    else False

-- The variant. A turn of the loop decreases `m - rax`.
def V (b : BG) (l : Label) (t : MachineData) : Nat :=
  if l = Names.closestCopy then 2 ^ 70
  else if l = ".LB.MappingBuilder.closestCopy.2" then 8 * (b.m.toNat - (rax t).toNat) + 7
  else if l = ".LB.MappingBuilder.closestCopy.0" then 8 * (b.m.toNat - (rax t).toNat) + 6
  else if l = ".LB.MappingBuilder.closestCopy.3" then 8 * (b.m.toNat - (rax t).toNat) + 5
  else if l = ".LB.MappingBuilder.closestCopy.4" then 8 * (b.m.toNat - (rax t).toNat) + 4
  else if l = ".LB.MappingBuilder.closestCopy.1" then 8 * (b.m.toNat - (rax t).toNat) + 3
  else 0

-- The exception continuation of the body triple.
def E (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost BView BG.Ok B F 4 (fun a' t => closestQ b a' s t) s t
    ∧ Sep.mod.Agree s t

-- The obligation of `Program.WP.cfg` for the block `blk`.
def Obl [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (fr₀ : List Word) (blk : Program.Block) : Prop :=
  ∀ t, Inv B b F s ra fr₀ blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv B b F s ra fr₀ c u ∧ Program.Decreases (V b) blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels closestCopyAsm) (s.pushRa ra) I' (E B b F s ra)) t

-- The labels of `closestCopyAsm`, in the order of the blocks.
def labels : List CfgLabel :=
  [.entry, .label Names.closestCopy,
    .label ".LB.MappingBuilder.closestCopy.0", .label ".LB.MappingBuilder.closestCopy.1",
    .label ".LB.MappingBuilder.closestCopy.2", .label ".LB.MappingBuilder.closestCopy.3",
    .label ".LB.MappingBuilder.closestCopy.4", .label ".LB.MappingBuilder.closestCopy.5",
    .label ".LB.MappingBuilder.closestCopy.6"]

theorem labels_cover : closestCopyAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.closestCopy]
  cfg_labels

-- The invariant of a label, and the variant.
macro "cc_inv" : tactic => `(tactic|
  simp only [Inv, Rest, Names.closestCopy, String.reduceEq, ↓reduceIte])
macro "cc_inv" "at" h:ident : tactic => `(tactic|
  simp only [Inv, Rest, Names.closestCopy, String.reduceEq, ↓reduceIte] at $h:ident)
macro "cc_var" : tactic => `(tactic|
  simp only [V, Names.closestCopy, String.reduceEq, ↓reduceIte, rax, Reg64s.get64_rax])

/-! ### The blocks -/

open ShallowestCopy

section
variable [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (fr₀ : List Word)

theorem b_entry : closestCopyAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  cc_inv
  exact ht

theorem b_fn (hpre : VPre BView BG.Ok B b F closestA 4 s) (hfr : fr₀.length = 4)
    (hk0 : Kg (BView B b ∗ F) s ra fr₀ (s.pushRa ra)) :
    closestCopyAsm.ForallBlocks fun blk =>
      blk.label = .label Names.closestCopy → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl, Names.closestCopy]
  intro t ht
  cc_inv at ht
  subst ht
  have hok := hpre.ok
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = B := by
    simpa [MachineData.pushRa] using hpre.rdi
  have hm0 := hk0.vmem
  have hrsi : (s.pushRa ra).regs.rsi = s.regs.rsi := rfl
  have hlt : s.regs.rsi.toBitVec.toNat < b.n.toNat := hpre.args
  have hq : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by
    rw [← Reg64s.get64_rsp, hk0.sp64]
  have hsp4 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64
      = rsp s - 8#64 - 32#64 := by
    rw [hq]; bv_omega
  obtain ⟨hpo, hpm⟩ := hk0.pushes (xs := [(s.pushRa ra).regs.r15.toBitVec,
    (s.pushRa ra).regs.r14.toBitVec, (s.pushRa ra).regs.rbp.toBitVec,
    (s.pushRa ra).regs.rbx.toBitVec]) (by simp [hfr])
  rw [hfr] at hpm
  simp only [pushes] at hpm
  simp only [PushOk] at hpo
  obtain ⟨p1, p2, p3, p4, -⟩ := hpo
  have hb4 := hpm
  rw [sep_lc] at hb4
  have h_m := BView.rd_m hm0
  have h_tgt := BView.rd_tgt hb4
  have h_src := BView.rd_src hb4
  have h_r8 := BView.rd_tw hb4 hok hlt
  unfold rd at h_m h_tgt h_src h_r8
  have k_m := BView.isSome_m hm0
  have k_tgt := BView.isSome_tgt hb4
  have k_src := BView.isSome_src hb4
  have k_tw := BView.isSome_tw hb4 hok hlt
  clear hm0 hb4
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hrdi, hrsi, h_m, h_tgt, h_src, fold_slot] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_m
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
    | with_reducible exact p4
    | with_reducible exact k_tgt
    | with_reducible exact k_src
    | with_reducible exact k_tw
  | goto ".LB.MappingBuilder.closestCopy.5" =>
    have h0 := zf_true (by with_reducible assumption)
    cfg_goto
    · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
    · cc_inv
      exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl,
        from_ge (by show ¬ (0 : Word) < b.m; rw [h0]; decide)⟩
    · simp [V, Names.closestCopy]
  | goto ".LB.MappingBuilder.closestCopy.2" =>
    have h0 := zf_false (by with_reducible assumption)
    cfg_goto
    · exact Kb.stack ⟨hpm, hsp4⟩ (by decide)
    · cc_inv
      refine ⟨⟨⟨hpm, hsp4⟩, by simpa [MachineData.pushRa] using hpre.rdi, rfl, rfl, rfl, rfl, h_r8,
        by bv_omega, ?_, rfl, rfl,
        Nat.pos_of_ne_zero fun h => h0 (BitVec.eq_of_toNat_eq h)⟩, rfl⟩
      show BitVec.setWidth 8 (BitVec.replaceLow _ _) = _
      rw [IsSpilled.setWidth_replaceLow, cmp1_byte]; rfl
    · left; have := b.m.isLt; simp [V, Names.closestCopy]; omega

theorem b_0 : closestCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.closestCopy.0" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  cc_inv at ht
  obtain ⟨hci, hcand, hdx, hrest⟩ := ht
  have hw := wild_flag hci.bpl hdx
  have hlt : t.regs.rax.toBitVec < b.fl.m := BitVec.lt_def.2 hci.lt
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hw] at *
  vc_by_shape
  | goto ".LB.MappingBuilder.closestCopy.3" =>
    cfg_goto
    · exact hci.stk rfl rfl
    · cc_inv
      exact ⟨hci.flags, hcand, by assumption, hrest⟩
    · left; simp [V, Names.closestCopy]
  | other =>
    first
    | (left; cc_var; omega)
    | (cc_inv
       refine ⟨hci.flags, (from_skip hlt ?_).symm.trans hrest⟩
       simp only [decide_eq_true hcand.1, hcand.2, Bool.true_and]
       assumption)

theorem b_1 : closestCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.closestCopy.1" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  cc_inv at ht
  obtain ⟨hci, hrest⟩ := ht
  have hsi := hci.rsi
  have hlt := hci.lt
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [sub_beq_zero] at *
  vc_by_shape
  | goto ".LB.MappingBuilder.closestCopy.6" =>
    have he : (1#64 + t.regs.rax.toBitVec == t.regs.rsi.toBitVec) = true := by assumption
    rw [beq_iff_eq, hsi] at he
    cfg_goto
    · exact hci.stk rfl rfl
    · cc_inv
      refine ⟨hci.kb.next rfl rfl, hci.r12, hci.r13, (from_ge fun h => ?_).symm.trans hrest⟩
      rw [BitVec.add_comm, he] at h
      exact Nat.lt_irrefl _ (BitVec.lt_def.1 h)
    · left; simp [V, Names.closestCopy]
  | other =>
    have hne : (1#64 + t.regs.rax.toBitVec == t.regs.rsi.toBitVec) = false := by assumption
    rw [beq_eq_false_iff_ne, hsi] at hne
    first
    | (left; cc_var; bv_omega)
    | (cc_inv
       refine ⟨⟨hci.kb.next rfl rfl, hci.rdi, hci.rsi, hci.r10, hci.rbx, hci.r9, hci.r8, ?_,
          hci.bpl, hci.r12, hci.r13, ?_⟩, ?_⟩
       · show 1#64 + t.regs.rcx.toBitVec = 1#64 + t.regs.rax.toBitVec - s.regs.rsi.toBitVec
         rw [hci.rcx]; bv_omega
       · show (1#64 + t.regs.rax.toBitVec).toNat < b.m.toNat
         bv_omega
       · rw [BitVec.add_comm]; exact hrest)

theorem b_2 (hok : b.Ok) : closestCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.closestCopy.2" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  cc_inv at ht
  obtain ⟨hci, hrest⟩ := ht
  have hb := hci.kb.mem
  rw [sep_lc] at hb
  have hdi := hci.rdi
  have h9 := hci.r9
  have hbx := hci.rbx
  have hlt := hci.lt
  have hlt' : t.regs.rax.toBitVec < b.fl.m := BitVec.lt_def.2 hlt
  have hmax : t.regs.rax.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hlt hok.m
  obtain ⟨_, hM⟩ := BView.mapM hb
  have h_drp := BView.rd_drp hb
  have h_mp := BView.rd_mp hb
  have h_n := BView.rd_n hb
  have h_db := BView.rdb_drp hb hok hlt
  have h_dst := MapM.rd_dest hM hmax
  have h_sw := BView.rd_sw hb hok hlt
  unfold rd at h_drp h_mp h_n h_dst h_sw
  unfold rdb at h_db
  have k_sw := BView.isSome_sw hb hok hlt
  have k_drp := BView.isSome_drp hb
  have k_db := BView.isSome_drp_byte hb hok hlt
  have k_mp := BView.isSome_mp hb
  have k_dst := MapM.isSome_dest hM hmax
  have k_n := BView.isSome_n hb
  have k_kind := fun (i : Word) (hi : i.toNat < b.n.toNat) => BView.isSome_kind hb hok hi
  have k_rk := fun (i : Word) (hi : i.toNat < b.n.toNat) => BView.rdb_kind hb hok hi
  clear hb hM
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hdi, h9, hbx, h_drp, h_mp, h_n, h_db, h_dst, fold_slot, sub_beq_zero,
    neg_one_eq_none, byte_ne0] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_sw
    | with_reducible exact k_drp
    | with_reducible exact k_db
    | with_reducible exact k_mp
    | with_reducible exact k_dst
    | with_reducible exact k_n
    | (refine k_kind _ (nb_false ?_); with_reducible assumption)
  | closed => decide
  | goto ".LB.MappingBuilder.closestCopy.1" =>
    cfg_goto
    · exact hci.stk rfl rfl
    · cc_inv
      refine ⟨hci.same rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, Eq.trans ?_ hrest⟩
      first
      | (refine (skip_slot hlt' (slot_ne hci.r8 h_sw (jne_true ?_))).symm
         with_reducible assumption)
      | (refine (skip_drop hlt' ?_).symm; with_reducible assumption)
      | (refine (skip_dest hlt' ?_).symm; with_reducible assumption)
    · left; simp [V, Names.closestCopy]
  | goto ".LB.MappingBuilder.closestCopy.0" =>
    cfg_goto
    · exact hci.stk rfl rfl
    · cc_inv
      refine ⟨hci.same rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
        ⟨(slot_eq hci.r8 h_sw (jne_false ?_)).symm, mappable_of ?_ ?_⟩, ?_, hrest⟩
      · with_reducible assumption
      · with_reducible assumption
      · with_reducible assumption
      · first
        | (refine rdx_ge (nb_true (c := b.n) ?_); with_reducible assumption)
        | (refine rdx_kind (nb_false (c := b.n) ?_) (k_rk _ (nb_false (c := b.n) ?_)) <;>
            with_reducible assumption)
    · left; simp [V, Names.closestCopy]

theorem b_3 : closestCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.closestCopy.3" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  cc_inv at ht
  obtain ⟨hci, hcand, hw, hrest⟩ := ht
  have hlt' : t.regs.rax.toBitVec < b.fl.m := BitVec.lt_def.2 hci.lt
  have hcx := hci.rcx
  have h10 := hci.r10
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [sub_beq_zero, neg_one_eq_none] at *
  vc_by_shape
  | goto ".LB.MappingBuilder.closestCopy.4" =>
    have hn : (t.regs.r11.toBitVec == Flat.NONE) = true := by assumption
    cfg_goto
    · exact hci.stk rfl rfl
    · cc_inv
      exact ⟨hci.flags, hcand, hw, hrest, beq_iff_eq.1 hn⟩
    · left; simp [V, Names.closestCopy]
  | goto ".LB.MappingBuilder.closestCopy.1" =>
    have hn : (t.regs.r11.toBitVec == Flat.NONE) = false := by assumption
    rw [beq_eq_false_iff_ne] at hn
    cfg_goto
    · exact hci.stk rfl rfl
    · cc_inv
      refine ⟨hci.same rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, Eq.trans ?_ hrest⟩
      rw [from_take hlt' hcand.1 hcand.2 hw]
      congr 1
      simp only [hcx, h10]
      simp only [bor_iff, nb_iff, absD_i, absD_r]
      by_cases hp : Flat.absDiff t.regs.rax.toBitVec s.regs.rsi.toBitVec
          ≤ Flat.absDiff t.regs.r11.toBitVec s.regs.rsi.toBitVec <;> simp [hp, hn]
    · left; simp [V, Names.closestCopy]

theorem b_4 : closestCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.closestCopy.4" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  cc_inv at ht
  obtain ⟨hci, hcand, hw, hrest, hn⟩ := ht
  have hlt' : t.regs.rax.toBitVec < b.fl.m := BitVec.lt_def.2 hci.lt
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.MappingBuilder.closestCopy.1" =>
    cfg_goto
    · exact hci.stk rfl rfl
    · cc_inv
      refine ⟨hci.same rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, Eq.trans ?_ hrest⟩
      rw [from_take hlt' hcand.1 hcand.2 hw]
      congr 1
      simp [hn]
    · left; simp [V, Names.closestCopy]

theorem b_5 (hok : b.Ok) (hfr : fr₀.length = 4) : closestCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.closestCopy.5" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  cc_inv at ht
  obtain ⟨hk, hc⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | retAddr =>
    exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
  | ret =>
    refine Kg.vret (ok := BG.Ok) (a' := b) (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) hfr hok
      fun t' _ hax => ⟨rfl, ?_⟩
    rw [hax]
    exact hc.symm

theorem b_6 (hok : b.Ok) : closestCopyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.closestCopy.6" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  cc_inv at ht
  obtain ⟨hk, h12, h13, h11⟩ := ht
  obtain ⟨p0, p1, p2, p3⟩ := pop_isSome hk
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact p0
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
  | retAddr => exact Option.isSome_iff_exists.mpr ⟨ra, (pop_kg hk h12 h13).retAddr⟩
  | ret =>
    refine Kg.vret (ok := BG.Ok) (a' := b) (pop_kg hk h12 h13) rfl hok fun t' _ hax => ⟨rfl, ?_⟩
    rw [hax]
    exact h11

end

end ClosestU

open ClosestU in
theorem closestCopy_unit [Host] [FunDecls] : BThm closestCopyAsm closestA 4 closestQ := by
  intro B b F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr₀, hfr, hk0⟩ := hpre.kg ra
  refine Program.WP.cfg (ClosestU.Inv B b F s ra fr₀) (ClosestU.V b) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry B b F s ra fr₀
  · exact b_fn B b F s ra fr₀ hpre hfr hk0
  · exact b_0 B b F s ra fr₀
  · exact b_1 B b F s ra fr₀
  · exact b_2 B b F s ra fr₀ hpre.ok
  · exact b_3 B b F s ra fr₀
  · exact b_4 B b F s ra fr₀
  · exact b_5 B b F s ra fr₀ hpre.ok hfr
  · exact b_6 B b F s ra fr₀ hpre.ok

end FlatShuffler.Unit
