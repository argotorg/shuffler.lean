module

public import FlatShuffler.Unit.StackCall
import all FlatShuffler.Unit.StackCall
public import FlatShuffler.Sep.Stores
import all FlatShuffler.Sep.Stores
public import ProofKit.Cfg
import all ProofKit.Cfg
public import ProofKit.Idioms
import all ProofKit.Idioms

@[expose] public section

/-! The stack frame of `produce`: six saved registers, three local words,
plus a return slot and two free words for its callees. -/
namespace FlatShuffler.Unit.ProduceProof
open FlatShuffler.Sep

structure Scratch where
  a : Word
  b : Word
  ret : Word
  lo : Word
  hi : Word

def saved (s : MachineData) (y : Scratch) (k : Word) : List Word :=
  [y.a, y.b, y.ret, y.lo, k, y.hi, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec,
    s.regs.r12.toBitVec, s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]

theorem stk12 (sp : Addr) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 v : Word) :
    Stk sp [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] v
      = Wd (sp - 104#64) x0 ∗ Wd (sp - 96#64) x1 ∗ Wd (sp - 88#64) x2 ∗ Wd (sp - 80#64) x3 ∗ Wd (sp - 72#64) x4 ∗ Wd (sp - 64#64) x5 ∗ Wd (sp - 56#64) x6 ∗ Wd (sp - 48#64) x7 ∗ Wd (sp - 40#64) x8 ∗ Wd (sp - 32#64) x9 ∗ Wd (sp - 24#64) x10 ∗ Wd (sp - 16#64) x11
        ∗ Wd (sp - 8#64) v := by
  unfold Stk
  simp only [Arr, List.length_cons, List.length_nil, MProp.sep_emp, MProp.sep_assoc]
  rw [show sp - 8#64 - BitVec.ofNat 64 (8 * (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = sp - 104#64 by bv_omega,
    show sp - 104#64 + 8#64 = sp - 96#64 by bv_omega,
    show sp - 96#64 + 8#64 = sp - 88#64 by bv_omega,
    show sp - 88#64 + 8#64 = sp - 80#64 by bv_omega,
    show sp - 80#64 + 8#64 = sp - 72#64 by bv_omega,
    show sp - 72#64 + 8#64 = sp - 64#64 by bv_omega,
    show sp - 64#64 + 8#64 = sp - 56#64 by bv_omega,
    show sp - 56#64 + 8#64 = sp - 48#64 by bv_omega,
    show sp - 48#64 + 8#64 = sp - 40#64 by bv_omega,
    show sp - 40#64 + 8#64 = sp - 32#64 by bv_omega,
    show sp - 32#64 + 8#64 = sp - 24#64 by bv_omega,
    show sp - 24#64 + 8#64 = sp - 16#64 by bv_omega]

def Fr (s : MachineData) (ra : Int64) (y : Scratch) (k : Word) (F : MProp 64) : MProp 64 :=
  Wd (rsp s - 80#64) y.lo ∗ Wd (rsp s - 72#64) k ∗ Wd (rsp s - 64#64) y.hi
    ∗ Wd (rsp s - 56#64) s.regs.rbx.toBitVec
    ∗ Wd (rsp s - 48#64) s.regs.rbp.toBitVec ∗ Wd (rsp s - 40#64) s.regs.r12.toBitVec
    ∗ Wd (rsp s - 32#64) s.regs.r13.toBitVec ∗ Wd (rsp s - 24#64) s.regs.r14.toBitVec
    ∗ Wd (rsp s - 16#64) s.regs.r15.toBitVec ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F

theorem stk2 (sp : Addr) (y : Scratch) :
    Stk (sp - 80#64) [y.a, y.b] y.ret =
      Wd (sp - 104#64) y.a ∗ Wd (sp - 96#64) y.b ∗ Wd (sp - 88#64) y.ret := by
  unfold Stk
  simp only [Arr, List.length_cons, List.length_nil, MProp.sep_emp, MProp.sep_assoc]
  rw [show sp - 80#64 - 8#64 - BitVec.ofNat 64 (8 * (0 + 1 + 1)) = sp - 104#64 by bv_omega,
    show sp - 104#64 + 8#64 = sp - 96#64 by bv_omega,
    show sp - 80#64 - 8#64 = sp - 88#64 by bv_omega]

theorem frame_eq (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (y : Scratch) (k : Word) :
    View S g ∗ Stk (rsp s - 80#64) [y.a, y.b] y.ret ∗ Fr s ra y k F =
      View S g ∗ Stk (rsp s) (saved s y k) ra.toBitVec ∗ F := by
  unfold saved
  rw [stk12, stk2]
  unfold Fr
  ecancel

-- A load from a word atom.
theorem isSome_at {P R : MProp 64} {m : Mem 64} (a : Addr) (v : Word) (h : P.get m)
    (e : P = Wd a v ∗ R) : (m.loadInt a 8).isSome = true :=
  Wd.isSome (e ▸ h)

-- A store to a word atom.
theorem st_at {P R : MProp 64} {m : Mem 64} (a : Addr) (v : Word) (h : P.get m)
    (e : P = Wd a v ∗ R) (w : Word) : (Wd a w ∗ R).get (m.storeInt a 8 w.toInt) :=
  Wd.store (e ▸ h) w

theorem store_all {P P' R : MProp 64} {m : Mem 64} {a : Addr} {v : Word}
    (h : P.get m) (e : P = Wd a v ∗ R) (w : Word) (e' : P' = Wd a w ∗ R) :
    P'.get (m.storeInt a 8 w.toInt) :=
  e'.symm ▸ Wd.store (e ▸ h) w

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64}

-- The 6 `pushq` from the entry stack (`r` is `rsp` after the call): the loads before the stores,
-- and the memory after them.
theorem pushes {m : Mem 64} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word}
    (hm : (View S g ∗ Stk (rsp s) [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] ra.toBitVec ∗ F).get m)
    {r a b c d e f : Word} (hr : r = rsp s - 8#64) (ha : a = s.regs.r15.toBitVec)
    (hb : b = s.regs.r14.toBitVec) (hc : c = s.regs.r13.toBitVec) (hd : d = s.regs.r12.toBitVec)
    (he : e = s.regs.rbp.toBitVec) (hf : f = s.regs.rbx.toBitVec) :
    (m.loadInt (r - 8#64) 8).isSome = true
    ∧ ((m.storeInt (r - 8#64) 8 a.toInt).loadInt (r - 8#64 - 8#64) 8).isSome = true
    ∧ (((m.storeInt (r - 8#64) 8 a.toInt).storeInt (r - 8#64 - 8#64) 8 b.toInt).loadInt
        (r - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ ((((m.storeInt (r - 8#64) 8 a.toInt).storeInt (r - 8#64 - 8#64) 8 b.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64) 8 c.toInt).loadInt (r - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ (((((m.storeInt (r - 8#64) 8 a.toInt).storeInt (r - 8#64 - 8#64) 8 b.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64) 8 c.toInt).storeInt (r - 8#64 - 8#64 - 8#64 - 8#64) 8 d.toInt).loadInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ ((((((m.storeInt (r - 8#64) 8 a.toInt).storeInt (r - 8#64 - 8#64) 8 b.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64) 8 c.toInt).storeInt (r - 8#64 - 8#64 - 8#64 - 8#64) 8 d.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 e.toInt).loadInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ (View S g ∗ Stk (rsp s - 80#64) [x0, x1] x2 ∗ Fr s ra ⟨x0, x1, x2, x3, x5⟩ x4 F).get
        ((((((m.storeInt (r - 8#64) 8 a.toInt).storeInt (r - 8#64 - 8#64) 8 b.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64) 8 c.toInt).storeInt (r - 8#64 - 8#64 - 8#64 - 8#64) 8 d.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 e.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 f.toInt) := by
  subst hr ha hb hc hd he hf
  rw [stk12] at hm
  rw [show rsp s - 8#64 - 8#64 = rsp s - 16#64 by bv_omega,
    show rsp s - 16#64 - 8#64 = rsp s - 24#64 by bv_omega,
    show rsp s - 24#64 - 8#64 = rsp s - 32#64 by bv_omega,
    show rsp s - 32#64 - 8#64 = rsp s - 40#64 by bv_omega,
    show rsp s - 40#64 - 8#64 = rsp s - 48#64 by bv_omega,
    show rsp s - 48#64 - 8#64 = rsp s - 56#64 by bv_omega]
  have h1 := st_at (rsp s - 16#64) x11 hm (by ecancel) s.regs.r15.toBitVec
  have h2 := st_at (rsp s - 24#64) x10 h1 (by ecancel) s.regs.r14.toBitVec
  have h3 := st_at (rsp s - 32#64) x9 h2 (by ecancel) s.regs.r13.toBitVec
  have h4 := st_at (rsp s - 40#64) x8 h3 (by ecancel) s.regs.r12.toBitVec
  have h5 := st_at (rsp s - 48#64) x7 h4 (by ecancel) s.regs.rbp.toBitVec
  have h6 := st_at (rsp s - 56#64) x6 h5 (by ecancel) s.regs.rbx.toBitVec
  refine ⟨isSome_at _ x11 hm (by ecancel), isSome_at _ x10 h1 (by ecancel),
    isSome_at _ x9 h2 (by ecancel), isSome_at _ x8 h3 (by ecancel), isSome_at _ x7 h4 (by ecancel),
    isSome_at _ x6 h5 (by ecancel), ?_⟩
  rw [stk2 (rsp s) ⟨x0, x1, x2, x3, x5⟩]
  unfold Fr
  simp only [MProp.sep_assoc]
  have he : Wd (rsp s - 56#64) s.regs.rbx.toBitVec ∗ Wd (rsp s - 48#64) s.regs.rbp.toBitVec
      ∗ Wd (rsp s - 40#64) s.regs.r12.toBitVec ∗ Wd (rsp s - 32#64) s.regs.r13.toBitVec
      ∗ Wd (rsp s - 24#64) s.regs.r14.toBitVec ∗ Wd (rsp s - 16#64) s.regs.r15.toBitVec
      ∗ View S g ∗ Wd (rsp s - 104#64) x0 ∗ Wd (rsp s - 96#64) x1
      ∗ Wd (rsp s - 88#64) x2 ∗ Wd (rsp s - 80#64) x3 ∗ Wd (rsp s - 72#64) x4
      ∗ Wd (rsp s - 64#64) x5 ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F =
      View S g ∗ Wd (rsp s - 104#64) x0 ∗ Wd (rsp s - 96#64) x1
      ∗ Wd (rsp s - 88#64) x2 ∗ Wd (rsp s - 80#64) x3 ∗ Wd (rsp s - 72#64) x4
      ∗ Wd (rsp s - 64#64) x5 ∗ Wd (rsp s - 56#64) s.regs.rbx.toBitVec
      ∗ Wd (rsp s - 48#64) s.regs.rbp.toBitVec ∗ Wd (rsp s - 40#64) s.regs.r12.toBitVec
      ∗ Wd (rsp s - 32#64) s.regs.r13.toBitVec ∗ Wd (rsp s - 24#64) s.regs.r14.toBitVec
      ∗ Wd (rsp s - 16#64) s.regs.r15.toBitVec ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F := by ecancel
  exact he ▸ h6

end

/-! ## The body state -/

-- A state between the pushes and the pops: `rbx` is the struct, `rbp` is the slot word `w`,
-- `r12` is the argument `T`, `r14` is `8 T`, and the low bytes of `r13` and `r15` are the kind
-- and the value opcode of `w`. The stack holds the return slot `y` of a callee and `Fr` with `k`.
structure Bd (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (w : Word) (y : Scratch) (k : Word)
    (t : MachineData) : Prop where
  mem : (View S g ∗ Stk (rsp s - 80#64) [y.a, y.b] y.ret ∗ Fr s ra y k F).get t.dmem
  sp : t.regs.rsp.toBitVec = rsp s - 80#64
  bx : t.regs.rbx.toBitVec = S
  bp : t.regs.rbp.toBitVec = w
  r12 : t.regs.r12.toBitVec = s.regs.rsi.toBitVec
  kind : t.regs.r15.toBitVec.extractLsb' 0 8 = w.extractLsb' 32 8
  r14 : t.regs.r14.toBitVec = s.regs.rsi.toBitVec * 8#64
  opcode : t.regs.r13.toBitVec.extractLsb' 0 8 = w.extractLsb' 40 8

-- `movzbl` and `movb`: the low byte of a byte that is zero-extended.
theorem byte_zext (b : BitVec 8) : (BitVec.setWidth 64 (BitVec.setWidth 32 b)).extractLsb' 0 8 = b := by
  bv_decide

-- `andq` with the mask of byte 5 and `orq` with byte 5: the slot word again.
theorem pack (w : Word) :
    18446463698244468735#64 &&& w ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.extractLsb' 0 8
      (BitVec.setWidth 64 (BitVec.setWidth 32 (w.extractLsb' 40 8)))))).shiftLeft 40 = w := by
  bv_decide

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {w k : Word} {y : Scratch}

-- The loads of the slot word `T` of the target, from the struct at `d`.
theorem tgt_loads {m : Mem 64} {R : MProp 64} (hm : (View S g ∗ R).get m) {d T : Word} (hd : d = S)
    (hT : T.toNat < g.h.n.toNat) :
    BitVec.ofInt 64 (m.loadInt d 8).get! = g.h.tgt
    ∧ BitVec.ofInt 64 (m.loadInt (slotAt g.h.tgt T.toNat) 8).get! = g.tgt[T.toNat]
    ∧ BitVec.ofInt 8 (m.loadInt (slotAt g.h.tgt T.toNat + 4#64) 1).get!
      = g.tgt[T.toNat].extractLsb' 32 8
    ∧ BitVec.ofInt 8 (m.loadInt (slotAt g.h.tgt T.toNat + 5#64) 1).get!
      = g.tgt[T.toNat].extractLsb' 40 8 := by
  rw [hd]
  have e0 : rd m (Fld.target S) = g.h.tgt := rd_of_eq hm (by unfold View Em; ecancel)
  exact ⟨e0, View.rd_tgt hm hT, View.rdb_tgt_byte hm hT (j := 4) (by decide),
    View.rdb_tgt_byte hm hT (j := 5) (by decide)⟩

theorem tgt_isSome {m : Mem 64} {R : MProp 64} (hm : (View S g ∗ R).get m) {d T : Word} (hd : d = S)
    (hT : T.toNat < g.h.n.toNat) :
    (m.loadInt d 8).isSome = true
    ∧ (m.loadInt (BitVec.ofInt 64 (m.loadInt d 8).get! + T * 8#64) 8).isSome = true
    ∧ (m.loadInt (BitVec.ofInt 64 (m.loadInt d 8).get! + T * 8#64 + 4#64) 1).isSome = true
    ∧ (m.loadInt (BitVec.ofInt 64 (m.loadInt d 8).get! + T * 8#64 + 5#64) 1).isSome = true := by
  rw [(tgt_loads hm hd hT).1, fold_slot]
  rw [hd]
  refine ⟨isSome_of_eq g.h.tgt hm (P := View S g) (a := Fld.target S) (by unfold View Em; ecancel),
    View.isSome_tgt hm hT, ?_, ?_⟩
  · obtain ⟨_, h⟩ := View.b8_tgt hm hT (j := 4) (by decide); exact B8.isSome h
  · obtain ⟨_, h⟩ := View.b8_tgt hm hT (j := 5) (by decide); exact B8.isSome h

-- The state at the call of `shallowestCopyPosition`, in the form of the asm (`r` is `rsp` after
-- the call of `produce`, `d` is `rdi`, `T` is `rsi`).
theorem Bd.entry {c : MachineData} {r d T k : Word} {y : Scratch}
    (hm : (View S g ∗ Stk (rsp s - 80#64) [y.a, y.b] y.ret ∗ Fr s ra y k F).get c.dmem)
    (hT : T.toNat < g.h.n.toNat) (hd : d = S) (hTs : T = s.regs.rsi.toBitVec) (hr : r = rsp s - 8#64)
    (hsp : c.regs.rsp.toBitVec = r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 24#64)
    (hbx : c.regs.rbx.toBitVec = d)
    (hbp : c.regs.rbp.toBitVec = 18446463698244468735#64 &&& BitVec.ofInt 64
        (c.dmem.loadInt (BitVec.ofInt 64 (c.dmem.loadInt d 8).get! + T * 8#64) 8).get!
      ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.extractLsb' 0 8 (BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.ofInt 8 (c.dmem.loadInt
          (BitVec.ofInt 64 (c.dmem.loadInt d 8).get! + T * 8#64 + 5#64) 1).get!)))))).shiftLeft 40)
    (h12 : c.regs.r12.toBitVec = T)
    (h13 : c.regs.r15.toBitVec = BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8
      (c.dmem.loadInt (BitVec.ofInt 64 (c.dmem.loadInt d 8).get! + T * 8#64 + 4#64) 1).get!)))
    (h14 : c.regs.r14.toBitVec = T * 8#64)
    (h15 : c.regs.r13.toBitVec = BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8
      (c.dmem.loadInt (BitVec.ofInt 64 (c.dmem.loadInt d 8).get! + T * 8#64 + 5#64) 1).get!)))
    (hw : g.tgt[T.toNat] = w) : Bd S g F s ra w y k c := by
  subst hw
  obtain ⟨e0, e1, e4, e5⟩ := tgt_loads hm hd hT
  rw [e0, fold_slot] at hbp h13 h15
  rw [e1, e5, pack] at hbp
  rw [e4] at h13
  rw [e5] at h15
  refine ⟨hm, by rw [hsp, hr]; bv_omega, hbx.trans hd, hbp, h12.trans hTs, ?_, by rw [h14, hTs], ?_⟩
  · rw [h13]; exact byte_zext _
  · rw [h15]; exact byte_zext _


theorem Bd.pre {A : G → MachineData → Prop} {c : MachineData} (h : Bd S g F s ra w y k c)
    (hdi : rdi c = S) (hok : g.Ok) (hA : A g c) : Sep.Pre S g (Fr s ra y k F) A 2 c :=
  ⟨hdi, hok, ⟨[y.a, y.b], y.ret, rfl,
    by simpa only [rsp, Reg64s.get64_rsp, h.sp] using h.mem⟩, hA⟩

theorem Bd.agree {c t : MachineData} {g' : G} {fr' : List Word} {v' : Word}
    (h : Bd S g F s ra w y k c) (hag : Sep.mod.Agree c t) (hl : fr'.length = 2)
    (hm : (View S g' ∗ Stk (rsp c) fr' v' ∗ Fr s ra y k F).get t.dmem) :
    ∃ y', Bd S g' F s ra w y' k t := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, fr' = [a, b] := by
    match fr', hl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  refine ⟨{y with a := a, b := b, ret := v'}, ?_⟩
  exact {
    mem := by simpa only [rsp, Reg64s.get64_rsp, h.sp, Fr] using hm
    sp := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp
    bx := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx]; exact h.bx
    bp := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]; exact h.bp
    r12 := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact h.r12
    kind := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15]; exact h.kind
    r14 := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]; exact h.r14
    opcode := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13]; exact h.opcode }

theorem Bd.call {A : G → MachineData → Prop} {Q : G → G → MachineData → MachineData → Prop}
    {c : MachineData} {K : MachineData → Prop} (h : Bd S g F s ra w y k c) (hdi : rdi c = S)
    (hok : g.Ok) (hA : A g c)
    (hK : Bd S g F s ra w y k c → ∀ t g' y', Bd S g' F s ra w y' k t → Q g g' c t → g'.Ok → K t) :
    ∃ S' g' F', Sep.Pre S' g' F' A 2 c
      ∧ ∀ t, Sep.Post S' F' 2 (fun g'' t => Q g' g'' c t) c t → Sep.mod.Agree c t → K t := by
  refine ⟨S, g, _, h.pre hdi hok hA, ?_⟩
  intro t ⟨g', fr', v', hQ, hok', hl, hm⟩ hag
  obtain ⟨y', hbd⟩ := h.agree hag hl hm
  exact hK h t g' y' hbd hQ hok'

theorem Bd.post {Q : G → MachineData → Prop} {c t : MachineData}
    (h : Bd S g F s ra w y k c)
    (hp : Sep.Post S (Fr s ra y k F) 2 Q c t) : Sep.Post S F 12 Q s t := by
  obtain ⟨g', fr', v', hQ, hok', hl, hm⟩ := hp
  obtain ⟨a, b, rfl⟩ : ∃ a b, fr' = [a, b] := by
    match fr', hl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  refine ⟨g', saved s {y with a := a, b := b, ret := v'} k, ra.toBitVec, hQ, hok', rfl, ?_⟩
  rw [← frame_eq]
  simpa only [rsp, Reg64s.get64_rsp, h.sp, Fr] using hm

theorem Bd.callX [Host] {A : G → MachineData → Prop}
    {Q X : G → G → MachineData → MachineData → Prop}
    {c : MachineData} {K : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (h : Bd S g F s ra w y k c) (hdi : rdi c = S) (hok : g.Ok) (hA : A g c)
    (hK : Bd S g F s ra w y k c → ∀ t g' y', Bd S g' F s ra w y' k t → Q g g' c t → g'.Ok → K t)
    (hX : ∀ t, Sep.Post S F 12 (fun g' t => X g g' c t) s t →
      t.regs.get64 .rdi = 1#64 → E (label "exit") t) :
    ∃ S' g' F', Sep.Pre S' g' F' A 2 c
      ∧ (∀ t, Sep.Post S' F' 2 (fun g'' t => Q g' g'' c t) c t → Sep.mod.Agree c t → K t)
      ∧ (∀ t, Sep.Post S' F' 2 (fun g'' t => X g' g'' c t) c t →
        t.regs.get64 .rdi = 1#64 → E (label "exit") t) := by
  refine ⟨S, g, _, h.pre hdi hok hA, ?_, ?_⟩
  · intro t hp hag
    obtain ⟨g', fr', v', hQ, hok', hl, hm⟩ := hp
    obtain ⟨y', hbd⟩ := h.agree hag hl hm
    exact hK h t g' y' hbd hQ hok'
  · intro t hp harg
    exact hX t (h.post hp) harg

-- A step that keeps the stack registers: the struct is now `g'` and `(%rsp)` holds `k'`.
theorem Bd.step {t P : MachineData} {g' : G} {k' : Word} (h : Bd S g F s ra w y k t)
    (hm : (View S g' ∗ Stk (rsp s - 80#64) [y.a, y.b] y.ret ∗ Fr s ra y k' F).get P.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) (hbx : P.regs.rbx = t.regs.rbx)
    (hbp : P.regs.rbp = t.regs.rbp) (h12 : P.regs.r12 = t.regs.r12)
    (h13 : P.regs.r13 = t.regs.r13) (h14 : P.regs.r14 = t.regs.r14)
    (h15 : P.regs.r15 = t.regs.r15) : Bd S g' F s ra w y k' P :=
  ⟨hm, by rw [hsp]; exact h.sp, by rw [hbx]; exact h.bx, by rw [hbp]; exact h.bp,
    by rw [h12]; exact h.r12, by rw [h15]; exact h.kind, by rw [h14]; exact h.r14,
    by rw [h13]; exact h.opcode⟩

-- A step that keeps the memory and the stack registers.
theorem Bd.next {t P : MachineData} (h : Bd S g F s ra w y k t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) (hbx : P.regs.rbx = t.regs.rbx)
    (hbp : P.regs.rbp = t.regs.rbp) (h12 : P.regs.r12 = t.regs.r12)
    (h13 : P.regs.r13 = t.regs.r13) (h14 : P.regs.r14 = t.regs.r14)
    (h15 : P.regs.r15 = t.regs.r15) : Bd S g F s ra w y k P :=
  h.step (hm ▸ h.mem) hsp hbx hbp h12 h13 h14 h15

theorem Bd.stack {t : MachineData} (h : Bd S g F s ra w y k t) : t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    rw [Reg64s.get64_rsp, Reg64s.get64_rsp, h.sp]
    simp only [MachineData.pushRa, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp]
    bv_omega)

-- `(%rsp)`: the word `k`.
theorem Bd.rd_k {t : MachineData} (h : Bd S g F s ra w y k t) :
    BitVec.ofInt 64 (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).get! = k := by
  rw [h.sp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega]; exact rd_of_eq h.mem (by unfold Fr; ecancel)

theorem Bd.isSome_k {t : MachineData} (h : Bd S g F s ra w y k t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome = true := by
  rw [h.sp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega]; exact isSome_of_eq k h.mem (by unfold Fr; ecancel)

-- `movq %rax, (%rsp)`: the memory with `k'` at `(%rsp)`.
theorem Bd.mem_k {t : MachineData} (h : Bd S g F s ra w y k t) (k' : Word) :
    (View S g ∗ Stk (rsp s - 80#64) [y.a, y.b] y.ret ∗ Fr s ra y k' F).get
      (t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8 k'.toInt) := by
  rw [h.sp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega]
  exact store_all h.mem (by unfold Fr; ecancel) k' (by unfold Fr; ecancel)

theorem Bd.isSome_exit {t : MachineData} (h : Bd S g F s ra w y k t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec - 8#64) 8).isSome = true := by
  rw [h.sp, show rsp s - 80#64 - 8#64 = rsp s - 88#64 by bv_omega]
  exact isSome_of_eq y.ret h.mem (by rw [stk2]; ecancel)

theorem Bd.mem_exit {t : MachineData} (h : Bd S g F s ra w y k t) (exitra : Int64) :
    (View S g ∗ Stk (rsp s) (saved s {y with ret := exitra.toBitVec} k) ra.toBitVec ∗ F).get
      (t.dmem.storeInt (t.regs.rsp.toBitVec - 8#64) 8 exitra.toBitVec.toInt) := by
  rw [← frame_eq, h.sp, show rsp s - 80#64 - 8#64 = rsp s - 88#64 by bv_omega]
  exact store_all h.mem (by rw [stk2]; ecancel) exitra.toBitVec
    (by rw [stk2]; unfold Fr; ecancel)

end

/-! ## The stack words of the body -/

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {w k : Word} {y : Scratch}

-- `movq (%rsp), …` after `movq x, (%rsp)`.
theorem Bd.rd_st {t : MachineData} (h : Bd S g F s ra w y k t) (x : Word) :
    BitVec.ofInt 64 ((t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8 x.toInt).loadInt (t.regs.rsp.toBitVec + 8#64) 8).get!
      = x := by
  have hm := h.mem_k x
  rw [h.sp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega] at hm ⊢
  exact rd_of_eq hm (by unfold Fr; ecancel)

theorem Bd.isSome_st {t : MachineData} (h : Bd S g F s ra w y k t) (x : Word) :
    ((t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8 x.toInt).loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome = true := by
  have hm := h.mem_k x
  rw [h.sp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega] at hm ⊢
  exact isSome_of_eq x hm (by unfold Fr; ecancel)

-- `movq x, (%rsp)` with `x = k'`.
theorem Bd.store_k {t P : MachineData} {x k' : Word} (h : Bd S g F s ra w y k t) (hx : x = k')
    (hm : P.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8 x.toInt)
    (hsp : P.regs.rsp = t.regs.rsp) (hbx : P.regs.rbx = t.regs.rbx)
    (hbp : P.regs.rbp = t.regs.rbp) (h12 : P.regs.r12 = t.regs.r12)
    (h13 : P.regs.r13 = t.regs.r13) (h14 : P.regs.r14 = t.regs.r14)
    (h15 : P.regs.r15 = t.regs.r15) : Bd S g F s ra w y k' P := by
  subst hx
  exact h.step (hm ▸ h.mem_k x) hsp hbx hbp h12 h13 h14 h15

-- The 6 `popq` read the words of `Fr` above `(%rsp)`.
theorem Bd.isSome_pops {t : MachineData} (h : Bd S g F s ra w y k t) :
    (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec) 8).isSome = true
    ∧ (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8).isSome
      = true := by
  have hm := h.mem
  rw [h.sp, show 24#64 + (rsp s - 80#64) = rsp s - 56#64 by bv_omega,
    show rsp s - 56#64 + 8#64 = rsp s - 48#64 by bv_omega,
    show rsp s - 48#64 + 8#64 = rsp s - 40#64 by bv_omega,
    show rsp s - 40#64 + 8#64 = rsp s - 32#64 by bv_omega,
    show rsp s - 32#64 + 8#64 = rsp s - 24#64 by bv_omega,
    show rsp s - 24#64 + 8#64 = rsp s - 16#64 by bv_omega]
  exact ⟨isSome_of_eq _ hm (by unfold Fr; ecancel), isSome_of_eq _ hm (by unfold Fr; ecancel),
    isSome_of_eq _ hm (by unfold Fr; ecancel), isSome_of_eq _ hm (by unfold Fr; ecancel),
    isSome_of_eq _ hm (by unfold Fr; ecancel), isSome_of_eq _ hm (by unfold Fr; ecancel)⟩

-- `addq $8, %rsp` and the 6 `popq`: the state `P` before the `ret` is a `Kp` state.
theorem Bd.pop {t P : MachineData} (h : Bd S g F s ra w y k t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp.toBitVec
      = 24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
    (hbx : P.regs.rbx.toBitVec = rd t.dmem (24#64 + t.regs.rsp.toBitVec))
    (hbp : P.regs.rbp.toBitVec = rd t.dmem (24#64 + t.regs.rsp.toBitVec + 8#64))
    (h12 : P.regs.r12.toBitVec = rd t.dmem (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64))
    (h13 : P.regs.r13.toBitVec = rd t.dmem (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64))
    (h14 : P.regs.r14.toBitVec
      = rd t.dmem (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64))
    (h15 : P.regs.r15.toBitVec
      = rd t.dmem (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)) :
    Kp S g F s ra (saved s y k) P := by
  have hmem := h.mem
  have a1 : 24#64 + (rsp s - 80#64) = rsp s - 56#64 := by bv_omega
  have a2 : rsp s - 56#64 + 8#64 = rsp s - 48#64 := by bv_omega
  have a3 : rsp s - 48#64 + 8#64 = rsp s - 40#64 := by bv_omega
  have a4 : rsp s - 40#64 + 8#64 = rsp s - 32#64 := by bv_omega
  have a5 : rsp s - 32#64 + 8#64 = rsp s - 24#64 := by bv_omega
  have a6 : rsp s - 24#64 + 8#64 = rsp s - 16#64 := by bv_omega
  have a7 : rsp s - 16#64 + 8#64 = rsp s - 8#64 := by bv_omega
  simp only [h.sp, a1, a2, a3, a4, a5, a6, a7] at hsp hbx hbp h12 h13 h14 h15
  refine ⟨by rw [hm, ← frame_eq]; exact hmem, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply UInt64.toBitVec_inj.mp
    rw [hsp]
    show _ = rsp s - 8#64
    rfl
  · apply UInt64.toBitVec_inj.mp; rw [hbx]; exact rd_of_eq hmem (by unfold Fr; ecancel)
  · apply UInt64.toBitVec_inj.mp; rw [hbp]; exact rd_of_eq hmem (by unfold Fr; ecancel)
  · apply UInt64.toBitVec_inj.mp; rw [h12]; exact rd_of_eq hmem (by unfold Fr; ecancel)
  · apply UInt64.toBitVec_inj.mp; rw [h13]; exact rd_of_eq hmem (by unfold Fr; ecancel)
  · apply UInt64.toBitVec_inj.mp; rw [h14]; exact rd_of_eq hmem (by unfold Fr; ecancel)
  · apply UInt64.toBitVec_inj.mp; rw [h15]; exact rd_of_eq hmem (by unfold Fr; ecancel)

end

theorem split12 {fr : List Word} (h : fr.length = 12) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11,
      fr = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] :=
  match fr, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11], _ =>
    ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, rfl⟩

/-! ## The flat model of `produce` -/

-- The last two cases of the action: a free slot or a spilled slot, then a block.
def tail (st : Flat.St) (x : StackSlot) (cp t : Word) : Flat.Status × Flat.St :=
  if canBeFreelyGenerated x || Flat.isSpilled st x then Flat.push st x t
  else if cp ≠ Flat.NONE then Flat.blockDupUnreachable st cp
  else (.assertionFailed, st)

-- The action of `produce` for the slot `x` with the copy position `cp`.
def act (st : Flat.St) (x : StackSlot) (cp t : Word) : Flat.Status × Flat.St :=
  if isJunk x then Flat.push st x t
  else if cp ≠ Flat.NONE ∧ Flat.isDupReachable st cp then Flat.dup st cp t
  else tail st x cp t

-- The check after the action.
def fin (r : Flat.Status × Flat.St) (t : Word) : Flat.Status × Flat.St :=
  if r.1 ≠ .done then r
  else if Flat.get r.2.pos t ≠ r.2.size - 1 then (.assertionFailed, r.2)
  else (.done, { r.2 with pend := r.2.pend - 1 })

theorem produce_eq (st : Flat.St) (t : Word) :
    Flat.produce st t = fin (act st (Flat.get st.target t)
      (Flat.shallowestCopyPosition st (Flat.get st.target t)) t) t := rfl

section
variable {st : Flat.St} {x : StackSlot} {cp t : Word}

theorem act_junk (h : isJunk x = true) : act st x cp t = Flat.push st x t := by
  simp [act, h]

theorem act_dup (hj : isJunk x = false) (hc : cp ≠ Flat.NONE)
    (hr : Flat.isDupReachable st cp = true) : act st x cp t = Flat.dup st cp t := by
  simp [act, hj, hc, hr]

theorem act_tail (hj : isJunk x = false) (h : cp = Flat.NONE ∨ Flat.isDupReachable st cp = false) :
    act st x cp t = tail st x cp t := by
  rcases h with h | h <;> simp [act, hj, h]

theorem tail_push (h : (canBeFreelyGenerated x || Flat.isSpilled st x) = true) :
    tail st x cp t = Flat.push st x t := by
  unfold tail; rw [ite_eq_left h]

theorem tail_none (h : (canBeFreelyGenerated x || Flat.isSpilled st x) = false)
    (hc : cp = Flat.NONE) : tail st x cp t = (.assertionFailed, st) := by
  unfold tail; rw [ite_eq_right (by rw [h]; decide), ite_eq_right (fun e => e hc)]

theorem tail_block (h : (canBeFreelyGenerated x || Flat.isSpilled st x) = false)
    (hc : cp ≠ Flat.NONE) : tail st x cp t = Flat.blockDupUnreachable st cp := by
  unfold tail; rw [ite_eq_right (by rw [h]; decide), ite_eq_left hc]

theorem block_zero {p e : Word} (h : e = 0) : Flat.block st p e = (.assertionFailed, st) := by
  unfold Flat.block; rw [ite_eq_left h]

theorem block_ne {p e : Word} (h : e ≠ 0) :
    Flat.block st p e = (.blocked, { st with blockedOffset := p, blockedExcess := e }) := by
  unfold Flat.block; rw [ite_eq_right h]

theorem fin_ne {r : Flat.Status × Flat.St} (h : r.1 ≠ .done) : fin r t = r := by
  unfold fin; rw [ite_eq_left h]

theorem fin_bad {r : Flat.Status × Flat.St} (h : r.1 = .done) (hp : Flat.get r.2.pos t ≠ r.2.size - 1) :
    fin r t = (.assertionFailed, r.2) := by
  unfold fin; rw [ite_eq_right (fun e => e h), ite_eq_left hp]

theorem fin_ok {r : Flat.Status × Flat.St} (h : r.1 = .done) (hp : Flat.get r.2.pos t = r.2.size - 1) :
    fin r t = (.done, { r.2 with pend := r.2.pend - 1 }) := by
  unfold fin; rw [ite_eq_right (fun e => e h), ite_eq_right (fun e => e hp)]

end

-- The copy below `pos` is none or below `pos`.
theorem copyBelow_lt (st : Flat.St) (x : StackSlot) (n : Nat) :
    ∀ pos : Word, pos.toNat = n →
      Flat.copyBelow st x pos = Flat.NONE ∨ (Flat.copyBelow st x pos).toNat < pos.toNat := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro pos hn
    generalize hc : Flat.copyBelow st x pos = c
    rw [Flat.copyBelow] at hc
    split at hc
    · exact Or.inl hc.symm
    · split at hc
      · subst hc; right; bv_omega
      · rcases ih (pos - 1).toNat (by bv_omega) (pos - 1) rfl with h | h
        · exact Or.inl (hc ▸ h)
        · right; rw [← hc]; bv_omega

-- A copy position that is not none is a slot of the stack.
theorem copy_lt {g : G} {x : StackSlot} {cp : Word}
    (h : Flat.shallowestCopyPosition (flat g) x = cp) (hc : cp ≠ Flat.NONE) :
    cp.toNat < g.h.len.toNat := by
  rcases copyBelow_lt (flat g) x _ (flat g).size rfl with e | e
  · exact absurd (h ▸ e) hc
  · exact h ▸ e

theorem get_target {g : G} (hok : g.Ok) {i : Word} (hi : i.toNat < g.h.n.toNat) :
    Flat.get (flat g).target i = StackSlot.ofWord g.tgt[i.toNat] := by
  simp [Flat.get, flat, vec, Nat.lt_of_lt_of_le hi hok.n, hi]

-- The slot `w` of the target: its variable id is in the target.
theorem spill_mem {g : G} {i : Nat} (hi : i < g.h.n.toNat) {w : Word} (hw : g.tgt[i] = w) :
    ∀ j, spillId (StackSlot.ofWord w) = some j → j ∈ splIds g.tgt.toList := by
  intro j h
  exact List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨w, by rw [← hw]; simp, h⟩)

/-! ## The posts of the callees, with the argument registers of the call -/

section
variable {g g' : G} {c t : MachineData}

theorem copyQ_of {x : Word} (h : shallowestCopyQ g g' c t) (hx : rsi c = x) :
    g' = g ∧ rax t = Flat.shallowestCopyPosition (flat g) (StackSlot.ofWord x) := by
  rw [← hx]; exact h

theorem spillQ_of {x : Word} (h : isSpilledQ g g' c t) (hx : rsi c = x) :
    g' = g ∧ al t = if Flat.isSpilled (flat g) (StackSlot.ofWord x) then 1#8 else 0#8 := by
  rw [← hx]; exact h

theorem pushQ_of {x d : Word} (h : pushQ g g' c t) (hx : rsi c = x) (hd : rdx c = d) :
    Res (Flat.push · (StackSlot.ofWord x) d) g g' t := by
  rw [← hx, ← hd]; exact h.1

theorem dupQ_of {x d : Word} (h : dupQ g g' c t) (hx : rsi c = x) (hd : rdx c = d) :
    Res (Flat.dup · x d) g g' t := by
  rw [← hx, ← hd]; exact h.1

end

/-! ## `Keep`, `Ok` and the ghost with other words of the struct -/

theorem Keep.refl (g : G) : Keep g g := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {g g1 g2 : G} (h1 : Keep g g1) (h2 : Keep g1 g2) : Keep g g2 :=
  ⟨h2.tgtp.trans h1.tgtp, h2.n.trans h1.n, h2.splp.trans h1.splp, h2.data.trans h1.data,
    h2.ops.trans h1.ops, h2.xs.trans h1.xs, h2.xo.trans h1.xo, h2.tgt.trans h1.tgt,
    h2.spl.trans h1.spl⟩

def withPend (g : G) (v : Word) : G := { g with h := { g.h with pend := v } }
def withOff (g : G) (v : Word) : G := { g with h := { g.h with blkOff := v } }
def withExc (g : G) (v : Word) : G := { g with h := { g.h with blkExc := v } }

section
variable {g : G}

theorem flat_withPend (v : Word) : flat (withPend g v) = { flat g with pend := v } := rfl
theorem flat_withBlk (p e : Word) :
    flat (withExc (withOff g p) e) = { flat g with blockedOffset := p, blockedExcess := e } := rfl

theorem Ok.withPend (h : g.Ok) (v : Word) : (withPend g v).Ok := ⟨h.len, h.n, h.xs, h.xo, h.nops, h.spl⟩
theorem Ok.withBlk (h : g.Ok) (p e : Word) : (withExc (withOff g p) e).Ok :=
  ⟨h.len, h.n, h.xs, h.xo, h.nops, h.spl⟩

theorem Keep.withPend (v : Word) : Keep g (withPend g v) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem Keep.withBlk (p e : Word) : Keep g (withExc (withOff g p) e) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

/-! ## Loads and stores of the struct at `rbx` -/

section
variable {S : Addr} {g : G} {R : MProp 64} {m : Mem 64}

theorem rd_len' (h : (View S g ∗ R).get m) :
    BitVec.ofInt 64 (m.loadInt (S + 32#64) 8).get! = g.h.len := by
  rw [Fld.fold_stack_size]; exact View.rd_len h
theorem isSome_len' (h : (View S g ∗ R).get m) : (m.loadInt (S + 32#64) 8).isSome = true := by
  rw [Fld.fold_stack_size]; exact View.isSome_len h

theorem rd_pos' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < maxStackSize) :
    BitVec.ofInt 64 (m.loadInt (S + x * 8#64 + 8248#64) 8).get! = g.h.pos[x.toNat] := by
  rw [Fld.fold_mapping_positionOf]; exact View.rd_pos h hx
theorem isSome_pos' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < maxStackSize) :
    (m.loadInt (S + x * 8#64 + 8248#64) 8).isSome = true := by
  rw [Fld.fold_mapping_positionOf]; exact View.isSome_pos h hx

theorem rd_pend' (h : (View S g ∗ R).get m) :
    BitVec.ofInt 64 (m.loadInt (S + 16440#64) 8).get! = g.h.pend := by
  rw [Fld.fold_pendingGenerations]; exact rd_of_eq h (by unfold View Em; ecancel)
theorem isSome_pend' (h : (View S g ∗ R).get m) : (m.loadInt (S + 16440#64) 8).isSome = true := by
  rw [Fld.fold_pendingGenerations]; exact isSome_of_eq g.h.pend h (by unfold View Em; ecancel)
theorem store_pend' (h : (View S g ∗ R).get m) (v : Word) :
    (View S (withPend g v) ∗ R).get (m.storeInt (S + 16440#64) 8 v.toInt) := by
  rw [Fld.fold_pendingGenerations]
  exact swap_of_eq h (A := Wd (Fld.pendingGenerations S) g.h.pend) (by unfold View Em; ecancel)
    (by unfold View withPend Em; ecancel) (Wd.store · v)

theorem isSome_off' (h : (View S g ∗ R).get m) : (m.loadInt (S + 16448#64) 8).isSome = true := by
  rw [Fld.fold_blocked_offset]; exact isSome_of_eq g.h.blkOff h (by unfold View Em; ecancel)
theorem store_off' (h : (View S g ∗ R).get m) (v : Word) :
    (View S (withOff g v) ∗ R).get (m.storeInt (S + 16448#64) 8 v.toInt) := by
  rw [Fld.fold_blocked_offset]
  exact swap_of_eq h (A := Wd (Fld.blocked_offset S) g.h.blkOff) (by unfold View Em; ecancel)
    (by unfold View withOff Em; ecancel) (Wd.store · v)

theorem isSome_exc' (h : (View S g ∗ R).get m) : (m.loadInt (S + 16456#64) 8).isSome = true := by
  rw [Fld.fold_blocked_excess]; exact isSome_of_eq g.h.blkExc h (by unfold View Em; ecancel)
theorem store_exc' (h : (View S g ∗ R).get m) (v : Word) :
    (View S (withExc g v) ∗ R).get (m.storeInt (S + 16456#64) 8 v.toInt) := by
  rw [Fld.fold_blocked_excess]
  exact swap_of_eq h (A := Wd (Fld.blocked_excess S) g.h.blkExc) (by unfold View Em; ecancel)
    (by unfold View withExc Em; ecancel) (Wd.store · v)

end

/-! ## Flags -/

-- `al` reads only `rax`. A step that does not write `rax` keeps `al`.
theorem al_eq {t t' : MachineData} (h : t'.regs.rax = t.regs.rax) : al t' = al t := by
  rw [al, al, rax, rax, Reg64s.get64_rax, Reg64s.get64_rax, h]

-- `testb %al, %al; jne`: the jump is not taken.
theorem al_zero {t : MachineData}
    (h : (!(BitVec.extractLsb' 0 8 t.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8 t.regs.rax.toBitVec
      == BitVec.zero 8)) = false) : al t = 0#8 := by
  simp only [Bool.not_eq_false', beq_iff_eq, BitVec.and_self] at h
  rw [al, rax, Reg64s.get64_rax, BitVec.setWidth_eq_extractLsb' (by decide)]
  exact h

-- `testb %al, %al; jne`: the jump is taken.
theorem al_ne {t : MachineData}
    (h : (!(BitVec.extractLsb' 0 8 t.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8 t.regs.rax.toBitVec
      == BitVec.zero 8)) = true) : al t ≠ 0#8 := by
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, BitVec.and_self] at h
  rw [al, rax, Reg64s.get64_rax, BitVec.setWidth_eq_extractLsb' (by decide)]
  exact h

theorem code_eq_zero {st : Flat.Status} (h : code st = 0#8) : st = .done := by
  cases st <;> revert h <;> decide

theorem code_ne_zero {st : Flat.Status} (h : code st ≠ 0#8) : st ≠ .done := by
  intro e; subst e; exact h rfl

-- `cmpq b, a; je`.
theorem eq_of_z {a b : Word} (h : (a - b == BitVec.zero 64) = true) : a = b := by
  simp only [beq_iff_eq] at h
  have : a - b = 0#64 := h
  bv_omega

theorem ne_of_z {a b : Word} (h : (a - b == BitVec.zero 64) = false) : a ≠ b := by
  intro e
  simp [e] at h

-- `cmpq b, a; jne`.
theorem eq_of_nz {a b : Word} (h : (!(a - b == BitVec.zero 64)) = false) : a = b :=
  eq_of_z (by simpa using h)

theorem ne_of_nz {a b : Word} (h : (!(a - b == BitVec.zero 64)) = true) : a ≠ b :=
  ne_of_z (by simpa using h)

-- `cmpb b, a; je`: the bytes `a` and `b`.
theorem sub_beq8 (a b : BitVec 8) : (a - b == BitVec.zero 8) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, show BitVec.zero 8 = 0#8 from rfl]
  constructor <;> intro h <;> bv_omega

-- `testb b, b; jne`: the byte `b`.
theorem test_beq8 (b : BitVec 8) : (!(b &&& b == BitVec.zero 8)) = (b != 0#8) := by
  rw [BitVec.and_self]; rfl

-- `cmpq $15, d; jbe`: the jump is taken.
theorem le_of_be {d : Word}
    (h : (((((d - 15#64).toNat : Int) != (d.toNat : Int) - 15)) || (d - 15#64 == BitVec.zero 64)) = true) :
    d ≤ 15#64 := by
  rw [Idioms.cf_sub_imm d 15 (by decide)] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h | h
  · bv_omega
  · have : d - 15#64 = 0#64 := h
    bv_omega

-- `cmpq $15, d; jbe`: the jump is not taken.
theorem not_le_of_be {d : Word}
    (h : (((((d - 15#64).toNat : Int) != (d.toNat : Int) - 15)) || (d - 15#64 == BitVec.zero 64)) = false) :
    ¬d ≤ 15#64 := by
  rw [Idioms.cf_sub_imm d 15 (by decide)] at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at h
  have : d - 15#64 ≠ 0#64 := h.2
  bv_omega

-- `notq; addq len; cmpq $15; jbe`: `len + ~cp` is the depth of `cp`.
theorem reach_iff (st : Flat.St) (cp : Word) :
    Flat.isDupReachable st cp = true ↔ st.size + ~~~cp ≤ 15#64 := by
  have e : st.size + ~~~cp = st.size - 1#64 - cp := by bv_decide
  rw [e]
  unfold Flat.isDupReachable Flat.depthOf Flat.maxDupDepth
  constructor
  · intro h; have := of_decide_eq_true h; bv_omega
  · intro h; exact decide_eq_true (by bv_omega)

theorem add_neg_one (x : Word) : x + BitVec.ofInt 64 (-1) = x - 1#64 := by
  rw [show BitVec.ofInt 64 (-1) = -1#64 from rfl]
  bv_omega

-- `movq $-16, %rdx; subq cp, %rdx; addq len, %rdx`: the excess of `blockDupUnreachable`.
theorem exc_eq (g : G) (cp : Word) :
    g.h.len + (18446744073709551600#64 - cp) = Flat.depthOf (flat g) cp - Flat.maxDupDepth := by
  unfold Flat.depthOf Flat.maxDupDepth
  show _ = g.h.len - 1 - cp - 15#64
  bv_omega

-- The byte `al` of a callee that returns the bool `b`.
theorem bit_true {t : MachineData} {b : Bool} (h : al t = if b then 1#8 else 0#8)
    (hz : al t ≠ 0#8) : b = true := by
  cases b
  · exact absurd h hz
  · rfl

theorem bit_false {t : MachineData} {b : Bool} (h : al t = if b then 1#8 else 0#8)
    (hz : al t = 0#8) : b = false := by
  cases b
  · rfl
  · rw [hz] at h; exact absurd h (by decide)

/-! ## The flags of the slot word -/

-- `cmpb $1, %r13b`: the kind byte is `Junk`.
theorem junk_iff (w : Word) : isJunk (StackSlot.ofWord w) = (w.extractLsb' 32 8 == 1#8) := rfl

-- `cmpb $2, %r13b; je`: a return label is free.
theorem free_of_label {w : Word} (h : w.extractLsb' 32 8 = 2#8) :
    canBeFreelyGenerated (StackSlot.ofWord w) = true := by
  simp [canBeFreelyGenerated, StackSlot.ofWord, h, FunctionCallReturnLabel]

-- `testb %r15b, %r15b; jne`, not taken: a literal is free.
theorem free_of_const {w : Word} (h : w.extractLsb' 40 8 = 0#8) :
    canBeFreelyGenerated (StackSlot.ofWord w) = true := by
  simp [canBeFreelyGenerated, isLiteralValue, StackSlot.ofWord, h, Const]

-- `testb %r15b, %r15b; jne`, taken: no other case makes the slot free.
theorem not_free {w : Word} (hj : isJunk (StackSlot.ofWord w) = false)
    (hl : w.extractLsb' 32 8 ≠ 2#8) (hc : w.extractLsb' 40 8 ≠ 0#8) :
    canBeFreelyGenerated (StackSlot.ofWord w) = false := by
  rw [junk_iff] at hj
  simp only [canBeFreelyGenerated, isLiteralValue, StackSlot.ofWord, Const, Junk,
    FunctionCallReturnLabel] at *
  simp [hj, hl, hc]


/-! ## The post -/

-- `produceQ` from the model result `r` of `fin`.
theorem prodQ {g g1 : G} {s t : MachineData} {r : Flat.Status × Flat.St} (hK : Keep g g1)
    (hP : Flat.produce (flat g) s.regs.rsi.toBitVec = r) (hf : flat g1 = r.2) (ha : al t = code r.1)
    (normalStatus : code r.1 ≠ ASSERTION_FAILED) :
    produceQ g g1 s t := by
  simp only [produceQ, NormalResult, Res, rsi, Reg64s.get64_rsi, hP]
  exact ⟨⟨hK, hf, ha⟩, fun failed => normalStatus (ha.symm.trans failed)⟩

theorem prodX_of {g g1 : G} {s t : MachineData} {f : Flat.St → Flat.Status × Flat.St}
    (hP : Flat.produce (flat g) (rsi s) = fin (f (flat g)) (rsi s))
    (hX : ExitRes f g g1) : produceX g g1 s t := by
  have hn : (f (flat g)).1 ≠ .done := by rw [hX.2.2]; decide
  dsimp only [produceX, ExitRes]
  rw [hP, fin_ne hn]
  exact hX

-- `Flat.get` in the bound is the vector index.
theorem get_eq {α : Type} [Inhabited α] (v : Vector α maxStackSize) {i : Word}
    (hi : i.toNat < maxStackSize) : Flat.get v i = v[i.toNat] := by
  simp [Flat.get, hi]

/-! ## `notq` -/

section
open Std.WP Lean.Order
open scoped Program.WP
set_option experimental.vcgen true

-- `notq r`: Kraken has no spec for it. It does not change the flags.
theorem not_reg_spec [Host] [FunDecls] (asz : Width) (r : Reg64)
    {Q : PUnit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (~~~(s.regs.get64 r)) } ⦄
      (Directive.instr (.regular asz .W64 (.not (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact hn _ hpre

end

end FlatShuffler.Unit.ProduceProof
