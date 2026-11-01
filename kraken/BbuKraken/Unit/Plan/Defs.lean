module

public import BbuKraken.Unit.SpillDefs
import all BbuKraken.Unit.SpillDefs
public import BbuKraken.FlatPlan
import all BbuKraken.FlatPlan
public import BbuKraken.Sep.Stores
import all BbuKraken.Sep.Stores
public import BbuKraken.Unit.IsSpilled
import all BbuKraken.Unit.IsSpilled

@[expose] public section

/-!
# The contracts of the planner units

The units of `MappingBuilder` and `Planner` (`c/bbu/*.S`) do not use `Emission`, so their
contracts do not use `Sep.View`. A contract here has a view `V S a`: the memory of the object
at `S` (`rdi`) for a ghost `a : α`, with an invariant `ok a`. `VPre`, `VPost`, `VThm` and `VSpec`
are `Sep.Pre`, `Sep.Post`, `UnitThm` and `Sep.Spec` with `V` in place of `Sep.View`. The body
state is `Kg (V S a ∗ F)`.

- `MapM a M`: the two arrays of a `Mapping` at `a` (`m_destinationOf`, then `m_positionOf` at
  `a + 8192`), `MAX_N` words each.
- `BView B b`: a `MappingBuilder` at `B`. The words and bytes of the members, the `m` source
  words, the `n` target words, the `m` dropped bytes and the `Mapping`. The padding of the struct
  is not in the view. `BG.fl b` is the flat `Flat.Builder`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit

open Bbu.Sep

/-! ## Contracts with a view -/

-- `d` free words below `rsp s`, the return slot and `P`.
def StkMem (d : Nat) (P : MProp 64) (s : MachineData) (m : Mem 64) : Prop :=
  ∃ fr v, fr.length = d ∧ (Stk (rsp s) fr v ∗ P).get m

section
variable {α : Type} (V : Addr → α → MProp 64) (ok : α → Prop)

structure VPre (S : Addr) (a : α) (F : MProp 64) (A : α → MachineData → Prop) (d : Nat)
    (s : MachineData) : Prop where
  rdi : rdi s = S
  ok : ok a
  args : A a s
  mem : StkMem d (V S a ∗ F) s s.dmem

def VPost (S : Addr) (F : MProp 64) (d : Nat) (Q : α → MachineData → Prop)
    (s t : MachineData) : Prop :=
  ∃ a', Q a' t ∧ ok a' ∧ StkMem d (V S a' ∗ F) s t.dmem

abbrev VThm [Host] [FunDecls] (prog : Program) (A : α → MachineData → Prop) (d : Nat)
    (Q : α → α → MachineData → MachineData → Prop) : Prop :=
  ∀ S a F, Sep.Body prog (VPre V ok S a F A d)
    (fun s t => VPost V ok S F d (fun a' t => Q a a' s t) s t)

abbrev VSpec [Host] [FunDecls] (f : Label) (A : α → MachineData → Prop) (d : Nat)
    (Q : α → α → MachineData → MachineData → Prop) : Prop :=
  ∀ asz osz (K : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => ∃ S a F, VPre V ok S a F A d s
        ∧ ∀ s', VPost V ok S F d (fun a' t => Q a a' s t) s s' → Sep.mod.Agree s s' → K () s' ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ K; E ⦄
end

section
variable {α : Type} {V : Addr → α → MProp 64} {ok : α → Prop}

theorem StkMem.isSome {d : Nat} {P : MProp 64} {s : MachineData} (h : StkMem d P s s.dmem) :
    (s.dmem.loadInt (s.regs.get64 .rsp - 8#64) 8).isSome = true := by
  obtain ⟨fr, v, -, hm⟩ := h
  obtain ⟨R, e⟩ : ∃ R, Stk (rsp s) fr v ∗ P = Wd (rsp s - 8#64) v ∗ R :=
    ⟨_, by unfold Stk; ecancel⟩
  exact Wd.isSome (e ▸ hm)

theorem vspec_of_body [Host] [FunDecls] {f : Label} {g₀ : Fragment}
    (hg : FunDecls.at (label f) = some g₀) {A : α → MachineData → Prop} {d : Nat}
    {Q : α → α → MachineData → MachineData → Prop} (hb : VThm V ok g₀.prog A d Q) :
    VSpec V ok f A d Q := by
  intro asz osz K E
  refine ⟨fun s ⟨S, a, F, hp, hk⟩ => ?_⟩
  exact (Program.WP.callSpec_of_triple hg (hb S a F) asz osz K E).1 s ⟨hp.mem.isSome, hp, hk⟩

-- The body state at the entry.
theorem VPre.kg {S : Addr} {a : α} {F : MProp 64} {A : α → MachineData → Prop} {d : Nat}
    {s : MachineData} (h : VPre V ok S a F A d s) (ra : Int64) :
    ∃ fr, fr.length = d ∧ Kg (V S a ∗ F) s ra fr (s.pushRa ra) :=
  let ⟨fr, _, hd, hm⟩ := h.mem
  ⟨fr, hd, Kg.init hm⟩

-- `ret` with the ghost `a'`.
theorem Kg.vret [Host] {S : Addr} {a' : α} {F : MProp 64} {d : Nat} {s t : MachineData}
    {ra : Int64} {fr : List Word} {Q : α → MachineData → Prop} {ls : List Label}
    {I' : CfgLabel → Nat → Unit → MachineData → Prop} (h : Kg (V S a' ∗ F) s ra fr t)
    (hd : fr.length = d) (hok : ok a') (hQ : ∀ t', t'.dmem = t.dmem → rax t' = rax t → Q a' t') :
    Program.Intercept ls (s.pushRa ra) I'
      (fun r t' => r = ra ∧ VPost V ok S F d Q s t' ∧ Sep.mod.Agree s t') t.retAddr.get!
      { regs := t.regs.set64 Reg64.rsp (t.regs.get64 Reg64.rsp + 8#64), zmms := t.zmms,
        status := t.status, dmem := t.dmem } :=
  h.ret fun t' hm hr => ⟨a', hQ t' hm hr, hok, fr, ra.toBitVec, hd, hm ▸ h.mem⟩
end

-- The view in front of the stack.
theorem Kg.vmem {P F : MProp 64} {s t : MachineData} {ra : Int64} {fr : List Word}
    (h : Kg (P ∗ F) s ra fr t) : (P ∗ Stk (rsp s) fr ra.toBitVec ∗ F).get t.dmem := by
  have := h.mem; rwa [sep_lc] at this

/-! ## Flags (after `symexec_norm`) -/

-- `cmpq c, x`: `zf` is set iff `x = c`.
theorem sub_beq_zero (x c : Word) : (x - c == BitVec.zero 64) = (x == c) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor <;> intro h <;> bv_decide

theorem neg_one_eq_none : (18446744073709551615#64 : Word) = Flat.NONE := rfl

-- `setne %al`: the bit `b`.
theorem setne_bit (x : Word) (b : Bool) :
    BitVec.setWidth 8 (x.replaceLow (BitVec.ofNat 8 b.toNat)) = if b = true then 1#8 else 0#8 := by
  rw [IsSpilled.setWidth_replaceLow]; cases b <;> rfl

/-! ## Bytes -/

section
variable {a : Addr} {bs : List (BitVec 8)} {F : MProp 64} {m : Mem 64} {i : Nat}

private theorem Bs.rot (a : Addr) (b : BitVec 8) (bs : List (BitVec 8)) (F : MProp 64) :
    Bs a (b :: bs) ∗ F = Bs (a + 1#64) bs ∗ (B8 a b ∗ F) := by
  simp only [Bs]; rw [MProp.sep_assoc, sep_lc]

private theorem addr_succ1 (a : Addr) (i : Nat) :
    a + BitVec.ofNat 64 (i + 1) = a + 1#64 + BitVec.ofNat 64 i := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem Bs.isSome (h : (Bs a bs ∗ F).get m) (hi : i < bs.length) :
    (m.loadInt (a + BitVec.ofNat 64 i) 1).isSome = true := by
  induction bs generalizing a F i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp only [Bs, MProp.sep_assoc] at h; simpa using B8.isSome h
    | succ i => rw [Bs.rot] at h; rw [addr_succ1]; exact ih h (by simpa using hi)

theorem Bs.rdb (h : (Bs a bs ∗ F).get m) (hi : i < bs.length) :
    rdb m (a + BitVec.ofNat 64 i) = bs[i] := by
  induction bs generalizing a F i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp only [Bs, MProp.sep_assoc] at h; simpa using B8.rdb h
    | succ i => rw [Bs.rot] at h; rw [addr_succ1]; exact ih h (by simpa using hi)
end

/-! ## `Mapping` -/

def MapM (a : Addr) (M : Flat.Mapping) : MProp 64 :=
  Arr a M.dest.toList ∗ Arr (a + 8192#64) M.pos.toList

section
variable {a : Addr} {M : Flat.Mapping} {F : MProp 64} {m : Mem 64} {p : Word}

theorem get_eq {α : Type} [Inhabited α] (v : Vector α MAX_N) (hp : p.toNat < MAX_N) :
    Flat.get v p = v[p.toNat] := dite_eq_left hp

theorem MapM.rd_dest (h : (MapM a M ∗ F).get m) (hp : p.toNat < MAX_N) :
    rd m (slotAt a p.toNat) = Flat.get M.dest p := by
  unfold MapM at h; rw [MProp.sep_assoc] at h
  exact (Arr.rd h (by simpa using hp)).trans (by simp [get_eq _ hp])

theorem MapM.isSome_dest (h : (MapM a M ∗ F).get m) (hp : p.toNat < MAX_N) :
    (m.loadInt (slotAt a p.toNat) 8).isSome = true := by
  unfold MapM at h; rw [MProp.sep_assoc] at h
  exact Arr.isSome h (by simpa using hp)

theorem MapM.rd_pos (h : (MapM a M ∗ F).get m) (hp : p.toNat < MAX_N) :
    rd m (slotAt (a + 8192#64) p.toNat) = Flat.get M.pos p := by
  unfold MapM at h; rw [MProp.sep_assoc, sep_lc] at h
  exact (Arr.rd h (by simpa using hp)).trans (by simp [get_eq _ hp])

theorem MapM.isSome_pos (h : (MapM a M ∗ F).get m) (hp : p.toNat < MAX_N) :
    (m.loadInt (slotAt (a + 8192#64) p.toNat) 8).isSome = true := by
  unfold MapM at h; rw [MProp.sep_assoc, sep_lc] at h
  exact Arr.isSome h (by simpa using hp)

theorem MapM.store_dest (h : (MapM a M ∗ F).get m) (hp : p.toNat < MAX_N) (w : Word) :
    (MapM a ⟨Flat.put M.dest p w, M.pos⟩ ∗ F).get (m.storeInt (slotAt a p.toNat) 8 w.toInt) := by
  unfold MapM at h ⊢; rw [MProp.sep_assoc] at h ⊢
  simpa [Flat.put, slotAt] using Arr.store h (by simpa using hp) w

theorem MapM.store_pos (h : (MapM a M ∗ F).get m) (hp : p.toNat < MAX_N) (w : Word) :
    (MapM a ⟨M.dest, Flat.put M.pos p w⟩ ∗ F).get
      (m.storeInt (slotAt (a + 8192#64) p.toNat) 8 w.toInt) := by
  unfold MapM at h ⊢; rw [MProp.sep_assoc, sep_lc] at h ⊢
  simpa [Flat.put, slotAt] using Arr.store h (by simpa using hp) w
end

/-! ## `MappingBuilder` -/

-- The members of a `MappingBuilder`, the words and bytes that they point to, and the `Mapping`.
structure BG where
  src : Addr
  m : Word
  tgt : Addr
  n : Word
  drp : Addr
  strat : BitVec 8
  mp : Addr
  saw : BitVec 8
  sw : List Word
  tw : List Word
  db : List (BitVec 8)
  M : Flat.Mapping

structure BG.Ok (b : BG) : Prop where
  m : b.m.toNat ≤ MAX_N
  n : b.n.toNat ≤ MAX_N
  sw : b.sw.length = b.m.toNat
  tw : b.tw.length = b.n.toNat
  db : b.db.length = b.m.toNat

def BView (B : Addr) (b : BG) : MProp 64 :=
  Wd B b.src ∗ Wd (B + 8#64) b.m ∗ Wd (B + 16#64) b.tgt ∗ Wd (B + 24#64) b.n
    ∗ Wd (B + 32#64) b.drp ∗ B8 (B + 40#64) b.strat ∗ Wd (B + 48#64) b.mp ∗ B8 (B + 56#64) b.saw
    ∗ Arr b.src b.sw ∗ Arr b.tgt b.tw ∗ Bs b.drp b.db ∗ MapM b.mp b.M

-- The flat `MappingBuilder`.
def BG.fl (b : BG) : Flat.Builder :=
  ⟨vec (b.sw.map StackSlot.ofWord), b.m, vec (b.tw.map StackSlot.ofWord), b.n, vec b.db,
    b.strat == 1⟩

abbrev BThm [Host] [FunDecls] (prog : Program) (A : BG → MachineData → Prop) (d : Nat)
    (Q : BG → BG → MachineData → MachineData → Prop) : Prop :=
  VThm BView BG.Ok prog A d Q

abbrev BSpec [Host] [FunDecls] (f : Label) (A : BG → MachineData → Prop) (d : Nat)
    (Q : BG → BG → MachineData → MachineData → Prop) : Prop :=
  VSpec BView BG.Ok f A d Q

/-! ### Loads of the members -/

section
variable {B : Addr} {b : BG} {F : MProp 64} {m : Mem 64}

theorem BView.rd_drp (h : (BView B b ∗ F).get m) : rd m (B + 32#64) = b.drp :=
  rd_of_eq h (by unfold BView; ecancel)
theorem BView.isSome_drp (h : (BView B b ∗ F).get m) : (m.loadInt (B + 32#64) 8).isSome = true :=
  isSome_of_eq b.drp h (by unfold BView; ecancel)
theorem BView.rd_mp (h : (BView B b ∗ F).get m) : rd m (B + 48#64) = b.mp :=
  rd_of_eq h (by unfold BView; ecancel)
theorem BView.isSome_mp (h : (BView B b ∗ F).get m) : (m.loadInt (B + 48#64) 8).isSome = true :=
  isSome_of_eq b.mp h (by unfold BView; ecancel)
end


theorem get_vecL {α : Type} [Inhabited α] {l : List α} {i : Word} (hi : i.toNat < l.length)
    (hl : l.length ≤ MAX_N) : Flat.get (vec l) i = l[i.toNat] := by
  simp [Flat.get, vec, Nat.lt_of_lt_of_le hi hl, hi]

/-! ### The dropped bytes and the mapping -/

section
variable {B : Addr} {b : BG} {F : MProp 64} {m : Mem 64} {p : Word}

theorem BView.rdb_drp (h : (BView B b ∗ F).get m) (hok : b.Ok) (hp : p.toNat < b.m.toNat) :
    rdb m (b.drp + p) = Flat.get b.fl.dropped p := by
  obtain ⟨R, e⟩ : ∃ R, BView B b ∗ F = Bs b.drp b.db ∗ R := ⟨_, by unfold BView; ecancel⟩
  have hi : p.toNat < b.db.length := hok.db ▸ hp
  have := Bs.rdb (e ▸ h) hi
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  rw [this]; exact (get_vecL hi (hok.db ▸ hok.m)).symm

theorem BView.isSome_drp_byte (h : (BView B b ∗ F).get m) (hok : b.Ok) (hp : p.toNat < b.m.toNat) :
    (m.loadInt (b.drp + p) 1).isSome = true := by
  obtain ⟨R, e⟩ : ∃ R, BView B b ∗ F = Bs b.drp b.db ∗ R := ⟨_, by unfold BView; ecancel⟩
  have := Bs.isSome (e ▸ h) (hok.db ▸ hp)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem BView.mapM (h : (BView B b ∗ F).get m) : ∃ R, (MapM b.mp b.M ∗ R).get m :=
  ⟨_, (by unfold BView; ecancel : BView B b ∗ F = MapM b.mp b.M ∗ _) ▸ h⟩

-- `movq %rdx, (%rcx,%rsi,8)` then `movq %rsi, 8192(%rcx,%rdx,8)`: `Mapping::bind`.
theorem BView.store_bind (h : (BView B b ∗ F).get m) {t : Word} (hp : p.toNat < MAX_N)
    (ht : t.toNat < MAX_N) :
    (BView B { b with M := b.M.bind p t } ∗ F).get
      ((m.storeInt (slotAt b.mp p.toNat) 8 t.toInt).storeInt (slotAt (b.mp + 8192#64) t.toNat) 8
        p.toInt) := by
  obtain ⟨R, e⟩ : ∃ R, ∀ M', BView B { b with M := M' } ∗ F = MapM b.mp M' ∗ R :=
    ⟨_, fun M' => by simp only [BView]; ecancel⟩
  rw [e]
  exact MapM.store_pos (MapM.store_dest ((e b.M) ▸ h) hp t) ht p
end

-- A step that writes the memory of the view.
theorem Kg.vstore {P P' F : MProp 64} {s t t' : MachineData} {ra : Int64} {fr : List Word}
    (h : Kg (P ∗ F) s ra fr t) (hm : (P' ∗ Stk (rsp s) fr ra.toBitVec ∗ F).get t'.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) (hbx : t'.regs.rbx = t.regs.rbx)
    (hbp : t'.regs.rbp = t.regs.rbp) (h12 : t'.regs.r12 = t.regs.r12)
    (h13 : t'.regs.r13 = t.regs.r13) (h14 : t'.regs.r14 = t.regs.r14)
    (h15 : t'.regs.r15 = t.regs.r15) : Kg (P' ∗ F) s ra fr t' :=
  ⟨by rw [sep_lc] at hm; exact hm, hsp.trans h.sp, hbx.trans h.bx, hbp.trans h.bp,
    h12.trans h.r12, h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩

theorem slot_8192 (a : Addr) (i : Nat) : slotAt a i + 8192#64 = slotAt (a + 8192#64) i := by
  unfold slotAt; ac_rfl

-- `movzbl` then `testb %al, %al`.
theorem zext_byte (x : BitVec 8) :
    BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = x := by bv_decide

theorem sub_beq_zero' (x c : Word) : (x - c == 0#64) = (x == c) := sub_beq_zero x c

/-! ### Loads of the other members and of the slots -/

section
variable {B : Addr} {b : BG} {F : MProp 64} {m : Mem 64} {i : Word}

theorem BView.rd_src (h : (BView B b ∗ F).get m) : rd m B = b.src :=
  rd_of_eq h (by unfold BView; ecancel)
theorem BView.isSome_src (h : (BView B b ∗ F).get m) : (m.loadInt B 8).isSome = true :=
  isSome_of_eq b.src h (by unfold BView; ecancel)
theorem BView.rd_m (h : (BView B b ∗ F).get m) : rd m (B + 8#64) = b.m :=
  rd_of_eq h (by unfold BView; ecancel)
theorem BView.isSome_m (h : (BView B b ∗ F).get m) : (m.loadInt (B + 8#64) 8).isSome = true :=
  isSome_of_eq b.m h (by unfold BView; ecancel)
theorem BView.rd_tgt (h : (BView B b ∗ F).get m) : rd m (B + 16#64) = b.tgt :=
  rd_of_eq h (by unfold BView; ecancel)
theorem BView.isSome_tgt (h : (BView B b ∗ F).get m) : (m.loadInt (B + 16#64) 8).isSome = true :=
  isSome_of_eq b.tgt h (by unfold BView; ecancel)
theorem BView.rd_n (h : (BView B b ∗ F).get m) : rd m (B + 24#64) = b.n :=
  rd_of_eq h (by unfold BView; ecancel)
theorem BView.isSome_n (h : (BView B b ∗ F).get m) : (m.loadInt (B + 24#64) 8).isSome = true :=
  isSome_of_eq b.n h (by unfold BView; ecancel)

theorem BView.arr_src (h : (BView B b ∗ F).get m) : ∃ R, (Arr b.src b.sw ∗ R).get m :=
  ⟨_, (by unfold BView; ecancel : BView B b ∗ F = Arr b.src b.sw ∗ _) ▸ h⟩

theorem BView.arr_tgt (h : (BView B b ∗ F).get m) : ∃ R, (Arr b.tgt b.tw ∗ R).get m :=
  ⟨_, (by unfold BView; ecancel : BView B b ∗ F = Arr b.tgt b.tw ∗ _) ▸ h⟩

theorem BView.isSome_sw (h : (BView B b ∗ F).get m) (hok : b.Ok) (hi : i.toNat < b.m.toNat) :
    (m.loadInt (slotAt b.src i.toNat) 8).isSome = true :=
  let ⟨_, h⟩ := BView.arr_src h; Arr.isSome h (hok.sw ▸ hi)

-- Slot `i < m` of the source.
theorem BView.rd_sw (h : (BView B b ∗ F).get m) (hok : b.Ok) (hi : i.toNat < b.m.toNat) :
    StackSlot.ofWord (rd m (slotAt b.src i.toNat)) = Flat.get b.fl.source i := by
  obtain ⟨_, h⟩ := BView.arr_src h
  have hi' : i.toNat < b.sw.length := hok.sw ▸ hi
  show _ = Flat.get (vec (b.sw.map StackSlot.ofWord)) i
  rw [get_vecL (by simpa using hi') (by simpa [hok.sw] using hok.m), List.getElem_map]
  exact congrArg StackSlot.ofWord (Arr.rd h hi')

theorem BView.isSome_tw (h : (BView B b ∗ F).get m) (hok : b.Ok) (hi : i.toNat < b.n.toNat) :
    (m.loadInt (slotAt b.tgt i.toNat) 8).isSome = true :=
  let ⟨_, h⟩ := BView.arr_tgt h; Arr.isSome h (hok.tw ▸ hi)

-- Slot `i < n` of the target.
theorem BView.rd_tw (h : (BView B b ∗ F).get m) (hok : b.Ok) (hi : i.toNat < b.n.toNat) :
    StackSlot.ofWord (rd m (slotAt b.tgt i.toNat)) = Flat.get b.fl.target i := by
  obtain ⟨_, h⟩ := BView.arr_tgt h
  have hi' : i.toNat < b.tw.length := hok.tw ▸ hi
  show _ = Flat.get (vec (b.tw.map StackSlot.ofWord)) i
  rw [get_vecL (by simpa using hi') (by simpa [hok.tw] using hok.n), List.getElem_map]
  exact congrArg StackSlot.ofWord (Arr.rd h hi')

-- Byte 4 of the target word `i < n`.
theorem BView.b8_kind (h : (BView B b ∗ F).get m) (hok : b.Ok) (hi : i.toNat < b.n.toNat) :
    ∃ R, (B8 (slotAt b.tgt i.toNat + 4#64) (Flat.get b.fl.target i).kind ∗ R).get m := by
  obtain ⟨R, h⟩ := BView.arr_tgt h
  have hi' : i.toNat < b.tw.length := hok.tw ▸ hi
  obtain ⟨Q, e⟩ := Arr.focus b.tgt b.tw hi'
  obtain ⟨P, e'⟩ := Wd.focus_byte (slotAt b.tgt i.toNat) b.tw[i.toNat] (j := 4) (by decide)
  have hk : (Flat.get b.fl.target i).kind = b.tw[i.toNat].extractLsb' (8 * 4) 8 := by
    show (Flat.get (vec (b.tw.map StackSlot.ofWord)) i).kind = _
    rw [get_vecL (by simpa using hi') (by simpa [hok.tw] using hok.n), List.getElem_map]
    rfl
  rw [e] at h
  change ((Wd (slotAt b.tgt i.toNat) b.tw[i.toNat] ∗ Q) ∗ R).get m at h
  rw [e', MProp.sep_assoc, MProp.sep_assoc] at h
  exact ⟨_, hk ▸ h⟩

theorem BView.rdb_kind (h : (BView B b ∗ F).get m) (hok : b.Ok) (hi : i.toNat < b.n.toNat) :
    rdb m (slotAt b.tgt i.toNat + 4#64) = (Flat.get b.fl.target i).kind :=
  let ⟨_, h⟩ := BView.b8_kind h hok hi; B8.rdb h

theorem BView.isSome_kind (h : (BView B b ∗ F).get m) (hok : b.Ok) (hi : i.toNat < b.n.toNat) :
    (m.loadInt (slotAt b.tgt i.toNat + 4#64) 1).isSome = true :=
  let ⟨_, h⟩ := BView.b8_kind h hok hi; B8.isSome h
end

end Bbu.Unit
