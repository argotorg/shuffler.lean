module

public import BbuKraken.Unit.Defs
import all BbuKraken.Unit.Defs
public import BbuKraken.Top
import all BbuKraken.Top
public import BbuKraken.Sep.Stores
import all BbuKraken.Sep.Stores
public import BbuKraken.Sep.Carve
import all BbuKraken.Sep.Carve
public import BbuKraken.Unit.TopCtor
import all BbuKraken.Unit.TopCtor
public import ProofKit.Idioms
import all ProofKit.Idioms

@[expose] public section

/-!
# The frame of `build_bottom_up`

`build_bottom_up` (`build/kraken/c/build_bottom_up.S`) does `subq $32872,%rsp` after the return address.
The offsets from the new `rsp`, `topS s = rsp s - 32880` (one def each):

| def | offset | bytes |
|---|---|---|
| | 0 | the struct up to `m_plannedMapping` (`Em`, `EmSize`) |
| `offPM` | 16464 | `m_plannedMapping` |
| `offPad` | 16472 | pad |
| `offPD` | 16480 | the local planned `destinationOf` (`MAX_N` words) |
| `offPP` | 24672 | the local planned `positionOf` (`MAX_N` words) |
| `offLoc` | 32864 | pad (the end of `Lc`) |
| `frSub` | 32872 | the return address |
| `offOps` | 32880 | the stack argument `ops` (`rsp s`) |
| `offBlk` | 32888 | the stack argument `blocked` (`rsp s + 8`) |

Before the call of `buildBottomUp`, the memory is `Em ∗ Lc ∗ R0`: `Lc` holds the words at
`offPM .. offLoc` (`Loc`), and `R0` is the memory at the entry outside the first `offLoc` bytes,
as one exact part. The loops write only `Em` and `Lc`. At the call, `R0` gives the arrays of the
callee and its stack (`Carve`).
-/

namespace Bbu.Unit
open Bbu.Sep

namespace Top

/-! ## The offsets of the frame -/

abbrev frSub : Nat := 32872
abbrev offPM : Nat := 16464
abbrev offPad : Nat := 16472
abbrev offPD : Nat := 16480
abbrev offPP : Nat := 24672
abbrev offLoc : Nat := 32864
abbrev offOps : Nat := 32880
abbrev offBlk : Nat := 32888

theorem frSub_eq : frSub = topLocals := rfl
theorem offPM_eq (S : Addr) : Fld.plannedMapping S = S + BitVec.ofNat 64 offPM := rfl
theorem offs_eq : EmSize = offPM ∧ offPM + 8 = offPad ∧ offPad + 8 = offPD ∧
    offPD + 8 * MAX_N = offPP ∧ offPP + 8 * MAX_N = offLoc ∧ offLoc + 8 = frSub ∧
    frSub + 8 = offOps ∧ offOps + 8 = offBlk := by decide

/-! ## The struct and the rest -/

-- The struct in the frame.
def topS (s : MachineData) : Addr := rsp s - BitVec.ofNat 64 offOps

section
variable (s : MachineData) (ra : Int64)

theorem pushRa_sp : (s.pushRa ra).regs.rsp.toBitVec - BitVec.ofNat 64 frSub = topS s := by
  rw [show (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 by simp [MachineData.pushRa]]
  unfold topS frSub offOps; bv_omega

theorem topS_add : topS s + BitVec.ofNat 64 offOps = rsp s := by unfold topS; bv_omega

-- The memory at the entry outside the struct and the locals.
noncomputable def R0 : MProp 64 :=
  MProp.mk (Eq (cut (s.pushRa ra).dmem fun b => ¬In (topS s) offLoc b))

-- The struct at the entry: the words that the stack holds.
def hdr0 : Hdr :=
  let m := (s.pushRa ra).dmem
  let S := topS s
  { tgt := rd m (Fld.target S), n := rd m (Fld.targetSize S), spl := rd m (Fld.spills S),
    data := rd m (Fld.stack_data S), len := rd m (Fld.stack_size S),
    ops := rd m (Fld.stack_trace S), nops := rd m (Fld.stack_traceSize S),
    dest := Vector.ofFn fun i => rd m (Fld.mapping_destinationOf S i),
    pos := Vector.ofFn fun i => rd m (Fld.mapping_positionOf S i),
    pend := rd m (Fld.pendingGenerations S), blkOff := rd m (Fld.blocked_offset S),
    blkExc := rd m (Fld.blocked_excess S) }

-- The members that the constructor does not initialize.
def u0 : Flat.Uninit := ⟨(hdr0 s ra).dest, (hdr0 s ra).pos, (hdr0 s ra).blkOff, (hdr0 s ra).blkExc⟩

-- The struct after the stores of the entry block, with `dest`, `pos` and `pend` of a loop.
def hdr (D P : Vector Word MAX_N) (E : Word) : Hdr where
  tgt := s.regs.rcx.toBitVec
  n := s.regs.rsi.toBitVec
  spl := s.regs.r9.toBitVec
  data := s.regs.rdx.toBitVec
  len := s.regs.rdi.toBitVec
  ops := opsArg s
  nops := 0
  dest := D
  pos := P
  pend := E
  blkOff := (hdr0 s ra).blkOff
  blkExc := (hdr0 s ra).blkExc


end

/-! ## The locals of the frame -/

-- The words at `offPM .. offLoc`: `m_plannedMapping`, a pad, and the local planned mapping.
structure Loc where
  pm : Word
  pad : Word
  pd : Vector Word MAX_N
  pp : Vector Word MAX_N

def Lc (S : Addr) (L : Loc) : MProp 64 :=
  Wd (S + BitVec.ofNat 64 offPM) L.pm ∗ Wd (S + BitVec.ofNat 64 offPad) L.pad ∗
    Arr (S + BitVec.ofNat 64 offPD) L.pd.toList ∗ Arr (S + BitVec.ofNat 64 offPP) L.pp.toList

section
variable (s : MachineData) (ra : Int64)

-- The locals at the entry: the words that the stack holds.
def loc0 : Loc :=
  let m := (s.pushRa ra).dmem
  let S := topS s
  { pm := rd m (S + BitVec.ofNat 64 offPM), pad := rd m (S + BitVec.ofNat 64 offPad),
    pd := Vector.ofFn fun i => rd m (S + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * i.1)),
    pp := Vector.ofFn fun i => rd m (S + BitVec.ofNat 64 offPP + BitVec.ofNat 64 (8 * i.1)) }

end

theorem Lc.own (S : Addr) (L : Loc) : Own (Lc S L) (Rng S offPM (offLoc - offPM)) := by
  unfold Lc
  exact (Wd.own_rng S (o := offPM) L.pm (by decide)).sep_rng
    ((Wd.own_rng S (o := offPad) L.pad (by decide)).sep_rng
    ((Arr.own_rng S (o := offPD) L.pd (by decide)).sep_rng
      (Arr.own_rng S (o := offPP) L.pp (by decide)) rfl) rfl) rfl

-- The struct and the locals own the first `offLoc` bytes.
theorem EmLc.own (S : Addr) (h : Hdr) (L : Loc) : Own (Em S h ∗ Lc S L) (In S offLoc) :=
  (((Em.own S h).congr fun _ => in_iff_rng).sep_rng (Lc.own S L) rfl).congr fun _ => in_iff_rng.symm

-- Change the atom `A` of `X` to `A'`, with the same rest `R`.
theorem swap_eq {X X' A A' R : MProp 64} {m m' : Mem 64} (h : X.get m) (e : X = A ∗ R)
    (e' : X' = A' ∗ R) (hA : (A ∗ R).get m → (A' ∗ R).get m') : X'.get m' := e' ▸ hA (e ▸ h)

/-! ## Loads and stores of the locals -/

section
variable {S : Addr} {h : Hdr} {L : Loc} {R : MProp 64} {m : Mem 64}

theorem Lc.st_pm (hm : (Em S h ∗ Lc S L ∗ R).get m) (w : Word) :
    (Em S h ∗ Lc S { L with pm := w } ∗ R).get
      (m.storeInt (S + BitVec.ofNat 64 offPM) 8 w.toInt) :=
  swap_eq hm (A := Wd (S + BitVec.ofNat 64 offPM) L.pm) (by unfold Lc; ecancel)
    (by unfold Lc; ecancel) (Wd.store · w)

theorem Lc.st_pd (hm : (Em S h ∗ Lc S L ∗ R).get m) {i : Nat} (hi : i < MAX_N) (w : Word) :
    (Em S h ∗ Lc S { L with pd := L.pd.set i w } ∗ R).get
      (m.storeInt (S + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * i)) 8 w.toInt) :=
  swap_eq hm (A := Arr (S + BitVec.ofNat 64 offPD) L.pd.toList)
    (A' := Arr (S + BitVec.ofNat 64 offPD) (L.pd.set i w).toList)
    (by unfold Lc; ecancel) (by unfold Lc; ecancel)
    fun h => by rw [Vector.toList_set]; exact Arr.store h (by simpa using hi) w

theorem Lc.st_pp (hm : (Em S h ∗ Lc S L ∗ R).get m) {i : Nat} (hi : i < MAX_N) (w : Word) :
    (Em S h ∗ Lc S { L with pp := L.pp.set i w } ∗ R).get
      (m.storeInt (S + BitVec.ofNat 64 offPP + BitVec.ofNat 64 (8 * i)) 8 w.toInt) :=
  swap_eq hm (A := Arr (S + BitVec.ofNat 64 offPP) L.pp.toList)
    (A' := Arr (S + BitVec.ofNat 64 offPP) (L.pp.set i w).toList)
    (by unfold Lc; ecancel) (by unfold Lc; ecancel)
    fun h => by rw [Vector.toList_set]; exact Arr.store h (by simpa using hi) w

-- `Em ∗ Lc ∗ R` with one atom `A` in front.
theorem Lc.focus (hm : (Em S h ∗ Lc S L ∗ R).get m) {A : MProp 64}
    (e : ∃ R', Em S h ∗ Lc S L ∗ R = A ∗ R') : ∃ R', (A ∗ R').get m :=
  let ⟨R', e⟩ := e; ⟨R', e ▸ hm⟩

theorem Lc.isSome_pm (hm : (Em S h ∗ Lc S L ∗ R).get m) :
    (m.loadInt (S + BitVec.ofNat 64 offPM) 8).isSome = true := by
  obtain ⟨_, h'⟩ := Lc.focus hm (A := Wd (S + BitVec.ofNat 64 offPM) L.pm) ⟨_, by unfold Lc; ecancel⟩
  exact Wd.isSome h'

theorem Lc.rd_pd (hm : (Em S h ∗ Lc S L ∗ R).get m) {i : Nat} (hi : i < MAX_N) :
    rd m (S + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * i)) = L.pd[i] := by
  obtain ⟨_, h'⟩ := Lc.focus hm (A := Arr (S + BitVec.ofNat 64 offPD) L.pd.toList)
    ⟨_, by unfold Lc; ecancel⟩
  exact (Arr.rd h' (by simpa using hi)).trans (by simp)

theorem Lc.isSome_pd (hm : (Em S h ∗ Lc S L ∗ R).get m) {i : Nat} (hi : i < MAX_N) :
    (m.loadInt (S + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  obtain ⟨_, h'⟩ := Lc.focus hm (A := Arr (S + BitVec.ofNat 64 offPD) L.pd.toList)
    ⟨_, by unfold Lc; ecancel⟩
  exact Arr.isSome h' (by simpa using hi)

theorem Lc.rd_pp (hm : (Em S h ∗ Lc S L ∗ R).get m) {i : Nat} (hi : i < MAX_N) :
    rd m (S + BitVec.ofNat 64 offPP + BitVec.ofNat 64 (8 * i)) = L.pp[i] := by
  obtain ⟨_, h'⟩ := Lc.focus hm (A := Arr (S + BitVec.ofNat 64 offPP) L.pp.toList)
    ⟨_, by unfold Lc; ecancel⟩
  exact (Arr.rd h' (by simpa using hi)).trans (by simp)

theorem Lc.isSome_pp (hm : (Em S h ∗ Lc S L ∗ R).get m) {i : Nat} (hi : i < MAX_N) :
    (m.loadInt (S + BitVec.ofNat 64 offPP + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  obtain ⟨_, h'⟩ := Lc.focus hm (A := Arr (S + BitVec.ofNat 64 offPP) L.pp.toList)
    ⟨_, by unfold Lc; ecancel⟩
  exact Arr.isSome h' (by simpa using hi)

end

/-! ## Byte sets -/

theorem inside_one {a b : Addr} {n : Nat} {bs : List (Addr × Nat)} :
    Mem.Blocks.Inside b 1 ((a, n) :: bs) ↔ In a n b ∨ Mem.Blocks.Inside b 1 bs := by
  simp only [Mem.Blocks.Inside, In, Nat.add_one_le_iff]

theorem inside_one_nil {a b : Addr} {n : Nat} : Mem.Blocks.Inside b 1 [(a, n)] ↔ In a n b := by
  rw [inside_one]; simp [Mem.Blocks.Inside]

theorem mapped_sub {a a' : Addr} {n n' : Nat} {m : Mem 64} (h : Mem.Mapped [(a, n)] m)
    (hs : ∀ b, In a' n' b → In a n b) : Mem.Mapped [(a', n')] m := fun b hb =>
  h b (inside_one_nil.mpr (hs b (inside_one_nil.mp hb)))

section
variable {s : MachineData} {ra : Int64}

-- The frame at the entry is mapped.
theorem frame0 (hp : TopPre s) : Mem.Mapped [frame topF s] (s.pushRa ra).dmem := by
  simp only [MachineData.dmem_pushRa]
  exact hp.frame.storeInt _ _ _

-- The struct is in the frame.
theorem in_frame_of_S (hp : TopPre s) {b : Addr} (h : In (topS s) offOps b) :
    In (rsp s - BitVec.ofNat 64 topF) topF b := by
  have := hp.rsp_ge
  unfold In topS at *; simp only [topF_eq, offOps] at *; bv_omega


end



/-! ## Stores to the struct

The addresses are in the form of the `kvcgen64` goals: `S + k` with the offset `k` of the field. -/

section
variable {S : Addr} {h : Hdr} {R : MProp 64} {m : Mem 64}

theorem Em.st_tgt (hm : (Em S h ∗ R).get m) (w : Word) :
    (Em S { h with tgt := w } ∗ R).get (m.storeInt S 8 w.toInt) :=
  swap_of_eq hm (A := Wd (Fld.target S) h.tgt) (by unfold Em; ecancel) (by unfold Em; ecancel)
    (Wd.store · w)

theorem Em.st_n (hm : (Em S h ∗ R).get m) (w : Word) :
    (Em S { h with n := w } ∗ R).get (m.storeInt (S + 8#64) 8 w.toInt) :=
  swap_of_eq hm (A := Wd (Fld.targetSize S) h.n) (by unfold Em; ecancel) (by unfold Em; ecancel)
    (Wd.store · w)

theorem Em.st_spl (hm : (Em S h ∗ R).get m) (w : Word) :
    (Em S { h with spl := w } ∗ R).get (m.storeInt (S + 16#64) 8 w.toInt) :=
  swap_of_eq hm (A := Wd (Fld.spills S) h.spl) (by unfold Em; ecancel) (by unfold Em; ecancel)
    (Wd.store · w)

theorem Em.st_data (hm : (Em S h ∗ R).get m) (w : Word) :
    (Em S { h with data := w } ∗ R).get (m.storeInt (S + 24#64) 8 w.toInt) :=
  swap_of_eq hm (A := Wd (Fld.stack_data S) h.data) (by unfold Em; ecancel) (by unfold Em; ecancel)
    (Wd.store · w)

theorem Em.st_len (hm : (Em S h ∗ R).get m) (w : Word) :
    (Em S { h with len := w } ∗ R).get (m.storeInt (S + 32#64) 8 w.toInt) :=
  swap_of_eq hm (A := Wd (Fld.stack_size S) h.len) (by unfold Em; ecancel) (by unfold Em; ecancel)
    (Wd.store · w)

theorem Em.st_ops (hm : (Em S h ∗ R).get m) (w : Word) :
    (Em S { h with ops := w } ∗ R).get (m.storeInt (S + 40#64) 8 w.toInt) :=
  swap_of_eq hm (A := Wd (Fld.stack_trace S) h.ops) (by unfold Em; ecancel) (by unfold Em; ecancel)
    (Wd.store · w)

theorem Em.st_nops (hm : (Em S h ∗ R).get m) (w : Word) :
    (Em S { h with nops := w } ∗ R).get (m.storeInt (S + 48#64) 8 w.toInt) :=
  swap_of_eq hm (A := Wd (Fld.stack_traceSize S) h.nops) (by unfold Em; ecancel)
    (by unfold Em; ecancel) (Wd.store · w)

theorem Em.st_pend (hm : (Em S h ∗ R).get m) (w : Word) :
    (Em S { h with pend := w } ∗ R).get (m.storeInt (S + 16440#64) 8 w.toInt) :=
  swap_of_eq hm (A := Wd (Fld.pendingGenerations S) h.pend) (by unfold Em; ecancel)
    (by unfold Em; ecancel) (Wd.store · w)

theorem Em.rd_pend (hm : (Em S h ∗ R).get m) : rd m (S + 16440#64) = h.pend :=
  rd_of_eq hm (by unfold Em; ecancel)

theorem Em.isSome_pend (hm : (Em S h ∗ R).get m) : (m.loadInt (S + 16440#64) 8).isSome = true :=
  isSome_of_eq h.pend hm (by unfold Em; ecancel)

-- A word of the struct at offset `o < 56` is mapped.
theorem Em.isSome_hd (hm : (Em S h ∗ R).get m) {o : Nat} (ho : o ∈ [0, 8, 16, 24, 32, 40, 48]) :
    (m.loadInt (S + BitVec.ofNat 64 o) 8).isSome = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact isSome_of_eq h.tgt hm (by unfold Em; rw [BitVec.add_zero]; ecancel)
  · exact isSome_of_eq h.n hm (by unfold Em; ecancel)
  · exact isSome_of_eq h.spl hm (by unfold Em; ecancel)
  · exact isSome_of_eq h.data hm (by unfold Em; ecancel)
  · exact isSome_of_eq h.len hm (by unfold Em; ecancel)
  · exact isSome_of_eq h.ops hm (by unfold Em; ecancel)
  · exact isSome_of_eq h.nops hm (by unfold Em; ecancel)

theorem Em.st_dest (hm : (Em S h ∗ R).get m) {i : Nat} (hi : i < MAX_N) (w : Word) :
    (Em S { h with dest := h.dest.set i w } ∗ R).get
      (m.storeInt (Fld.mapping_destinationOf S i) 8 w.toInt) :=
  swap_of_eq hm (A := Arr (S + 56#64) h.dest.toList) (A' := Arr (S + 56#64) (h.dest.set i w).toList)
    (by unfold Em; ecancel) (by unfold Em; ecancel)
    fun h => by rw [Vector.toList_set]; exact Arr.store h (by simpa using hi) w

theorem Em.st_pos (hm : (Em S h ∗ R).get m) {i : Nat} (hi : i < MAX_N) (w : Word) :
    (Em S { h with pos := h.pos.set i w } ∗ R).get
      (m.storeInt (Fld.mapping_positionOf S i) 8 w.toInt) :=
  swap_of_eq hm (A := Arr (S + 8248#64) h.pos.toList) (A' := Arr (S + 8248#64) (h.pos.set i w).toList)
    (by unfold Em; ecancel) (by unfold Em; ecancel)
    fun h => by rw [Vector.toList_set]; exact Arr.store h (by simpa using hi) w

theorem Em.arr_pos (hm : (Em S h ∗ R).get m) : ∃ R', (Arr (S + 8248#64) h.pos.toList ∗ R').get m := by
  obtain ⟨R', e⟩ : ∃ R', Em S h ∗ R = Arr (S + 8248#64) h.pos.toList ∗ R' := ⟨_, by unfold Em; ecancel⟩
  exact ⟨R', e ▸ hm⟩

theorem Em.arr_dest (hm : (Em S h ∗ R).get m) : ∃ R', (Arr (S + 56#64) h.dest.toList ∗ R').get m := by
  obtain ⟨R', e⟩ : ∃ R', Em S h ∗ R = Arr (S + 56#64) h.dest.toList ∗ R' := ⟨_, by unfold Em; ecancel⟩
  exact ⟨R', e ▸ hm⟩

theorem Em.rd_pos (hm : (Em S h ∗ R).get m) {i : Nat} (hi : i < MAX_N) :
    rd m (Fld.mapping_positionOf S i) = h.pos[i] := by
  obtain ⟨R', h'⟩ := Em.arr_pos hm
  exact (Arr.rd h' (by simpa using hi)).trans (by simp)

theorem Em.isSome_pos (hm : (Em S h ∗ R).get m) {i : Nat} (hi : i < MAX_N) :
    (m.loadInt (Fld.mapping_positionOf S i) 8).isSome = true := by
  obtain ⟨R', h'⟩ := Em.arr_pos hm
  exact Arr.isSome h' (by simpa using hi)

theorem Em.isSome_dest (hm : (Em S h ∗ R).get m) {i : Nat} (hi : i < MAX_N) :
    (m.loadInt (Fld.mapping_destinationOf S i) 8).isSome = true := by
  obtain ⟨R', h'⟩ := Em.arr_dest hm
  exact Arr.isSome h' (by simpa using hi)

end

/-! ## The states before the call -/

-- A state of the constructor: the struct holds `h`, the locals hold `L`, `rsp` is the struct,
-- and the callee-saved registers are the ones of the entry.
structure TS (s : MachineData) (ra : Int64) (h : Hdr) (L : Loc) (t : MachineData) : Prop where
  mem : (Em (topS s) h ∗ Lc (topS s) L ∗ R0 s ra).get t.dmem
  sp : t.regs.rsp.toBitVec = topS s
  rbx : t.regs.rbx = s.regs.rbx
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15
  g : TopGuard s

-- The argument registers of the entry (`r10` holds `data`), up to `.LB.build_bottom_up.6` and `.LB.build_bottom_up.19`.
structure TA (s t : MachineData) : Prop where
  rdi : t.regs.rdi = s.regs.rdi
  rsi : t.regs.rsi = s.regs.rsi
  rcx : t.regs.rcx = s.regs.rcx
  r8 : t.regs.r8 = s.regs.r8
  r9 : t.regs.r9 = s.regs.r9
  r10 : t.regs.r10 = s.regs.rdx

section
variable {s : MachineData} {ra : Int64} {h h' : Hdr} {L L' : Loc} {t t' : MachineData}

-- A step that keeps `rsp` and the callee-saved registers, with a new memory.
theorem TS.step (hs : TS s ra h L t) (hm : (Em (topS s) h' ∗ Lc (topS s) L' ∗ R0 s ra).get t'.dmem)
    (e0 : t'.regs.rsp = t.regs.rsp) (e4 : t'.regs.rbx = t.regs.rbx) (e5 : t'.regs.rbp = t.regs.rbp)
    (e6 : t'.regs.r12 = t.regs.r12) (e7 : t'.regs.r13 = t.regs.r13)
    (e8 : t'.regs.r14 = t.regs.r14) (e9 : t'.regs.r15 = t.regs.r15) : TS s ra h' L' t' :=
  ⟨hm, e0 ▸ hs.sp, e4 ▸ hs.rbx, e5 ▸ hs.rbp, e6 ▸ hs.r12, e7 ▸ hs.r13, e8 ▸ hs.r14, e9 ▸ hs.r15,
    hs.g⟩

-- A step that keeps the memory, `rsp` and the callee-saved registers.
theorem TS.next (hs : TS s ra h L t) (hm : t'.dmem = t.dmem)
    (e0 : t'.regs.rsp = t.regs.rsp) (e4 : t'.regs.rbx = t.regs.rbx) (e5 : t'.regs.rbp = t.regs.rbp)
    (e6 : t'.regs.r12 = t.regs.r12) (e7 : t'.regs.r13 = t.regs.r13)
    (e8 : t'.regs.r14 = t.regs.r14) (e9 : t'.regs.r15 = t.regs.r15) : TS s ra h L t' :=
  hs.step (hm ▸ hs.mem) e0 e4 e5 e6 e7 e8 e9

theorem TS.cast (hs : TS s ra h L t) (e : h = h') (e' : L = L') : TS s ra h' L' t := e ▸ e' ▸ hs

theorem TA.next (ha : TA s t) (e1 : t'.regs.rdi = t.regs.rdi) (e2 : t'.regs.rsi = t.regs.rsi)
    (e3 : t'.regs.rcx = t.regs.rcx) (e4 : t'.regs.r8 = t.regs.r8) (e5 : t'.regs.r9 = t.regs.r9)
    (e6 : t'.regs.r10 = t.regs.r10) : TA s t' :=
  ⟨e1 ▸ ha.rdi, e2 ▸ ha.rsi, e3 ▸ ha.rcx, e4 ▸ ha.r8, e5 ▸ ha.r9, e6 ▸ ha.r10⟩

end

/-! ## The members after each loop -/

section
variable (s : MachineData) (ra : Int64)

-- `pos` after the first loop.
def Pn : Vector Word MAX_N := Flat.clearPos (nArg s) (hdr0 s ra).pos
-- `dest` and `pos` of the struct after the loops (the flat model).
def Dm : Vector Word MAX_N := Flat.bindDest (flatDest s) (mArg s) (hdr0 s ra).dest
def Pm : Vector Word MAX_N := Flat.bindPos (flatDest s) (mArg s) (Pn s ra)

-- The locals after the loops `.LB.build_bottom_up.0`, `.LB.build_bottom_up.2` and `.LB.build_bottom_up.5`.
def locB : Loc :=
  { loc0 s ra with
    pd := Flat.bindDest (flatDest s) (mArg s) (Flat.clearPos (mArg s) (loc0 s ra).pd)
    pp := Flat.bindPos (flatDest s) (mArg s) (Flat.clearPos (nArg s) (loc0 s ra).pp) }

-- The locals after `movq rax,16464(rsp)` (`rax = rsp + 16480`) in `.LB.build_bottom_up.9` and `.LB.build_bottom_up.15`.
def locP : Loc := { locB s ra with pm := topS s + BitVec.ofNat 64 offPD }

end

/-! ## The entry block -/

section
variable {s : MachineData} {ra : Int64} {h : Hdr} {L : Loc} {m : Mem 64} {t : MachineData}
  {R : MProp 64}

-- A byte outside the struct and the locals holds its value of the entry.
theorem get?_R0 (hm : (Em (topS s) h ∗ Lc (topS s) L ∗ R0 s ra).get m) {b : Addr}
    (hb : ¬In (topS s) offLoc b) : m.get? b = (s.pushRa ra).dmem.get? b := by
  simp only [Std.ExtHashMap.get?_eq_getElem?]
  rw [← MProp.sep_assoc] at hm
  unfold R0 at hm
  rw [get?_mk hm (EmLc.own _ _ _) hb, get?_cut_of hb]

-- The word at `rsp`: the pointer `ops`.
theorem ld_ops (hm : (Em (topS s) h ∗ Lc (topS s) L ∗ R0 s ra).get m) :
    m.loadInt (topS s + BitVec.ofNat 64 offOps) 8 = s.dmem.loadInt (rsp s) 8 := by
  rw [topS_add]
  refine Mem.loadInt_congr fun i hi => ?_
  rw [get?_R0 hm (by unfold In topS; simp only [offLoc, offOps]; bv_omega), MachineData.dmem_pushRa]
  exact Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj => by simp only [rsp] at *; bv_omega

theorem rd_ops (hm : (Em (topS s) h ∗ Lc (topS s) L ∗ R0 s ra).get m) :
    rd m (topS s + BitVec.ofNat 64 offOps) = opsArg s := by
  unfold rd; rw [ld_ops hm]; rfl

theorem isSome_ops (hm : (Em (topS s) h ∗ Lc (topS s) L ∗ R0 s ra).get m) (hp : TopPre s)
    (hg : TopGuard s) : (m.loadInt (topS s + BitVec.ofNat 64 offOps) 8).isSome = true := by
  rw [ld_ops hm]
  refine (hp.mem hg).mapped.loadInt_isSome ?_
  simp only [topOut, topIn, List.cons_append, Mem.Blocks.Inside]
  right; right; right; left; simp

theorem Em.isSome_tgt (hm : (Em (topS s) h ∗ R).get m) : (m.loadInt (topS s) 8).isSome = true := by
  have := Em.isSome_hd hm (o := 0) (by simp)
  rwa [BitVec.add_zero] at this

-- The struct is below the entry `rsp`.
theorem TS.stack (hs : TS s ra h L t) : t.StackAtOrBelow (s.pushRa ra) := by
  apply MachineData.stackAtOrBelow_of_toNat_lt
  simp only [Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp, hs.sp, topS, offOps]
  bv_omega

theorem TS.stack_of (hs : TS s ra h L t) {t' : MachineData} (e : t'.regs.rsp = t.regs.rsp) :
    t'.StackAtOrBelow (s.pushRa ra) := by
  apply MachineData.stackAtOrBelow_of_toNat_lt
  simp only [Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp, e, hs.sp, topS, offOps]
  bv_omega

end

/-! ## The flags of the entry block -/

-- `cmpq $1024, rsi; ja`: the jump is not taken.
theorem le_of_ja {d : Word}
    (h : (!((((d - 1024#64).toNat : Int) != (d.toNat : Int) - 1024)) &&
      !(d - 1024#64 == BitVec.zero 64)) = false) : d.toNat ≤ 1024 := by
  rw [Idioms.cf_sub_imm d 1024 (by decide)] at h
  simp only [Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h | h
  · omega
  · have : d - 1024#64 = 0#64 := h
    bv_omega

-- `cmpq $1024, rsi; ja`: the jump is taken.
theorem lt_of_ja {d : Word}
    (h : (!((((d - 1024#64).toNat : Int) != (d.toNat : Int) - 1024)) &&
      !(d - 1024#64 == BitVec.zero 64)) = true) : 1024 < d.toNat := by
  rw [Idioms.cf_sub_imm d 1024 (by decide)] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne] at h
  have : d - 1024#64 ≠ 0#64 := h.2
  bv_omega

-- `testq d, d; je`.
theorem zero_of_test {d : Word} (h : (d &&& d == BitVec.zero 64) = true) : d.toNat = 0 := by
  simp only [BitVec.and_self, beq_iff_eq] at h
  have : d = 0#64 := h
  simp [this]

theorem pos_of_test {d : Word} (h : (d &&& d == BitVec.zero 64) = false) : 0 < d.toNat := by
  simp only [BitVec.and_self, beq_eq_false_iff_ne] at h
  have : d ≠ 0#64 := h
  bv_omega

section
variable {s : MachineData}

theorem guard_of (h1 : decide (s.regs.rsi.toBitVec.toNat < s.regs.rdi.toBitVec.toNat) = false)
    (h2 : (!((((s.regs.rsi.toBitVec - 1024#64).toNat : Int) != (s.regs.rsi.toBitVec.toNat : Int) - 1024)) &&
      !(s.regs.rsi.toBitVec - 1024#64 == BitVec.zero 64)) = false) : TopGuard s :=
  ⟨by simp only [decide_eq_false_iff_not, Nat.not_lt] at h1; exact h1, le_of_ja h2⟩

theorem not_guard_of_cf (h1 : decide (s.regs.rsi.toBitVec.toNat < s.regs.rdi.toBitVec.toNat) = true) :
    ¬TopGuard s := fun hg => by
  have := hg.1
  simp only [decide_eq_true_eq] at h1
  exact absurd this (by simp only [mArg, nArg, rdi, rsi, Reg64s.get64_rdi, Reg64s.get64_rsi]; omega)

theorem not_guard_of_ja
    (h2 : (!((((s.regs.rsi.toBitVec - 1024#64).toNat : Int) != (s.regs.rsi.toBitVec.toNat : Int) - 1024)) &&
      !(s.regs.rsi.toBitVec - 1024#64 == BitVec.zero 64)) = true) : ¬TopGuard s := fun hg => by
  have := hg.n_le'
  have := lt_of_ja h2
  simp only [nArg, rsi, Reg64s.get64_rsi] at *
  omega

end

/-! ## The loops

The addresses and the flags in the form of the `kvcgen64` goals. -/

-- `pos[d]` and `dest[d]` at the index register `d`.
theorem pos_addr (S d : Addr) : S + d * 8#64 + 8248#64 = Fld.mapping_positionOf S d.toNat := by
  rw [Fld.eq_mapping_positionOf]; bv_omega

theorem dest_addr (S d : Addr) : S + d * 8#64 + 56#64 = Fld.mapping_destinationOf S d.toNat := by
  rw [Fld.eq_mapping_destinationOf]; bv_omega

-- `pos[k]` at the pointer `S + 8k`.
theorem posk_addr (S : Addr) (k : Nat) :
    S + BitVec.ofNat 64 (8 * k) + 8248#64 = Fld.mapping_positionOf S k := by
  rw [Fld.eq_mapping_positionOf]; bv_omega

theorem toNat_ofNat_lt {k : Nat} (hk : k < MAX_N) : (BitVec.ofNat 64 k).toNat = k := by
  simp only [BitVec.toNat_ofNat, MAX_N] at *; omega

theorem get_ofNat {α : Type} [Inhabited α] (v : Vector α MAX_N) {k : Nat} (hk : k < MAX_N) :
    Flat.get v (BitVec.ofNat 64 k) = v[k] := by
  rw [Flat.get_of_lt v (by rwa [toNat_ofNat_lt hk])]; simp only [toNat_ofNat_lt hk]

theorem put_ofNat {α : Type} (v : Vector α MAX_N) {k : Nat} (hk : k < MAX_N) (x : α) :
    Flat.put v (BitVec.ofNat 64 k) x = v.set k x hk := by
  rw [Flat.put_of_lt v (by rwa [toNat_ofNat_lt hk])]; simp only [toNat_ofNat_lt hk]

theorem NONE_toInt : Flat.NONE.toInt = -1 := by decide


/-! ## The array `dest` of the caller -/

section
variable {s : MachineData} {ra : Int64} {h : Hdr} {L : Loc} {t : MachineData} {k : Nat}

-- The bytes outside the frame hold their values of the entry.
theorem TS.get?_out (hs : TS s ra h L t) (hp : TopPre s) {b : Addr}
    (hb : ¬Mem.Blocks.Inside b 1 [frame topF s]) : t.dmem.get? b = s.dmem.get? b := by
  have := hp.rsp_le
  simp only [Mem.Blocks.Inside, or_false, topF_eq] at hb this
  rw [get?_R0 hs.mem (by unfold In topS; simp only [offLoc, offOps]; simp only [rsp] at *; bv_omega),
    MachineData.dmem_pushRa]
  exact Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj => by simp only [rsp] at *; bv_omega

-- `movq (r8,rax,8)` in `.LB.build_bottom_up.5`: `dest[k]` from the caller.
theorem TS.ld_dst (hs : TS s ra h L t) (ha : TA s t) (hp : TopPre s)
    (hax : t.regs.rax.toBitVec = BitVec.ofNat 64 k) (hk : k < mArg s) :
    t.dmem.loadInt (t.regs.r8.toBitVec + t.regs.rax.toBitVec * 8#64) 8
      = s.dmem.loadInt (wordAt (dstArg s) k) 8 := by
  have hg := hs.g
  have hd := (hp.mem hg).disj_frame
  rw [ha.r8, hax, show s.regs.r8.toBitVec + BitVec.ofNat 64 k * 8#64 = wordAt (dstArg s) k by
    simp only [wordAt, dstArg, Reg64s.get64_r8] at *; bv_omega]
  refine Mem.loadInt_congr fun i hi => hs.get?_out hp fun hf => hd _ hf ?_
  simp only [topOut, List.cons_append, Mem.Blocks.Inside, List.nil_append]
  right; right; right; left
  simp only [wordAt] at *; bv_omega


theorem TS.isSome_dst (hs : TS s ra h L t) (ha : TA s t) (hp : TopPre s)
    (hax : t.regs.rax.toBitVec = BitVec.ofNat 64 k) (hk : k < mArg s) :
    (t.dmem.loadInt (t.regs.r8.toBitVec + t.regs.rax.toBitVec * 8#64) 8).isSome = true := by
  have hg := hs.g
  rw [hs.ld_dst ha hp hax hk]
  refine (hp.mem hg).mapped.loadInt_isSome ?_
  simp only [topOut, topIn, List.cons_append, Mem.Blocks.Inside, List.nil_append]
  right; right; right; right; left
  simp only [wordAt] at *; bv_omega


theorem flatDest_get (hk : k < mArg s) (hn : mArg s ≤ MAX_N) :
    Flat.get (flatDest s) (BitVec.ofNat 64 k) = rd s.dmem (wordAt (dstArg s) k) := by
  rw [get_ofNat _ (by omega)]; simp [flatDest, hk]


theorem TS.rd_dst (hs : TS s ra h L t) (ha : TA s t) (hp : TopPre s)
    (hax : t.regs.rax.toBitVec = BitVec.ofNat 64 k) (hk : k < mArg s) :
    rd t.dmem (t.regs.r8.toBitVec + t.regs.rax.toBitVec * 8#64) = Flat.get (flatDest s) (BitVec.ofNat 64 k) := by
  have hg := hs.g
  rw [flatDest_get hk (by omega)]
  unfold rd; rw [hs.ld_dst ha hp hax hk]

-- A destination is less than `n`.
theorem dest_lt (hp : TopPre s) (hg : TopGuard s) (hk : k < mArg s) :
    (Flat.get (flatDest s) (BitVec.ofNat 64 k)).toNat < nArg s := by
  have hl : k < (topDests s).length := by
    have hlen : (flatDest s).toList.length = MAX_N := Vector.length_toList
    simp only [topDests, Flat.listDests, List.length_map, List.length_take]; omega
  have := (hp.mem hg).dests.1 k hl
  simp only [topDests, Flat.listDests, List.getElem_map, List.getElem_take, Vector.getElem_toList] at this
  rwa [get_ofNat _ (by omega)]

end

/-! ## The flags of the loops -/

-- `cmpq $-1, pos[k]; jne`.
theorem ne_none_of_jne {d : Word} (h : (!d - 18446744073709551615#64 == BitVec.zero 64) = true) :
    d ≠ Flat.NONE := by
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  intro hd; subst hd; exact h (by decide)

theorem none_of_jne {d : Word} (h : (!d - 18446744073709551615#64 == BitVec.zero 64) = false) :
    d = Flat.NONE := by
  simp only [Bool.not_eq_false', beq_iff_eq] at h
  have : d - 18446744073709551615#64 = 0#64 := h
  unfold Flat.NONE; bv_omega

-- `addq $1, rax; cmpq rax, rsi; jne` with `rax = k`.
theorem succ_lt_of_jne {a b r : Word} {k : Nat} (h : (!a - (1#64 + r) == BitVec.zero 64) = true)
    (ha : a = b) (hr : r = BitVec.ofNat 64 k) (hk : k < b.toNat) : k + 1 < b.toNat := by
  subst ha hr
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  have : a - (1#64 + BitVec.ofNat 64 k) ≠ 0#64 := h
  bv_omega

theorem succ_eq_of_jne {a b r : Word} {k : Nat} (h : (!a - (1#64 + r) == BitVec.zero 64) = false)
    (ha : a = b) (hr : r = BitVec.ofNat 64 k) (hk : k < b.toNat) : k + 1 = b.toNat := by
  subst ha hr
  simp only [Bool.not_eq_false', beq_iff_eq] at h
  have : a - (1#64 + BitVec.ofNat 64 k) = 0#64 := h
  bv_omega

-- `addq $1, rax; cmpq rdi, rax; jb` with `rax = k`.
theorem succ_lt_of_jb {a b r : Word} {k : Nat}
    (h : (((1#64 + r - a).toNat : Int) != ((1#64 + r).toNat : Int) - (a.toNat : Int)) = true)
    (ha : a = b) (hr : r = BitVec.ofNat 64 k) (hk : k < b.toNat) : k + 1 < b.toNat := by
  subst ha hr
  simp only [Idioms.cf_sub, decide_eq_true_eq] at h
  bv_omega

theorem succ_eq_of_jb {a b r : Word} {k : Nat}
    (h : (((1#64 + r - a).toNat : Int) != ((1#64 + r).toNat : Int) - (a.toNat : Int)) = false)
    (ha : a = b) (hr : r = BitVec.ofNat 64 k) (hk : k < b.toNat) : k + 1 = b.toNat := by
  subst ha hr
  simp only [Idioms.cf_sub, decide_eq_false_iff_not, Nat.not_lt] at h
  bv_omega

-- `addq $8, rax; cmpq rdx, rax; je` with `rax = S + 8k` and `rdx = S + 8n`.
theorem succ_eq_of_je {S a d : Addr} {k n : Nat} (h : (8#64 + a - d == BitVec.zero 64) = true)
    (ha : a = S + BitVec.ofNat 64 (8 * k)) (hd : d = S + BitVec.ofNat 64 (8 * n)) (hk : k < n)
    (hn : n ≤ MAX_N) : k + 1 = n := by
  subst ha hd
  simp only [beq_iff_eq] at h
  have : 8#64 + (S + BitVec.ofNat 64 (8 * k)) - (S + BitVec.ofNat 64 (8 * n)) = 0#64 := h
  simp only [MAX_N] at hn
  bv_omega

theorem succ_lt_of_je {S a d : Addr} {k n : Nat} (h : (8#64 + a - d == BitVec.zero 64) = false)
    (ha : a = S + BitVec.ofNat 64 (8 * k)) (hd : d = S + BitVec.ofNat 64 (8 * n)) (hk : k < n) :
    k + 1 < n := by
  subst ha hd
  simp only [beq_eq_false_iff_ne, ne_eq] at h
  have : 8#64 + (S + BitVec.ofNat 64 (8 * k)) - (S + BitVec.ofNat 64 (8 * n)) ≠ 0#64 := h
  bv_omega

/-! ## The struct after the loops when `m = 0` or `n = 0` -/

section
variable (s : MachineData) (ra : Int64)

theorem Dm_m0 (hm : mArg s = 0) : Dm s ra = (hdr0 s ra).dest := by
  simp only [Dm, hm, Flat.bindDest_zero]

theorem Pm_m0 (hm : mArg s = 0) : Pm s ra = Pn s ra := by
  simp only [Pm, hm, Flat.bindPos_zero]

theorem Pn_n0 (hn : nArg s = 0) : Pn s ra = (hdr0 s ra).pos := by
  simp only [Pn, hn, Flat.clearPos_zero]

end

/-! ## The tests of `m` and `n` -/

section
variable {s t : MachineData}

-- `testq rdi, rdi` and `testq rsi, rsi` with the argument registers.
theorem TA.m0 (ha : TA s t)
    (hf : (t.regs.rdi.toBitVec &&& t.regs.rdi.toBitVec == BitVec.zero 64) = true) : mArg s = 0 := by
  rw [ha.rdi] at hf; exact zero_of_test hf

theorem TA.m_pos (ha : TA s t)
    (hf : (t.regs.rdi.toBitVec &&& t.regs.rdi.toBitVec == BitVec.zero 64) = false) : 0 < mArg s := by
  rw [ha.rdi] at hf; exact pos_of_test hf

theorem TA.n0 (ha : TA s t)
    (hf : (t.regs.rsi.toBitVec &&& t.regs.rsi.toBitVec == BitVec.zero 64) = true) : nArg s = 0 := by
  rw [ha.rsi] at hf; exact zero_of_test hf

theorem TA.n_pos (ha : TA s t)
    (hf : (t.regs.rsi.toBitVec &&& t.regs.rsi.toBitVec == BitVec.zero 64) = false) : 0 < nArg s := by
  rw [ha.rsi] at hf; exact pos_of_test hf

end

section
variable {s : MachineData} {ra : Int64} {k : Nat}

theorem Pn_succ (he : k + 1 = nArg s) : Flat.clearPos (k + 1) (hdr0 s ra).pos = Pn s ra := by
  rw [he]; rfl

theorem Dm_succ (he : k + 1 = mArg s) : Flat.bindDest (flatDest s) (k + 1) (hdr0 s ra).dest = Dm s ra := by
  rw [he]; rfl

theorem Pm_succ (he : k + 1 = mArg s) : Flat.bindPos (flatDest s) (k + 1) (Pn s ra) = Pm s ra := by
  rw [he]; rfl

theorem countNone_n (he : k + 1 = nArg s) (P : Vector Word MAX_N) :
    Flat.countNone P (k + 1) 0#64 = Flat.countNone P (nArg s) 0#64 := by
  rw [he]

end

/-! ## The glue of the loop blocks -/

section
variable {k : Nat}

-- `addq $1, rax` with `rax = k`.
theorem succ_ofNat {r : Word} (hr : r = BitVec.ofNat 64 k) : 1#64 + r = BitVec.ofNat 64 (k + 1) := by
  subst hr
  bv_omega

-- The variant of a loop with `addq $1, rax` and the bound `a`.
theorem sub_succ_lt {a r : Word} (hr : r = BitVec.ofNat 64 k) (hk : k + 1 < a.toNat) :
    (a - (1#64 + r)).toNat < (a - r).toNat := by
  subst hr
  bv_omega

-- `movq rsp, rax; leaq (rax, rsi, 8), rdx` in `.LB.build_bottom_up.5`.

-- `addq $8, rax` with `rax = S + 8k`.
theorem add8 {S a : Addr} (ha : a = S + BitVec.ofNat 64 (8 * k)) :
    8#64 + a = S + BitVec.ofNat 64 (8 * (k + 1)) := by
  subst ha
  bv_omega

-- The variant of a loop with `addq $8, rax` and the bound `d`.
theorem sub8_add {S a d : Addr} {k n : Nat} (ha : a = S + BitVec.ofNat 64 (8 * k))
    (hd : d = S + BitVec.ofNat 64 (8 * n)) (hk : k + 1 < n) (hn : n ≤ MAX_N) :
    (d - (8#64 + a)).toNat + 8 = (d - a).toNat := by
  subst ha hd
  simp only [MAX_N] at hn
  bv_omega

theorem sub8_lt {S a d : Addr} {k n : Nat} (ha : a = S + BitVec.ofNat 64 (8 * k))
    (hd : d = S + BitVec.ofNat 64 (8 * n)) (hk : k + 1 < n) (hn : n ≤ MAX_N) :
    (d - (8#64 + a)).toNat < (d - a).toNat := by
  have := sub8_add ha hd hk hn; omega

end
end Top

end Bbu.Unit
