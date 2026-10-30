import BbuKraken.Unit.SpillDefs
import BbuKraken.Sep.Stores
import BbuKraken.Unit.ProduceLemmas
import BbuKraken.Unit.ShallowestCopy

/-!
# Lemmas for the `spill_set` unit proof

`spill_set` pushes 6 registers and subtracts 24 from `rsp`. With `sp = rsp s` (the state at the
call), the stack is:

- `sp - 8`: the return address; `sp - 16` to `sp - 56`: `r15`, `r14`, `r13`, `r12`, `rbp`, `rbx`;
- `sp - 64` (`16(%rsp)`): the `SpillSet` object `o`, that holds the pointer `spilled`;
- `sp - 72` (`8(%rsp)`): a word that the body does not use;
- `sp - 80` (`(%rsp)`): `spilled` (`rsi s`);
- `sp - 88`: the return slot `y` of `SpillSet::add`.

`Sb` is the state between the pushes and the pops. `SpillSet::add` gets the object at `sp - 64`,
the bytes, a stack with no free word and the frame `Fr`.
-/

namespace Bbu.Unit.SpillSetProof

open Bbu.Sep
open Bbu.Unit.ProduceProof (st_at isSome_at)

/-! ## The stack frame -/

-- The 10 free words and the return slot as word atoms.
theorem stk10 (sp : Addr) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 v : Word) :
    Stk sp [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] v
      = Wd (sp - 88#64) x0 ∗ Wd (sp - 80#64) x1 ∗ Wd (sp - 72#64) x2 ∗ Wd (sp - 64#64) x3
        ∗ Wd (sp - 56#64) x4 ∗ Wd (sp - 48#64) x5 ∗ Wd (sp - 40#64) x6 ∗ Wd (sp - 32#64) x7
        ∗ Wd (sp - 24#64) x8 ∗ Wd (sp - 16#64) x9 ∗ Wd (sp - 8#64) v := by
  unfold Stk
  simp only [Arr, List.length_cons, List.length_nil, MProp.sep_emp, MProp.sep_assoc]
  rw [show sp - 8#64 - BitVec.ofNat 64 (8 * (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
        = sp - 88#64 by bv_omega,
    show sp - 88#64 + 8#64 = sp - 80#64 by bv_omega,
    show sp - 80#64 + 8#64 = sp - 72#64 by bv_omega,
    show sp - 72#64 + 8#64 = sp - 64#64 by bv_omega,
    show sp - 64#64 + 8#64 = sp - 56#64 by bv_omega,
    show sp - 56#64 + 8#64 = sp - 48#64 by bv_omega,
    show sp - 48#64 + 8#64 = sp - 40#64 by bv_omega,
    show sp - 40#64 + 8#64 = sp - 32#64 by bv_omega,
    show sp - 32#64 + 8#64 = sp - 24#64 by bv_omega,
    show sp - 24#64 + 8#64 = sp - 16#64 by bv_omega]

-- The stack of `SpillSet::add`: no free word, the return slot at `sp - 88`.
theorem stk0 (sp q : Addr) (hq : q = sp - 80#64) (y : Word) : Stk q [] y = Wd (sp - 88#64) y := by
  unfold Stk
  simp only [Arr, MProp.emp_sep]
  rw [show q - 8#64 = sp - 88#64 by subst hq; bv_omega]

theorem split10 {fr : List Word} (h : fr.length = 10) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, fr = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] :=
  match fr, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9], _ => ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, rfl⟩

-- The memory of the arguments: the bytes `f`, the words of `adds` and `queries`, the bytes `res`
-- at `r`, the word `r` at `rsp` and `F`.
def Rest (s : MachineData) (adds queries : List Word) (r : Addr) (F : MProp 64)
    (f : BitVec 32 → BitVec 8) (res : List (BitVec 8)) : MProp 64 :=
  Spl (rsi s) f (List.range (Flat.ids (rdi s))) ∗ Arr (rdx s) adds ∗ Arr (r8 s) queries
    ∗ Bs r res ∗ Wd (rsp s) r ∗ F

-- The frame of `SpillSet::add`: the words of the stack of `spill_set` above `16(%rsp)` and
-- below it, the return address, and the arguments without the bytes.
def Fr (s : MachineData) (ra : Int64) (x2 : Word) (adds queries : List Word) (r : Addr)
    (F : MProp 64) (res : List (BitVec 8)) : MProp 64 :=
  Wd (rsp s - 80#64) (rsi s) ∗ Wd (rsp s - 72#64) x2 ∗ Wd (rsp s - 56#64) s.regs.rbx.toBitVec
    ∗ Wd (rsp s - 48#64) s.regs.rbp.toBitVec ∗ Wd (rsp s - 40#64) s.regs.r12.toBitVec
    ∗ Wd (rsp s - 32#64) s.regs.r13.toBitVec ∗ Wd (rsp s - 24#64) s.regs.r14.toBitVec
    ∗ Wd (rsp s - 16#64) s.regs.r15.toBitVec ∗ Wd (rsp s - 8#64) ra.toBitVec
    ∗ Arr (rdx s) adds ∗ Arr (r8 s) queries ∗ Bs r res ∗ Wd (rsp s) r ∗ F

-- The memory of the body.
def Mb (s : MachineData) (ra : Int64) (adds queries : List Word) (r : Addr) (F : MProp 64)
    (f : BitVec 32 → BitVec 8) (res : List (BitVec 8)) (y o x2 : Word) : MProp 64 :=
  Wd (rsp s - 64#64) o ∗ Spl (rsi s) f (List.range (Flat.ids (rdi s)))
    ∗ Stk (rsp s - 80#64) [] y ∗ Fr s ra x2 adds queries r F res

-- The free words of the body.
def frm (s : MachineData) (y o x2 : Word) : List Word :=
  [y, rsi s, x2, o, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
    s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]

theorem mb_eq (s : MachineData) (ra : Int64) (adds queries : List Word) (r : Addr) (F : MProp 64)
    (f : BitVec 32 → BitVec 8) (res : List (BitVec 8)) (y o x2 : Word) :
    Mb s ra adds queries r F f res y o x2
      = Stk (rsp s) (frm s y o x2) ra.toBitVec ∗ Rest s adds queries r F f res := by
  unfold Mb Fr Rest frm
  rw [stk10, stk0 (rsp s) _ rfl]
  ecancel

/-! ## The body state -/

-- A state between the pushes and the pops: `rbp`, `r12` and `r13` are `queries`, `addCount`
-- and `queryCount`.
structure Sb (s : MachineData) (ra : Int64) (adds queries : List Word) (r : Addr) (F : MProp 64)
    (f : BitVec 32 → BitVec 8) (res : List (BitVec 8)) (y o x2 : Word) (t : MachineData) :
    Prop where
  mem : (Mb s ra adds queries r F f res y o x2).get t.dmem
  sp : t.regs.rsp.toBitVec = rsp s - 80#64
  bp : t.regs.rbp.toBitVec = r8 s
  r12 : t.regs.r12.toBitVec = rcx s
  r13 : t.regs.r13.toBitVec = r9 s

section
variable {s : MachineData} {ra : Int64} {adds queries : List Word} {r : Addr} {F : MProp 64}
  {f : BitVec 32 → BitVec 8} {res : List (BitVec 8)} {y o x2 : Word}

theorem Sb.step {t P : MachineData} {f' : BitVec 32 → BitVec 8} {res' : List (BitVec 8)}
    {y' o' x2' : Word} (h : Sb s ra adds queries r F f res y o x2 t)
    (hm : (Mb s ra adds queries r F f' res' y' o' x2').get P.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) (hbp : P.regs.rbp = t.regs.rbp)
    (h12 : P.regs.r12 = t.regs.r12) (h13 : P.regs.r13 = t.regs.r13) :
    Sb s ra adds queries r F f' res' y' o' x2' P :=
  ⟨hm, by rw [hsp]; exact h.sp, by rw [hbp]; exact h.bp, by rw [h12]; exact h.r12,
    by rw [h13]; exact h.r13⟩

theorem Sb.next {t P : MachineData} (h : Sb s ra adds queries r F f res y o x2 t)
    (hm : P.dmem = t.dmem) (hsp : P.regs.rsp = t.regs.rsp) (hbp : P.regs.rbp = t.regs.rbp)
    (h12 : P.regs.r12 = t.regs.r12) (h13 : P.regs.r13 = t.regs.r13) :
    Sb s ra adds queries r F f res y o x2 P :=
  h.step (hm ▸ h.mem) hsp hbp h12 h13

theorem Sb.stack {t : MachineData} (h : Sb s ra adds queries r F f res y o x2 t) :
    t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    rw [Reg64s.get64_rsp, Reg64s.get64_rsp, h.sp]
    simp only [MachineData.pushRa, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp]
    bv_omega)

end

theorem setMem_eq (s : MachineData) (f : BitVec 32 → BitVec 8) (adds queries : List Word)
    (r : Addr) (res : List (BitVec 8)) (F : MProp 64) (fr : List Word) (v : Word) :
    SetMem s f adds queries r res F fr v = Stk (rsp s) fr v ∗ Rest s adds queries r F f res := by
  unfold SetMem Rest; ecancel

/-! ## The pushes and the pops -/

-- A memory fact with the atoms in another order.
theorem get_eq {P Q : MProp 64} {m : Mem 64} (h : P.get m) (e : P = Q) : Q.get m := e ▸ h

section
variable {s : MachineData} {ra : Int64} {adds queries : List Word} {r : Addr} {F : MProp 64}
  {f : BitVec 32 → BitVec 8} {res : List (BitVec 8)}

-- The 6 `pushq`, `subq $24, %rsp` and `movq %rsi, (%rsp)` from the entry stack (`q` is `rsp`
-- after the call): the loads before the stores, and the memory after them.
theorem pushes {m m1 m2 m3 m4 m5 m6 m7 : Mem 64} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Word}
    (hm : (Stk (rsp s) [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] ra.toBitVec
      ∗ Rest s adds queries r F f res).get m)
    {q a b c d e k z : Word} (hq : q = rsp s - 8#64) (ha : a = s.regs.r15.toBitVec)
    (hb : b = s.regs.r14.toBitVec) (hc : c = s.regs.r13.toBitVec) (hd : d = s.regs.r12.toBitVec)
    (he : e = s.regs.rbp.toBitVec) (hk : k = s.regs.rbx.toBitVec) (hz : z = rsi s)
    (h1 : m1 = m.storeInt (q - 8#64) 8 a.toInt)
    (h2 : m2 = m1.storeInt (q - 8#64 - 8#64) 8 b.toInt)
    (h3 : m3 = m2.storeInt (q - 8#64 - 8#64 - 8#64) 8 c.toInt)
    (h4 : m4 = m3.storeInt (q - 8#64 - 8#64 - 8#64 - 8#64) 8 d.toInt)
    (h5 : m5 = m4.storeInt (q - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 e.toInt)
    (h6 : m6 = m5.storeInt (q - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 k.toInt)
    (h7 : m7 = m6.storeInt (q - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 24#64) 8 z.toInt) :
    (m.loadInt (q - 8#64) 8).isSome = true
    ∧ (m1.loadInt (q - 8#64 - 8#64) 8).isSome = true
    ∧ (m2.loadInt (q - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ (m3.loadInt (q - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ (m4.loadInt (q - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ (m5.loadInt (q - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ (m6.loadInt (q - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 24#64) 8).isSome = true
    ∧ (Mb s ra adds queries r F f res x0 x3 x2).get m7 := by
  subst hq ha hb hc hd he hk hz h1 h2 h3 h4 h5 h6 h7
  rw [stk10] at hm
  rw [show rsp s - 8#64 - 8#64 = rsp s - 16#64 by bv_omega,
    show rsp s - 16#64 - 8#64 = rsp s - 24#64 by bv_omega,
    show rsp s - 24#64 - 8#64 = rsp s - 32#64 by bv_omega,
    show rsp s - 32#64 - 8#64 = rsp s - 40#64 by bv_omega,
    show rsp s - 40#64 - 8#64 = rsp s - 48#64 by bv_omega,
    show rsp s - 48#64 - 8#64 = rsp s - 56#64 by bv_omega,
    show rsp s - 56#64 - 24#64 = rsp s - 80#64 by bv_omega]
  have h1 := st_at (rsp s - 16#64) x9 hm (by ecancel) s.regs.r15.toBitVec
  have h2 := st_at (rsp s - 24#64) x8 h1 (by ecancel) s.regs.r14.toBitVec
  have h3 := st_at (rsp s - 32#64) x7 h2 (by ecancel) s.regs.r13.toBitVec
  have h4 := st_at (rsp s - 40#64) x6 h3 (by ecancel) s.regs.r12.toBitVec
  have h5 := st_at (rsp s - 48#64) x5 h4 (by ecancel) s.regs.rbp.toBitVec
  have h6 := st_at (rsp s - 56#64) x4 h5 (by ecancel) s.regs.rbx.toBitVec
  have h7 := st_at (rsp s - 80#64) x1 h6 (by ecancel) (rsi s)
  refine ⟨isSome_at _ x9 hm (by ecancel), isSome_at _ x8 h1 (by ecancel),
    isSome_at _ x7 h2 (by ecancel), isSome_at _ x6 h3 (by ecancel), isSome_at _ x5 h4 (by ecancel),
    isSome_at _ x4 h5 (by ecancel), isSome_at _ x1 h6 (by ecancel), ?_⟩
  unfold Mb Fr Rest at *
  rw [stk0 (rsp s) _ rfl]
  exact get_eq h7 (by ecancel)

-- The 6 `popq` read the words of `Fr` above `24(%rsp)`.
theorem Sb.isSome_pops {y o x2 : Word} {t : MachineData}
    (h : Sb s ra adds queries r F f res y o x2 t) :
    (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec) 8).isSome = true
    ∧ (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (24#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8).isSome
      = true := by
  have hm := h.mem
  unfold Mb at hm
  rw [h.sp, show 24#64 + (rsp s - 80#64) = rsp s - 56#64 by bv_omega,
    show rsp s - 56#64 + 8#64 = rsp s - 48#64 by bv_omega,
    show rsp s - 48#64 + 8#64 = rsp s - 40#64 by bv_omega,
    show rsp s - 40#64 + 8#64 = rsp s - 32#64 by bv_omega,
    show rsp s - 32#64 + 8#64 = rsp s - 24#64 by bv_omega,
    show rsp s - 24#64 + 8#64 = rsp s - 16#64 by bv_omega]
  exact ⟨isSome_of_eq _ hm (by unfold Fr; ecancel), isSome_of_eq _ hm (by unfold Fr; ecancel),
    isSome_of_eq _ hm (by unfold Fr; ecancel), isSome_of_eq _ hm (by unfold Fr; ecancel),
    isSome_of_eq _ hm (by unfold Fr; ecancel), isSome_of_eq _ hm (by unfold Fr; ecancel)⟩

-- `addq $24, %rsp` and the 6 `popq`: the state `P` before the `ret` is a `Kg` state.
theorem Sb.pop {y o x2 : Word} {t P : MachineData} (h : Sb s ra adds queries r F f res y o x2 t)
    (hm : P.dmem = t.dmem)
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
    Kg (Rest s adds queries r F f res) s ra (frm s y o x2) P := by
  have hmem := h.mem
  have hmb := h.mem
  unfold Mb at hmem
  have a1 : 24#64 + (rsp s - 80#64) = rsp s - 56#64 := by bv_omega
  have a2 : rsp s - 56#64 + 8#64 = rsp s - 48#64 := by bv_omega
  have a3 : rsp s - 48#64 + 8#64 = rsp s - 40#64 := by bv_omega
  have a4 : rsp s - 40#64 + 8#64 = rsp s - 32#64 := by bv_omega
  have a5 : rsp s - 32#64 + 8#64 = rsp s - 24#64 := by bv_omega
  have a6 : rsp s - 24#64 + 8#64 = rsp s - 16#64 := by bv_omega
  have a7 : rsp s - 16#64 + 8#64 = rsp s - 8#64 := by bv_omega
  simp only [h.sp, a1, a2, a3, a4, a5, a6, a7] at hsp hbx hbp h12 h13 h14 h15
  refine ⟨by rw [hm, ← mb_eq]; exact hmb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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


-- The post at `ret`: `rax` and the memory of a state `t` at `.LB244` with the result `hres`.
theorem Sb.post {f₀ : BitVec 32 → BitVec 8} {res₀ : List (BitVec 8)} {y o x2 : Word}
    {t t' : MachineData} (h : Sb s ra adds queries r F f res y o x2 t)
    (hres : setRes s f₀ adds queries res₀ = (rax t, f, res)) (hm : t'.dmem = t.dmem)
    (hax : rax t' = rax t) : SetPost f₀ adds queries r res₀ F s t' := by
  refine ⟨by rw [hres, hax], frm s y o x2, ra.toBitVec, rfl, ?_⟩
  rw [hres, setMem_eq, ← mb_eq, hm]
  exact h.mem
end


/-! ## The variant -/

-- The variant of the CFG proof: `na` and `nq` are `addCount` and `queryCount`. The four loops
-- run in order, so each loop has a band of `4 * 2 ^ 64` above the bands of the loops after it.
def var (na nq : Nat) (l : String) (t : MachineData) : Nat :=
  if l = "spill_set" then 7 * (4 * 2 ^ 64)
  else if l = ".LB245" then 6 * (4 * 2 ^ 64)
  else if l = ".LB248" then 5 * (4 * 2 ^ 64) + 2 * (na - (rax t).toNat) + 1
  else if l = ".LB246" then 5 * (4 * 2 ^ 64) + 2 * (na - (rax t).toNat)
  else if l = ".LB272" then 5 * (4 * 2 ^ 64) - 1
  else if l = ".LB251" then 4 * (4 * 2 ^ 64) + 2 * (nq - (rax t).toNat) + 1
  else if l = ".LB250" then 4 * (4 * 2 ^ 64) + 2 * (nq - (rax t).toNat)
  else if l = ".LB273" then 4 * (4 * 2 ^ 64) - 1
  else if l = ".LB257" then 3 * (4 * 2 ^ 64) + 2 ^ 64 + 1
  else if l = ".LB253" then 3 * (4 * 2 ^ 64) + (na - t.regs.r14.toBitVec.toNat)
  else if l = ".LB252" then 2 * (4 * 2 ^ 64) + 2 * 2 ^ 64 + 2
  else if l = ".LB255" then 2 * (4 * 2 ^ 64) + 2 * (nq - (rax t).toNat) + 1
  else if l = ".LB254" then 2 * (4 * 2 ^ 64) + 2 * (nq - (rax t).toNat)
  else if l = ".LB274" ∨ l = ".LB262" then 1
  else 0

/-! ## The model -/

-- The result byte of the query `q`.
def g (f : BitVec 32 → BitVec 8) (q : StackSlot) : BitVec 8 :=
  Flat.boolByte (Flat.spillIsSpilled f q)
end Bbu.Unit.SpillSetProof
