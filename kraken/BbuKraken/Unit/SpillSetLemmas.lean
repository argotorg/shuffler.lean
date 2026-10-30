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

-- The stack goal of a jump from a state `P` with the `rsp` of `t`.
theorem Sb.stack' {t P : MachineData} (h : Sb s ra adds queries r F f res y o x2 t)
    (hsp : P.regs.rsp = t.regs.rsp) : P.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    rw [Reg64s.get64_rsp, Reg64s.get64_rsp, hsp, h.sp]
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


-- The post at `ret`: `rax` and the memory of a state `t` at `.LB.spill_set.12` with the result `hres`.
theorem Sb.post {f₀ : BitVec 32 → BitVec 8} {res₀ : List (BitVec 8)} {y o x2 : Word}
    {t t' : MachineData} (h : Sb s ra adds queries r F f res y o x2 t)
    (hres : setRes s f₀ adds queries res₀ = (rax t, f, res)) (hm : t'.dmem = t.dmem)
    (hax : rax t' = rax t) : SetPost f₀ adds queries r res₀ F s t' := by
  refine ⟨by rw [hres, hax], frm s y o x2, ra.toBitVec, rfl, ?_⟩
  rw [hres, setMem_eq, ← mb_eq, hm]
  exact h.mem
end


/-! ## The words of `adds` and `queries` -/

-- A copy of `SwapWith.B32.rd32`: the `movl` load of a 4-byte atom.
theorem rd32_b32 {m : Mem 64} {a : Addr} {v : BitVec 32} {F : MProp 64}
    (h : (B32 a v ∗ F).get m) : BitVec.ofInt 32 (m.loadInt a 4).get! = v := by
  unfold B32 at h
  simp only [Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.get!_some,
    BitVec.ofInt_ofBytes_toBytes 32 4 rfl]

section
variable {m : Mem 64} {a : Addr} {vs : List Word} {P : MProp 64} {x : Word}

theorem arr_wd (h : (Arr a vs ∗ P).get m) (hx : x.toNat < vs.length) :
    ∃ R, (Wd (a + x * 8#64) vs[x.toNat] ∗ R).get m := by
  obtain ⟨R, e⟩ := Arr.focus a vs hx
  rw [e, MProp.sep_assoc] at h
  exact ⟨_, by rw [fold_slot]; exact h⟩

-- `cmpb $0, 5(%b,%x,8)`: byte 5 of word `x` is the opcode.
theorem arr_op (h : (Arr a vs ∗ P).get m) (hx : x.toNat < vs.length) :
    (m.loadInt (a + x * 8#64 + 5#64) 1).isSome = true
      ∧ BitVec.ofInt 8 (m.loadInt (a + x * 8#64 + 5#64) 1).get!
        = (StackSlot.ofWord vs[x.toNat]).valueOpcode := by
  obtain ⟨R, h⟩ := arr_wd h hx
  exact ⟨Wd.isSome_byte h (j := 5) (by omega), Wd.rdb_byte h (j := 5) (by omega)⟩

-- `cmpb $0, 4(%b,%x,8)`: byte 4 of word `x` is the kind.
theorem arr_kind (h : (Arr a vs ∗ P).get m) (hx : x.toNat < vs.length) :
    (m.loadInt (a + x * 8#64 + 4#64) 1).isSome = true
      ∧ BitVec.ofInt 8 (m.loadInt (a + x * 8#64 + 4#64) 1).get!
        = (StackSlot.ofWord vs[x.toNat]).kind := by
  obtain ⟨R, h⟩ := arr_wd h hx
  exact ⟨Wd.isSome_byte h (j := 4) (by omega), Wd.rdb_byte h (j := 4) (by omega)⟩

-- `movl (%b,%x,8), %r32`: the low 4 bytes of word `x` are the payload.
theorem arr_pay (h : (Arr a vs ∗ P).get m) (hx : x.toNat < vs.length) :
    (m.loadInt (a + x * 8#64) 4).isSome = true
      ∧ BitVec.ofInt 32 (m.loadInt (a + x * 8#64) 4).get!
        = (StackSlot.ofWord vs[x.toNat]).payload := by
  obtain ⟨R, h⟩ := arr_wd h hx
  rw [Wd.split, MProp.sep_assoc] at h
  exact ⟨B32.isSome h, rd32_b32 h⟩
end

section
variable {s : MachineData} {ra : Int64} {adds queries : List Word} {r : Addr} {F : MProp 64}
  {f : BitVec 32 → BitVec 8} {res : List (BitVec 8)} {y o x2 : Word} {t : MachineData}

theorem Sb.addsArr (h : Sb s ra adds queries r F f res y o x2 t) :
    ∃ R, (Arr (rdx s) adds ∗ R).get t.dmem :=
  ⟨_, get_eq h.mem (by unfold Mb Fr; ecancel)⟩

theorem Sb.queriesArr (h : Sb s ra adds queries r F f res y o x2 t) :
    ∃ R, (Arr (r8 s) queries ∗ R).get t.dmem :=
  ⟨_, get_eq h.mem (by unfold Mb Fr; ecancel)⟩
end

/-! ## The bytes of `results` -/

-- The byte `i`, and the bytes after a store to it, with the same rest.
theorem Bs.focus (a : Addr) (bs : List (BitVec 8)) {i : Nat} (hi : i < bs.length)
    (v : BitVec 8) :
    ∃ R, Bs a bs = B8 (a + BitVec.ofNat 64 i) bs[i] ∗ R
      ∧ Bs a (bs.set i v) = B8 (a + BitVec.ofNat 64 i) v ∗ R := by
  induction bs generalizing a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons b bs ih =>
    cases i with
    | zero => exact ⟨Bs (a + 1#64) bs, by simp [Bs], by simp [Bs]⟩
    | succ i =>
      obtain ⟨R, e1, e2⟩ := ih (a + 1#64) (i := i) (by simpa using hi)
      have ha : a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by bv_omega
      refine ⟨B8 a b ∗ R, ?_, ?_⟩
      · simp only [Bs, List.getElem_cons_succ]; rw [e1, ha, sep_lc]
      · simp only [Bs, List.set_cons_succ]; rw [e2, ha, sep_lc]

section
variable {a : Addr} {bs : List (BitVec 8)} {F : MProp 64} {m : Mem 64} {x : Word}

theorem Bs.isSome (h : (Bs a bs ∗ F).get m) (hx : x.toNat < bs.length) :
    (m.loadInt (a + x) 1).isSome = true := by
  obtain ⟨R, e1, -⟩ := Bs.focus a bs hx 0#8
  rw [e1, MProp.sep_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact B8.isSome h

theorem Bs.store (h : (Bs a bs ∗ F).get m) (hx : x.toNat < bs.length) (z : Int) :
    (Bs a (bs.set x.toNat (BitVec.ofInt 8 z)) ∗ F).get (m.storeInt (a + x) 1 z) := by
  obtain ⟨R, e1, e2⟩ := Bs.focus a bs hx (BitVec.ofInt 8 z)
  rw [e1, MProp.sep_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  rw [e2, MProp.sep_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact B8.store h z
end

/-! ## The stack words, the stores and the call -/

section
variable {s : MachineData} {ra : Int64} {adds queries : List Word} {r : Addr} {F : MProp 64}
  {f : BitVec 32 → BitVec 8} {res : List (BitVec 8)} {y o x2 : Word} {t : MachineData}

-- `movq (%rsp), %r`: the word `spilled`.
theorem Sb.ld_sp (h : Sb s ra adds queries r F f res y o x2 t) :
    (t.dmem.loadInt t.regs.rsp.toBitVec 8).isSome = true
      ∧ rd t.dmem t.regs.rsp.toBitVec = rsi s := by
  have hm := h.mem
  unfold Mb at hm
  rw [h.sp]
  exact ⟨isSome_of_eq _ hm (by unfold Fr; ecancel), rd_of_eq hm (by unfold Fr; ecancel)⟩

-- `movq 80(%rsp), %r`: the word `results`.
theorem Sb.ld_res (h : Sb s ra adds queries r F f res y o x2 t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 80#64) 8).isSome = true
      ∧ rd t.dmem (t.regs.rsp.toBitVec + 80#64) = r := by
  have hm := h.mem
  unfold Mb at hm
  rw [h.sp, show rsp s - 80#64 + 80#64 = rsp s by bv_omega]
  exact ⟨isSome_of_eq _ hm (by unfold Fr; ecancel), rd_of_eq hm (by unfold Fr; ecancel)⟩

theorem Sb.isSome_o (h : Sb s ra adds queries r F f res y o x2 t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 16#64) 8).isSome = true := by
  have hm := h.mem
  unfold Mb at hm
  rw [h.sp, show rsp s - 80#64 + 16#64 = rsp s - 64#64 by bv_omega]
  exact Wd.isSome hm

-- `movq (%rsp), %rax; movq %rax, 16(%rsp)`: the object holds `spilled`.
theorem Sb.st_o {P : MachineData} (h : Sb s ra adds queries r F f res y o x2 t)
    (hm : P.dmem
      = t.dmem.storeInt (t.regs.rsp.toBitVec + 16#64) 8 (rd t.dmem t.regs.rsp.toBitVec).toInt)
    (hsp : P.regs.rsp = t.regs.rsp) (hbp : P.regs.rbp = t.regs.rbp)
    (h12 : P.regs.r12 = t.regs.r12) (h13 : P.regs.r13 = t.regs.r13) :
    Sb s ra adds queries r F f res y (rsi s) x2 P := by
  have hmem := h.mem
  unfold Mb at hmem
  refine h.step ?_ hsp hbp h12 h13
  rw [hm, h.ld_sp.2, h.sp, show rsp s - 80#64 + 16#64 = rsp s - 64#64 by bv_omega]
  unfold Mb
  exact Wd.store hmem (rsi s)

theorem Sb.isSome_res (h : Sb s ra adds queries r F f res y o x2 t) {x : Word}
    (hx : x.toNat < res.length) : (t.dmem.loadInt (r + x) 1).isSome = true :=
  Bs.isSome (get_eq h.mem (by unfold Mb Fr; ecancel)) hx

-- `movb %dl, (%rcx,%rax)`: the byte `x` of `results`.
theorem Sb.st_res {P : MachineData} (h : Sb s ra adds queries r F f res y o x2 t) {x : Word}
    (hx : x.toNat < res.length) (z : Int) (hm : P.dmem = t.dmem.storeInt (r + x) 1 z)
    {res' : List (BitVec 8)} (e : res.set x.toNat (BitVec.ofInt 8 z) = res')
    (hsp : P.regs.rsp = t.regs.rsp) (hbp : P.regs.rbp = t.regs.rbp)
    (h12 : P.regs.r12 = t.regs.r12) (h13 : P.regs.r13 = t.regs.r13) :
    Sb s ra adds queries r F f res' y o x2 P := by
  subst e
  refine h.step ?_ hsp hbp h12 h13
  rw [hm]
  exact get_eq (Bs.store (get_eq h.mem (by unfold Mb Fr; ecancel)) hx z) (by unfold Mb Fr; ecancel)

-- The byte of the id `i` of `spilled`.
theorem Sb.isSome_spl (h : Sb s ra adds queries r F f res y o x2 t) {i : Nat}
    (hi : i < Flat.ids (rdi s)) : (t.dmem.loadInt (rsi s + BitVec.ofNat 64 i) 1).isSome = true :=
  Spl.isSome (get_eq h.mem (by unfold Mb; ecancel)) (List.mem_range.mpr hi)

theorem Sb.rdb_spl (h : Sb s ra adds queries r F f res y o x2 t) {i : Nat}
    (hi : i < Flat.ids (rdi s)) : rdb t.dmem (rsi s + BitVec.ofNat 64 i) = f (BitVec.ofNat 32 i) :=
  Spl.rdb (get_eq h.mem (by unfold Mb; ecancel)) (List.mem_range.mpr hi)

-- `call SpillSet::add` in a state `c` with the object in `rdi` and the slot `w` in `rsi`: the
-- callee gets the object, the bytes and the frame `Fr`, and keeps `rsp`, `rbp`, `r12` and `r13`.
theorem Sb.call {c : MachineData} {K : MachineData → Prop} {w : Word}
    (h : Sb s ra adds queries r F f res y (rsi s) x2 c) (hdi : rdi c = rsp s - 64#64)
    (hw : rsi c = w)
    (hlt : Flat.isVariable (StackSlot.ofWord w) = true →
      (StackSlot.ofWord w).payload.toNat < Flat.ids (rdi s))
    (hK : ∀ t v, Sb s ra adds queries r F (Flat.spillAdd f (StackSlot.ofWord w)).2 res v
        (rsi s) x2 t → al t = code (Flat.spillAdd f (StackSlot.ofWord w)).1
        → Sep.mod.Agree c t → K t) :
    ∃ p S f' n F', AddPre p S f' n F' c
      ∧ ∀ s', AddPost p S f' n F' c s' → Sep.mod.Agree c s' → K s' := by
  subst hw
  refine ⟨rsp s - 64#64, rsi s, f, Flat.ids (rdi s), Fr s ra x2 adds queries r F res,
    ⟨hdi, Nat.min_le_right _ _, hlt, ⟨y, ?_⟩⟩, fun s' hpost hag => ?_⟩
  · have hm := h.mem
    unfold Mb at hm
    simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm
  · obtain ⟨hal, v, hm⟩ := hpost
    refine hK s' v ⟨?_, ?_, ?_, ?_, ?_⟩ hal hag
    · unfold Mb
      simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]; exact h.bp
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact h.r12
    · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13]; exact h.r13
end

/-! ## Specs for two instruction forms

`kvcgen64` has no spec for `movl disp(%b, %i, 8), %r32` and for `andb %r8, %r8`. The proofs are
the proofs of `mov_load_reg32_spec`/`mov_load_idx8_spec` and of `or_reg8_reg8_spec`. -/

section
open Std.WP Lean.Order
open scoped Program.WP
variable [Host] [FunDecls] {Q : PUnit → MachineData → Prop} {E : Int64 → MachineData → Prop}

-- `movl disp(%b, %i, 8), %r32`: the write clears the upper half.
theorem movl_idx8_spec (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8#64 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 4).isSome = true
        ∧ Q () { s with
            regs := s.regs.set64 rd ((BitVec.ofInt 32 (Mem.loadInt s.dmem a 4).get!).zeroExtend 64) } ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low rd .W32))
            (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  obtain ⟨hmapped, hpre⟩ := hpre
  obtain ⟨v, hload⟩ := Option.isSome_iff_exists.mp hmapped
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.set_low_W32, AddrExpr.zeroExtend_interp_base_idx8, Width.bytes, hload, Effects.All]
  exact hn _ (by rwa [hload, Option.get!_some] at hpre)

-- `andb %rs8, %rd8`: the bits above the low byte of `rd` stay.
theorem andb_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).take 8 &&& (s.regs.get64 rs).take 8
        ∀ af : Bool, Q () { s with
          regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v)
          status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8
          (.and (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, MachineData.setReg,
    Effects.All]
  simp only [Reg64s.get_low_W8, Reg64s.set_low_W8]
  intro af
  exact hn _ (hpre af)
end

/-! ## The variant -/

-- The variant of the CFG proof: `na` and `nq` are `addCount` and `queryCount`. The four loops
-- run in order, so each loop has a band of `4 * 2 ^ 64` above the bands of the loops after it.
def var (na nq : Nat) (l : String) (t : MachineData) : Nat :=
  if l = "spill_set" then 7 * (4 * 2 ^ 64)
  else if l = ".LB.spill_set.14" then 6 * (4 * 2 ^ 64)
  else if l = ".LB.spill_set.1" then 5 * (4 * 2 ^ 64) + 2 * (na - (rax t).toNat) + 1
  else if l = ".LB.spill_set.0" then 5 * (4 * 2 ^ 64) + 2 * (na - (rax t).toNat)
  else if l = ".LB.spill_set.15" then 5 * (4 * 2 ^ 64) - 1
  else if l = ".LB.spill_set.3" then 4 * (4 * 2 ^ 64) + 2 * (nq - (rax t).toNat) + 1
  else if l = ".LB.spill_set.2" then 4 * (4 * 2 ^ 64) + 2 * (nq - (rax t).toNat)
  else if l = ".LB.spill_set.4" then 4 * (4 * 2 ^ 64) - 1
  else if l = ".LB.spill_set.5" then 3 * (4 * 2 ^ 64) + 2 ^ 64 + 1
  else if l = ".LB.spill_set.6" then 3 * (4 * 2 ^ 64) + (na - t.regs.r14.toBitVec.toNat)
  else if l = ".LB.spill_set.7" then 2 * (4 * 2 ^ 64) + 2 * 2 ^ 64 + 2
  else if l = ".LB.spill_set.9" then 2 * (4 * 2 ^ 64) + 2 * (nq - (rax t).toNat) + 1
  else if l = ".LB.spill_set.8" then 2 * (4 * 2 ^ 64) + 2 * (nq - (rax t).toNat)
  else if l = ".LB.spill_set.10" ∨ l = ".LB.spill_set.13" ∨ l = ".LB.spill_set.11" then 1
  else 0

/-! ## The model -/

-- The result byte of the query `q`.
def g (f : BitVec 32 → BitVec 8) (q : StackSlot) : BitVec 8 :=
  Flat.boolByte (Flat.spillIsSpilled f q)

-- The check of a slot: a literal, a slot that is not a value, and an id below `n` pass.
theorem idOk_op {n : Word} {x : StackSlot} (h : x.valueOpcode = 0#8) : Flat.idOk n x = true := by
  simp [Flat.idOk, Flat.isVariable, isLiteralValue, Const, h]

theorem idOk_kind {n : Word} {x : StackSlot} (h : x.kind ≠ 0#8) : Flat.idOk n x = true := by
  simp [Flat.idOk, Flat.isVariable, Value, h]

theorem idOk_lt {n : Word} {x : StackSlot} (h : x.payload.toNat < n.toNat) :
    Flat.idOk n x = true := by
  simp only [Flat.idOk, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Nat.not_le]
  exact Or.inr h

theorem idOk_false {n : Word} {x : StackSlot} (hk : x.kind = 0#8) (ho : x.valueOpcode ≠ 0#8)
    (h : n.toNat ≤ x.payload.toNat) : Flat.idOk n x = false := by
  simp [Flat.idOk, Flat.isVariable, isLiteralValue, Value, Const, hk, ho, h]

theorem all_take_succ {α : Type} {p : α → Bool} {l : List α} {i : Nat} (hi : i < l.length)
    (h : (l.take i).all p = true) (hp : p l[i] = true) : (l.take (i + 1)).all p = true := by
  rw [List.take_succ_eq_append_getElem hi, List.all_append, h, Bool.true_and]
  simpa using hp

theorem all_false {α : Type} {p : α → Bool} {l : List α} {i : Nat} (hi : i < l.length)
    (hp : p l[i] = false) : l.all p = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [List.all_eq_true] at h
  simp [h _ (List.getElem_mem hi)] at hp

-- A check that fails: `spill_set` returns `-2` and changes nothing.
theorem setRes_bad {s : MachineData} {f : BitVec 32 → BitVec 8} {adds queries : List Word}
    {res : List (BitVec 8)}
    (h : ((adds.map StackSlot.ofWord).all (Flat.idOk (rdi s))
      && (queries.map StackSlot.ofWord).all (Flat.idOk (rdi s))) = false) :
    setRes s f adds queries res = (-2#64, f, res) := by
  simp only [setRes, Flat.spill_set, h, Bool.not_false, ↓reduceIte]
  rfl

-- The id of a variable slot that passes the check is a byte of `spilled`.
theorem lt_ids {n : Word} {x : StackSlot} (hok : Flat.idOk n x = true)
    (hv : Flat.isVariable x = true) : x.payload.toNat < Flat.ids n := by
  simp only [Flat.idOk, hv, Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not,
    Nat.not_le] at hok
  have := x.payload.isLt
  unfold Flat.ids
  omega

theorem idOk_of_all {n : Word} {l : List StackSlot} {i : Nat} (hi : i < l.length)
    (h : l.all (Flat.idOk n) = true) : Flat.idOk n l[i] = true :=
  List.all_eq_true.mp h _ (List.getElem_mem hi)

theorem isVariable_eq (x : StackSlot) :
    Flat.isVariable x = (x.kind == 0#8 && !(x.valueOpcode == 0#8)) := rfl

/-! ## The loop of the adds -/

section
variable {f f' : BitVec 32 → BitVec 8}

theorem spillAddAll_append (f : BitVec 32 → BitVec 8) (xs ys : List StackSlot) :
    Flat.spillAddAll f (xs ++ ys)
      = if (Flat.spillAddAll f xs).1 = .done then Flat.spillAddAll (Flat.spillAddAll f xs).2 ys
        else Flat.spillAddAll f xs := by
  induction xs generalizing f with
  | nil => simp [Flat.spillAddAll]
  | cons x xs ih =>
    by_cases hd : (Flat.spillAdd f x).1 = .done
    · simp only [List.cons_append, Flat.spillAddAll, hd, ↓reduceIte]; exact ih _
    · simp only [List.cons_append, Flat.spillAddAll, hd, ↓reduceIte]

theorem addAll_step {l : List StackSlot} {i : Nat} (hi : i < l.length)
    (h : Flat.spillAddAll f (l.take i) = (.done, f')) :
    Flat.spillAddAll f (l.take (i + 1)) = Flat.spillAdd f' l[i] := by
  rw [List.take_succ_eq_append_getElem hi, spillAddAll_append, h]
  simp only [↓reduceIte, Flat.spillAddAll]
  by_cases hd : (Flat.spillAdd f' l[i]).1 = .done
  · simp only [hd, ↓reduceIte]; exact Prod.ext hd.symm rfl
  · simp only [hd, ↓reduceIte]

-- An add that fails ends the loop.
theorem addAll_fail {l : List StackSlot} {i : Nat}
    (h : (Flat.spillAddAll f (l.take i)).1 ≠ .done) :
    Flat.spillAddAll f l = Flat.spillAddAll f (l.take i) := by
  rw [← congrArg (Flat.spillAddAll f) (List.take_append_drop i l), spillAddAll_append, ite_eq_right h]

theorem addAll_all {l : List StackSlot} {i : Nat} (hi : l.length ≤ i) :
    Flat.spillAddAll f (l.take i) = Flat.spillAddAll f l := by
  rw [List.take_of_length_le hi]
end

section
variable {s : MachineData} {f f' : BitVec 32 → BitVec 8} {adds queries : List Word}
  {res : List (BitVec 8)}

theorem setRes_done (hok : (adds.map StackSlot.ofWord).all (Flat.idOk (rdi s)) = true)
    (hq : (queries.map StackSlot.ofWord).all (Flat.idOk (rdi s)) = true)
    (h : Flat.spillAddAll f (adds.map StackSlot.ofWord) = (.done, f')) :
    setRes s f adds queries res = (0#64, f', (queries.map StackSlot.ofWord).map (g f')) := by
  simp only [setRes, Flat.spill_set, hok, hq, h, Bool.and_self, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

theorem setRes_fail {st : Flat.Status}
    (hok : (adds.map StackSlot.ofWord).all (Flat.idOk (rdi s)) = true)
    (hq : (queries.map StackSlot.ofWord).all (Flat.idOk (rdi s)) = true)
    (h : Flat.spillAddAll f (adds.map StackSlot.ofWord) = (st, f')) (hst : st ≠ .done) :
    setRes s f adds queries res = (-2#64, f', res) := by
  simp only [setRes, Flat.spill_set, hok, hq, h, hst, Bool.and_self, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  all_goals rfl
end

/-! ## The loop of the queries -/

-- The results after `i` queries: the bytes of the first `i` queries, then the old bytes.
theorem res_step {f : BitVec 32 → BitVec 8} {Q : List StackSlot} {res : List (BitVec 8)}
    {i : Nat} (hi : i < Q.length) (hr : Q.length = res.length) :
    ((Q.take i).map (g f) ++ res.drop i).set i (g f Q[i])
      = (Q.take (i + 1)).map (g f) ++ res.drop (i + 1) := by
  have hri : i < res.length := hr ▸ hi
  rw [List.drop_eq_getElem_cons hri, List.set_append_right _ _ (by simp; omega),
    List.take_succ_eq_append_getElem hi, List.map_append, List.append_assoc]
  simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi), Nat.sub_self,
    List.set_cons_zero, List.map_cons, List.map_nil, List.cons_append, List.nil_append]

theorem res_end {f : BitVec 32 → BitVec 8} {Q : List StackSlot} {res : List (BitVec 8)}
    {i : Nat} (hi : i = Q.length) (hr : Q.length = res.length) :
    (Q.take i).map (g f) ++ res.drop i = Q.map (g f) := by
  subst hi
  rw [List.take_length, hr, List.drop_length, List.append_nil]

/-! ## The flags and the bytes -/

-- `testq %r, %r; jne` taken.
theorem nz_true {r : Word} (h : (!(r &&& r == BitVec.zero 64)) = true) : r ≠ 0#64 :=
  ShallowestCopy.zf_false (by simpa only [Bool.not_eq_true'] using h)

-- `testq %r, %r; jne` not taken.
theorem nz_false {r : Word} (h : (!(r &&& r == BitVec.zero 64)) = false) : r = 0#64 :=
  ShallowestCopy.zf_true (by simpa only [Bool.not_eq_false'] using h)

-- `setne %dl` and `andb %cl, %dl` write the low byte of `rdx`.
theorem setWidth_replaceLow (x : Word) (v : BitVec 8) :
    BitVec.setWidth 8 (x.replaceLow v) = v := by
  conv => rhs; rw [← BitVec.take_replaceLow_8 x v]
  ext i hi
  simp [BitVec.take]

-- `movb %dl, m`: the byte that the store writes.
theorem ofInt_extract8 (x : Word) :
    BitVec.ofInt 8 (BitVec.extractLsb' 0 8 x).toInt = x.setWidth 8 := by
  rw [BitVec.ofInt_toInt, BitVec.setWidth_eq_extractLsb' (by decide)]

-- `cmpb $0, op; setne %dl; cmpb $0, kind; sete %cl; andb %cl, %dl`.
theorem andb_byte (a b : BitVec 8) :
    (BitVec.ofNat 8 (!(a - 0#8 == BitVec.zero 8)).toNat
        &&& BitVec.ofNat 8 (b - 0#8 == BitVec.zero 8).toNat)
      = Flat.boolByte (b == 0#8 && !(a == 0#8)) := by
  rw [BitVec.sub_zero, BitVec.sub_zero, show BitVec.zero 8 = 0#8 from rfl]
  cases a == 0#8 <;> cases b == 0#8 <;> rfl

-- `cmpb $0, b; setne %dl`.
theorem setne_byte (b : BitVec 8) :
    BitVec.ofNat 8 (!(b - 0#8 == BitVec.zero 8)).toNat = Flat.boolByte (b != 0#8) := by
  rw [BitVec.sub_zero, show BitVec.zero 8 = 0#8 from rfl]
  unfold bne
  cases b == 0#8 <;> rfl

-- `je` after `andb`: the byte is zero.
theorem boolByte_beq (b : Bool) : (Flat.boolByte b == BitVec.zero 8) = !b := by
  cases b <;> rfl

theorem g_not_var {f : BitVec 32 → BitVec 8} {q : StackSlot} (h : Flat.isVariable q = false) :
    g f q = Flat.boolByte (Flat.isVariable q) := by
  unfold g Flat.spillIsSpilled
  rw [h, Bool.false_and]

theorem g_var {f : BitVec 32 → BitVec 8} {q : StackSlot} (h : Flat.isVariable q = true) :
    g f q = Flat.boolByte (f q.payload != 0#8) := by
  unfold g Flat.spillIsSpilled
  rw [h, Bool.true_and]
  all_goals rfl

-- `cmpq %n, %a; jb` taken.
theorem lt_of_cfb {a n : Word}
    (h : ((((a - n).toNat : Int) != (a.toNat : Int) - (n.toNat : Int))) = true) :
    a.toNat < n.toNat := by
  rw [Idioms.cf_sub] at h
  simpa using h

-- `cmpq %n, %a; jb` not taken.
theorem ge_of_cfb {a n : Word}
    (h : ((((a - n).toNat : Int) != (a.toNat : Int) - (n.toNat : Int))) = false) :
    n.toNat ≤ a.toNat := by
  rw [Idioms.cf_sub] at h
  simpa using h

-- `andb %cl, %dl; je` not taken: the slot is a variable.
theorem var_of_andb {a b : BitVec 8} {q : StackSlot} (ho : a = q.valueOpcode) (hk : b = q.kind)
    (h : (BitVec.ofNat 8 (!(a - 0#8 == BitVec.zero 8)).toNat
        &&& BitVec.ofNat 8 (b - 0#8 == BitVec.zero 8).toNat == BitVec.zero 8) = false) :
    Flat.isVariable q = true := by
  rw [andb_byte, boolByte_beq, ho, hk, ← isVariable_eq] at h
  simpa using h

-- `andb %cl, %dl; je` taken: the slot is not a variable.
theorem notvar_of_andb {a b : BitVec 8} {q : StackSlot} (ho : a = q.valueOpcode)
    (hk : b = q.kind)
    (h : (BitVec.ofNat 8 (!(a - 0#8 == BitVec.zero 8)).toNat
        &&& BitVec.ofNat 8 (b - 0#8 == BitVec.zero 8).toNat == BitVec.zero 8) = true) :
    Flat.isVariable q = false := by
  rw [andb_byte, boolByte_beq, ho, hk, ← isVariable_eq] at h
  simpa using h

end Bbu.Unit.SpillSetProof
