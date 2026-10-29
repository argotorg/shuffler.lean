import BbuKraken.Kit

/-!
Lemmas for the body triples of `push` (`c/bbu/push.S`) and `dup` (`c/bbu/dup.S`).
Both save three registers, call `positionOf`, and then write the new slot and the
operation.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace PushDup

-- The registers that `push` and `dup` save, in the order of the pushes.
abbrev regs : List Reg64 := [.r12, .rbp, .rbx]

-- The memory of `push` and `dup`: the frame of 40 bytes, the saved words and the struct.
abbrev Fm := Kit.Fm 40 regs

section
variable {s : MachineData} {ra : Int64} {A : MachineData → Prop}

-- The state `c` after the call to `positionOf`.
structure After (s : MachineData) (ra : Int64) (c : MachineData) : Prop where
  fm : Fm s ra c.dmem
  mst : stOf c.dmem (rdi s) = st s
  ax : c.regs.rax.toBitVec = encOpt (positionOf (st s) (rdx s).toNat)
  rsp : c.regs.rsp.toBitVec = rsp s - 32#64
  rbx : c.regs.rbx.toBitVec = s.regs.rdi.toBitVec
  rbp : c.regs.rbp.toBitVec = s.regs.rsi.toBitVec
  r12 : c.regs.r12.toBitVec = s.regs.rdx.toBitVec
  r13 : c.regs.r13 = s.regs.r13
  r14 : c.regs.r14 = s.regs.r14
  r15 : c.regs.r15 = s.regs.r15

theorem after {C c : MachineData} (hp : Post 8 positionOfR C c) (hag : (mod 8 C).Agree C c)
    (hpre : Pre 40 A s) (hm : C.dmem = Kit.pushes s ra regs)
    (hsp : C.regs.rsp.toBitVec = rsp s - 32#64) (hdi : C.regs.rdi = s.regs.rdi)
    (hsi : C.regs.rsi.toBitVec = s.regs.rdx.toBitVec)
    (hbx : C.regs.rbx.toBitVec = s.regs.rdi.toBitVec) (hbp : C.regs.rbp.toBitVec = s.regs.rsi.toBitVec)
    (h12 : C.regs.r12.toBitVec = s.regs.rdx.toBitVec) (h13 : C.regs.r13 = s.regs.r13)
    (h14 : C.regs.r14 = s.regs.r14) (h15 : C.regs.r15 = s.regs.r15) : After s ra c := by
  have hrdi : rdi C = rdi s := by simp only [rdi, Reg64s.get64_rdi, hdi]
  have hreg : ∀ r, r ∉ (mod 8 C).regs → c.regs.get64 r = C.regs.get64 r := hag.1
  obtain ⟨-, -, hrax, hst⟩ := id hp
  have hs := Kit.st_pushes (rs := regs) (ra := ra) (by decide) hpre
  simp only [st', st, hrdi, hm, hs] at hst
  simp only [rax, st, hrdi, hm, hs, rsi, Reg64s.get64_rsi, hsi] at hrax
  have g := fun r (h : r ∉ (mod 8 C).regs) => hreg r h
  refine ⟨Kit.Fm.call (k := 32) (by decide) (by decide) hpre (Kit.Fm.init (by decide) hpre) hm hsp
    hrdi hp hag, hst, hrax, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := g .rsp (by simp [mod]); simp only [Reg64s.get64_rsp] at this; rw [this, hsp]
  · have := g .rbx (by simp [mod]); simp only [Reg64s.get64_rbx] at this; rw [this, hbx]
  · have := g .rbp (by simp [mod]); simp only [Reg64s.get64_rbp] at this; rw [this, hbp]
  · have := g .r12 (by simp [mod]); simp only [Reg64s.get64_r12] at this; rw [this, h12]
  · have := g .r13 (by simp [mod]); simp only [Reg64s.get64_r13] at this
    rw [← h13]; exact UInt64.toBitVec_inj.mp this
  · have := g .r14 (by simp [mod]); simp only [Reg64s.get64_r14] at this
    rw [← h14]; exact UInt64.toBitVec_inj.mp this
  · have := g .r15 (by simp [mod]); simp only [Reg64s.get64_r15] at this
    rw [← h15]; exact UInt64.toBitVec_inj.mp this

end
-- `jne` after `cmpq $-1` of the result of `positionOf`.
theorem pos_nz {st : St} {d : Nat} (hl : st.len ≤ 1024) (r) :
    CondCode.nz.interp (StatusFlags.from_result (encOpt (positionOf st d) - 18446744073709551615#64) r)
      = (positionOf st d).isSome := by
  rw [Kit.nz_sub]
  cases hp : positionOf st d with
  | none => simp [encOpt]
  | some p =>
    have : p < st.len := by
      simp only [positionOf, List.findIdx?_eq_some_iff_getElem] at hp; exact hp.1
    simp only [encOpt, Option.isSome_some, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne]
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega

section
variable {m : Mem 64} {S : Addr}

-- The reads after stores, one store at a time.
macro "pd_rds" : tactic => `(tactic| (
  repeat (first
    | (rw [rd_store_same]; rotate_left; bv_omega)
    | (rw [rd_store_other]; rotate_left; bv_omega))
  try simp only [BitVec.ofInt_toInt]))

-- The struct before the stores.
structure Lay (m : Mem 64) (S : Addr) : Prop where
  wf : Wf m S
  len : (rd m S).toNat < 1024
  nops : (rd m (S + 16#64)).toNat < 6 * nOf m S

theorem Lay.nat (h : Lay m S) :
    S.toNat + 16448 ≤ 2 ^ 64 ∧ (rd m (S + 48#64)).toNat + 96 * nOf m S ≤ 2 ^ 64
      ∧ 16448 ≤ (rd m (S + 48#64) - S).toNat ∧ 96 * nOf m S ≤ (S - rd m (S + 48#64)).toNat := by
  have hs : S.toNat + 16448 ≤ 2 ^ 64 := h.wf.struct_lt
  have ho : (rd m (S + 48#64)).toNat + 96 * nOf m S ≤ 2 ^ 64 := h.wf.ops_lt
  have hn := h.nops
  refine ⟨hs, ho, Nat.not_lt.mp fun hx => ?_, Nat.not_lt.mp fun hx => ?_⟩
  · refine h.wf.disj_struct (rd m (S + 48#64)) (Or.inl (show _ + 1 ≤ 16448 by omega)) (Or.inl ?_)
    show (rd m (S + 48#64) - rd m (S + 48#64)).toNat + 1 ≤ 96 * nOf m S
    simp only [BitVec.sub_self, BitVec.toNat_zero]; omega
  · refine h.wf.disj_struct S (Or.inl (show (S - S).toNat + 1 ≤ 16448 by simp)) (Or.inl ?_)
    show (S - rd m (S + 48#64)).toNat + 1 ≤ 96 * nOf m S
    omega

-- The address of the new operation.
abbrev opA (m : Mem 64) (S : Addr) : Addr := rd m (S + 48#64) + rd m (S + 16#64) * 16#64

-- The memory after the stores of `push` and `dup`: the destination of the new slot,
-- the new operation `⟨c, r⟩`, `nops + 1`, the value of the new slot and `len + 1`.
def stores (m : Mem 64) (S : Addr) (v d : Word) (c : Int) (r : Word) : Mem 64 :=
  (((((m.storeInt (S + rd m S * 8#64 + 8256#64) 8 d.toInt).storeInt (opA m S) 8 c).storeInt
    (opA m S + 8#64) 8 r.toInt).storeInt (S + 16#64) 8 (1#64 + rd m (S + 16#64)).toInt).storeInt
    (S + rd m S * 8#64 + 64#64) 8 v.toInt).storeInt S 8 (1#64 + rd m S).toInt

theorem stores_un (h : Lay m S) (v d : Word) (c : Int) (r : Word) :
    Mem.UnchangedOutside (writable m S) m (stores m S v d c r) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.nat
  have := h.nops
  have hl := h.len
  have h0 : Mem.UnchangedOutside (writable m S) m m := fun _ _ => rfl
  refine (((((h0.storeInt ?_ _).storeInt ?_ _).storeInt ?_ _).storeInt ?_ _).storeInt ?_ _).storeInt ?_ _
  all_goals simp only [writable, opsOf, wordAt, STACK, MAX_N, Mem.Blocks.Inside, Nat.reduceMul]
  · exact Or.inr (Or.inl (by bv_omega))
  · exact Or.inr (Or.inr (Or.inl (by bv_omega)))
  · exact Or.inr (Or.inr (Or.inl (by bv_omega)))
  · exact Or.inl (by bv_omega)
  · exact Or.inr (Or.inl (by bv_omega))
  · exact Or.inl (by bv_omega)

-- The facts for `bv_omega` of a `Lay`.
local macro "lay_facts" h:term : tactic => `(tactic| (
  obtain ⟨h1, h2, h3, h4⟩ := ($h).nat
  have hn := ($h).nops
  have hl := ($h).len
  generalize nOf m S = n at h2 h4 hn))

section
variable (h : Lay m S) (v d : Word) (c : Int) (r : Word)
include h

theorem stores_len : rd (stores m S v d c r) S = 1#64 + rd m S := by
  lay_facts h; simp only [stores]; pd_rds

theorem stores_pend : rd (stores m S v d c r) (wordAt S 1) = rd m (wordAt S 1) := by
  lay_facts h; simp only [stores, wordAt]; pd_rds

theorem stores_nops : rd (stores m S v d c r) (wordAt S 2) = 1#64 + rd m (S + 16#64) := by
  lay_facts h; simp only [stores, wordAt]; pd_rds

theorem stores_ops : opsOf (stores m S v d c r) S = rd m (S + 48#64) := by
  lay_facts h; simp only [stores, opsOf, wordAt, Nat.reduceMul]; pd_rds

theorem stores_slot {i : Nat} (hi : i < (rd m S).toNat) :
    slotOf (stores m S v d c r) S i = slotOf m S i := by
  lay_facts h; simp only [slotOf, stores, wordAt, STACK, DEST_eq]; pd_rds

theorem stores_slotL : slotOf (stores m S v d c r) S (rd m S).toNat = ⟨v, d.toNat⟩ := by
  lay_facts h; simp only [slotOf, stores, wordAt, STACK, DEST_eq]; pd_rds

theorem stores_op {i : Nat} (hi : i < (rd m (S + 16#64)).toNat) :
    opOf (stores m S v d c r) S i = opOf m S i := by
  simp only [opOf]
  rw [stores_ops h]
  lay_facts h; simp only [stores, opsOf, wordAt, Nat.reduceMul]; pd_rds

theorem stores_opN : opOf (stores m S v d c r) S (rd m (S + 16#64)).toNat = ⟨BitVec.ofInt 64 c, r⟩ := by
  simp only [opOf]
  rw [stores_ops h]
  lay_facts h; simp only [stores, wordAt]; pd_rds

theorem stOf_stores :
    stOf (stores m S v d c r) S =
      { stOf m S with slots := (stOf m S).slots ++ [(⟨v, d.toNat⟩ : Slot)]
                      trace := (stOf m S).trace ++ [(⟨BitVec.ofInt 64 c, r⟩ : Op)] } := by
  have hl1 : (1#64 + rd m S).toNat = (rd m S).toNat + 1 := by have := h.len; bv_omega
  have hn1 : (1#64 + rd m (S + 16#64)).toNat = (rd m (S + 16#64)).toNat + 1 := by
    have := h.nops; have := h.wf.ops_lt; bv_omega
  have hw0 : wordAt S 0 = S := by simp [wordAt]
  have hw2 : wordAt S 2 = S + 16#64 := rfl
  simp only [stOf, stores_len h, stores_pend h, stores_nops h, hl1, hn1, List.range_succ,
    List.map_append, List.map_cons, List.map_nil, stores_slotL h, stores_opN h, hw0, hw2]
  congr 2
  · exact List.map_congr_left fun i hi => stores_slot h v d c r (List.mem_range.mp hi)
  · exact List.map_congr_left fun i hi => stores_op h v d c r (List.mem_range.mp hi)

end

end
section
variable {s : MachineData} {ra : Int64} {A : MachineData → Prop} {m : Mem 64}

theorem Fm.lay (hpre : Pre 40 A s) (hA : (st s).len < MAX_N ∧ (st s).trace.length < cap s)
    (h : Fm s ra m) (hst : stOf m (rdi s) = st s) : Lay m (rdi s) := by
  have hn : nOf m (rdi s) = nOf s.dmem (rdi s) :=
    congrArg BitVec.toNat (hdr_congr h.un hpre.disj (k := 3) (by omega) (by omega))
  obtain ⟨hl, ho⟩ := hA
  rw [← hst] at hl ho
  refine ⟨h.wf, ?_, ?_⟩
  · simpa [St.len, stOf, wordAt, MAX_N] using hl
  · rw [hn]; simpa [stOf, cap] using ho

theorem Fm.after_stores (hpre : Pre 40 A s) (h : Fm s ra m) (hl : Lay m (rdi s)) (v d : Word)
    (c : Int) (r : Word) : Fm s ra (stores m (rdi s) v d c r) := by
  have hwr := (h.keeps hpre).2.2
  have hm0 : Mem.Mapped (writable m (rdi s)) m := fun x hx => h.wf.mapped x (inside_append.mpr (Or.inl hx))
  have hst := stOf_stores hl v d c r
  have hsl := congrArg (fun t => t.slots.length) hst
  have hop := congrArg (fun t => t.trace.length) hst
  simp only [stOf, List.length_map, List.length_range, List.length_append, List.length_cons,
    List.length_nil] at hsl hop
  have hlen := hl.len
  have hnops := hl.nops
  refine Kit.Fm.write (by decide) hpre h (hwr ▸ stores_un hl v d c r) ?_ ?_ ?_
  · rw [← hwr]
    exact ((((((hm0.storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _).storeInt _ _ _)
  · simp only [wordAt, Nat.reduceMul, BitVec.add_zero, MAX_N] at hsl hlen ⊢; omega
  · have hn : nOf m (rdi s) = nOf s.dmem (rdi s) :=
      congrArg BitVec.toNat (hdr_congr h.un hpre.disj (k := 3) (by omega) (by omega))
    simp only [wordAt, Nat.reduceMul] at hop hnops ⊢; omega

-- A load from the struct regions after stores that keep them mapped.
theorem isSome_of {m m' : Mem 64} {S a : Addr} (_hw : Wf m S)
    (hm : Mem.Mapped (writable m S ++ readable m S) m')
    (hin : Mem.Blocks.Inside a 8 (writable m S ++ readable m S)) : (m'.loadInt a 8).isSome = true :=
  hm.loadInt_isSome hin

-- The pops read the saved words.
theorem Fm.pops (h : Fm s ra m) {a : Addr} (ha : a = rsp s - 32#64) :
    rd m a = s.regs.rbx.toBitVec ∧ rd m (a + 8#64) = s.regs.rbp.toBitVec
      ∧ rd m (a + 8#64 + 8#64) = s.regs.r12.toBitVec := by
  subst ha
  refine ⟨h.saved 2 (by decide), ?_, ?_⟩
  · rw [show rsp s - 32#64 + 8#64 = rsp s - 24#64 by bv_omega]; exact h.saved 1 (by decide)
  · rw [show rsp s - 32#64 + 8#64 + 8#64 = rsp s - 16#64 by bv_omega]; exact h.saved 0 (by decide)

-- The result of `push` and `dup` depends on `rax` and the memory.
theorem res_congr {r : M St} {t t' : MachineData} (hm : t'.dmem = t.dmem) (hax : rax t' = rax t)
    (h : Res (rdi s) r (Ok s t (fun _ => 0#64) id) t) : Res (rdi s) r (Ok s t' (fun _ => 0#64) id) t' := by
  unfold Res at *
  rcases r with (⟨p, x⟩ | _) | a
  · exact ⟨hax.trans h.1, hm ▸ h.2.1, hm ▸ h.2.2⟩
  · exact hax.trans h
  · exact ⟨hax.trans h.1, by simp only [st', hm]; exact h.2⟩

end

end PushDup

end Bbu
