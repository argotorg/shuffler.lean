import BbuKraken.Unit.Loop.Step

/-!
# `buildBottomUp`: the prologue, the loop head, the end, and the epilogue (part P2)

The blocks of the entry, `Names.buildBottomUp` (prologue), `.26` and `.25` (the head and
the end of an iteration), `.27` (the test of `pend`), `.0` (`permute`), `.31` (the end
of the loop), `.13` (epilogue), `.28`, `.29`, `.30` (assertions) and `.24`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Loop

/-! ## The variant at the end of an iteration -/

-- `T + 1` with the same memory: `H` falls by `2 ^ 24`.
private theorem H_succ {S : Addr} {T : Word} {t t' : MachineData} {c d : Nat}
    (hm : t'.dmem = t.dmem) (hT : T.toNat < 1024) (hcd : c < 2 ^ 24 + d) :
    H S (T + 1#64) t' + c < H S T t + d := by
  simp only [H, hm, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

-- A slot offset is below `MAX_N = 1024`.
private theorem lt_1024 {g' : G} {T : Word} (h : Flat.FInv (flat g')) (hT : T < g'.h.len) :
    T.toNat < 1024 :=
  h.lt_max_of_size hT

/-! ## Loads of the struct at `r12` (the address form of `symexec`) -/

section
variable {S : Addr} {g : G} {R : MProp 64} {m : Mem 64}

private theorem rd_n' (h : (View S g ∗ R).get m) :
    BitVec.ofInt 64 (m.loadInt (S + 8#64) 8).get! = g.h.n := by
  rw [Fld.fold_targetSize]; exact rd_of_eq h (by unfold View Em; ecancel)
private theorem isSome_n' (h : (View S g ∗ R).get m) : (m.loadInt (S + 8#64) 8).isSome = true := by
  rw [Fld.fold_targetSize]; exact isSome_of_eq g.h.n h (by unfold View Em; ecancel)
private theorem rd_len' (h : (View S g ∗ R).get m) :
    BitVec.ofInt 64 (m.loadInt (S + 32#64) 8).get! = g.h.len := by
  rw [Fld.fold_stack_size]; exact View.rd_len h
private theorem isSome_len' (h : (View S g ∗ R).get m) : (m.loadInt (S + 32#64) 8).isSome = true := by
  rw [Fld.fold_stack_size]; exact View.isSome_len h
private theorem rd_pend' (h : (View S g ∗ R).get m) :
    BitVec.ofInt 64 (m.loadInt (S + 16440#64) 8).get! = g.h.pend := by
  rw [Fld.fold_pendingGenerations]; exact rd_pend h
private theorem isSome_pend' (h : (View S g ∗ R).get m) :
    (m.loadInt (S + 16440#64) 8).isSome = true := by
  rw [Fld.fold_pendingGenerations]; exact isSome_pend h
private theorem rd_dest' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    BitVec.ofInt 64 (m.loadInt (S + x * 8#64 + 56#64) 8).get! = Flat.get g.h.dest x := by
  rw [Fld.fold_mapping_destinationOf]; simp only [Flat.get, hx, ↓reduceDIte]
  obtain ⟨_, h'⟩ := View.arr_dest h
  exact (Arr.rd h' (by simpa using hx)).trans (by simp)
private theorem isSome_dest' (h : (View S g ∗ R).get m) {x : Word} (hx : x.toNat < MAX_N) :
    (m.loadInt (S + x * 8#64 + 56#64) 8).isSome = true := by
  rw [Fld.fold_mapping_destinationOf]; exact View.isSome_dest h hx

end

-- `setne %al; addl %eax, %eax`: the byte `al` is `v + v`.
private theorem al_add_self (x : Word) (v : BitVec 8) :
    BitVec.setWidth 8 (BitVec.extractLsb' 0 32 (x.replaceLow v)
      + BitVec.extractLsb' 0 32 (x.replaceLow v)) = v + v := by
  have h : BitVec.setWidth 8 (x.replaceLow v) = v := by
    conv => rhs; rw [← BitVec.take_replaceLow_8 x v]
    ext i hi; simp [BitVec.take]
  generalize x.replaceLow v = y at h ⊢
  subst h
  bv_decide

-- A load of the epilogue, at the address form of `symexec`.
private theorem isSome_pop' {S : Addr} {g' : G} {F : MProp 64} {s : MachineData} {ra : Int64}
    {x0 : Word} {x2 : Lc} {lo : List Word} {w u : Word} {t : MachineData}
    (h : Mid S g' F s ra x0 x2 lo w u t) {a : Word} {k : Nat} (hk : k < 6)
    (ha : a = 8216#64 + t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * k)) :
    (t.dmem.loadInt a 8).isSome = true := by
  subst ha; exact h.isSome_pop hk

-- A store into a word atom; `ecancel` finds the atom and the rest `R`.
private theorem wd_store' {P R : MProp 64} {a : Addr} {v : Word} {m : Mem 64} (v' : Word)
    (h : P.get m) (e : P = Wd a v ∗ R) : (Wd a v' ∗ R).get (m.storeInt a 8 v'.toInt) :=
  Wd.store (e ▸ h) v'

private theorem get_of_eq {P Q : MProp 64} {m : Mem 64} (h : P.get m) (e : P = Q) : Q.get m :=
  e ▸ h

-- `loopA` is `HInv` at `T = 0`.
private theorem fn_hinv {g : G} {s : MachineData} (hA : loopA g s) :
    Flat.HInv (flat g) 0#64 g.xo := hA

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {x0 : Word} {x2 : Lc}
  {lo : List Word} {w u : Word} {c : MachineData}

-- The two exits of the prologue: `r13 = n` (the load of `8(%rdi)`).
private theorem fn_n (hM : Mid S g F s ra x0 x2 lo w u c) (hdi : c.regs.rdi.toBitVec = S)
    (h13 : c.regs.r13.toBitVec
      = BitVec.ofInt 64 (c.dmem.loadInt (c.regs.rdi.toBitVec + 8#64) 8).get!) :
    c.regs.r13.toBitVec = g.h.n := by
  rw [h13, hdi]; exact rd_n' hM.mem

-- `n = 0`: the loop ends at once.
private theorem fn_31 (hM : Mid S g F s ra x0 x2 lo w u c) (hok : g.Ok)
    (hdi : c.regs.rdi.toBitVec = S)
    (h13 : c.regs.r13.toBitVec
      = BitVec.ofInt 64 (c.dmem.loadInt (c.regs.rdi.toBitVec + 8#64) 8).get!)
    (h0 : c.regs.r13.toBitVec = 0#64) : I31 S g F s ra c := by
  have hn := fn_n hM hdi h13
  refine ⟨g, u, ⟨x0, x2, lo, w, hM, hok, keep_refl g⟩, hn, ?_⟩
  show Flat.loop (flat g) 0#64 = _
  refine Flat.loop_ge ?_
  show ¬0#64 < g.h.n
  rw [← hn, h0]; decide

-- `n ≠ 0`: the head at `T = 0`.
private theorem fn_26 (hM : Mid S g F s ra x0 x2 lo w u c) (hok : g.Ok) (hA : loopA g s)
    (hdi : c.regs.rdi.toBitVec = S)
    (h13 : c.regs.r13.toBitVec
      = BitVec.ofInt 64 (c.dmem.loadInt (c.regs.rdi.toBitVec + 8#64) 8).get!)
    (hnz : c.regs.r13.toBitVec ≠ 0#64) (h14 : c.regs.r14.toBitVec = 0#64) :
    I26 S g F s ra c := by
  have hn := fn_n hM hdi h13
  refine ⟨g, u, ⟨x0, x2, lo, w, hM, hok, keep_refl g⟩, hn, ?_, ?_, ?_⟩
  · rw [h14, ← hn]; bv_omega
  · rw [h14]; exact fn_hinv hA
  · rw [h14]; rfl

-- The variant at the head `T = 0` is below the variant of the entry: `pend ≤ n ≤ 1024`.
private theorem fn_V {T : Word} (hM : Mid S g F s ra x0 x2 lo w u c) (hok : g.Ok)
    (hA : loopA g s) (hT : T = 0#64) : H S T c + 4200 < 2 ^ 36 := by
  have hc : g.h.len.toNat + g.h.pend.toNat = g.h.n.toNat := (fn_hinv hA).f.cnt
  have hn : g.h.n.toNat ≤ 1024 := hok.n
  simp only [H, hT, hM.rd_pend, BitVec.toNat_ofNat, Nat.zero_mod, Nat.reducePow]
  omega

end

theorem b_entry [Host] [FunDecls] (S g F s ra) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .entry → Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  simp only [LInv, Names.buildBottomUp, ↓reduceIte]
  exact ht

theorem b_fn [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label Names.buildBottomUp →
      Obl S g F s ra blk := by
  cfg_block [Obl, Names.buildBottomUp]
  intro t ht
  simp only [LInv, Names.buildBottomUp, ↓reduceIte] at ht
  subst ht
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  have hk0 : Kp S g F s ra fr (s.pushRa ra) := Kp.init hm
  obtain ⟨lo, w, x0, u, x2, a3, a4, a5, a6, a7, a8, rfl, hlo⟩ := split2068 hfr
  have hS : (s.pushRa ra).regs.rdi.toBitVec = S := by simpa [MachineData.pushRa] using hpre.rdi
  have hsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
  -- The memory after each push.
  have h0 := hk0.mem
  rw [stk_frame] at h0
  unfold Top TopR at h0
  have h1 := wd_store' (a := rsp s - 16#64) (v := a8) (s.pushRa ra).regs.r15.toBitVec h0 (by ecancel)
  have h2 := wd_store' (a := rsp s - 24#64) (v := a7) (s.pushRa ra).regs.r14.toBitVec h1 (by ecancel)
  have h3 := wd_store' (a := rsp s - 32#64) (v := a6) (s.pushRa ra).regs.r13.toBitVec h2 (by ecancel)
  have h4 := wd_store' (a := rsp s - 40#64) (v := a5) (s.pushRa ra).regs.r12.toBitVec h3 (by ecancel)
  have h5 := wd_store' (a := rsp s - 48#64) (v := a4) (s.pushRa ra).regs.rbp.toBitVec h4 (by ecancel)
  have h6 := wd_store' (a := rsp s - 56#64) (v := a3) (s.pushRa ra).regs.rbx.toBitVec h5 (by ecancel)
  have h7 := get_of_eq (Q := View S g ∗ _) h6 (by ecancel)
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    simp only [hsp, sub_sub_ofNat, Nat.reduceAdd]; exact isSome_of_eq a8 h0 (by ecancel)
  case vc2 =>
    simp only [hsp, sub_sub_ofNat, Nat.reduceAdd]; exact isSome_of_eq a7 h1 (by ecancel)
  case vc3 =>
    simp only [hsp, sub_sub_ofNat, Nat.reduceAdd]; exact isSome_of_eq a6 h2 (by ecancel)
  case vc4 =>
    simp only [hsp, sub_sub_ofNat, Nat.reduceAdd]; exact isSome_of_eq a5 h3 (by ecancel)
  case vc5 =>
    simp only [hsp, sub_sub_ofNat, Nat.reduceAdd]; exact isSome_of_eq a4 h4 (by ecancel)
  case vc6 =>
    simp only [hsp, sub_sub_ofNat, Nat.reduceAdd]; exact isSome_of_eq a3 h5 (by ecancel)
  case vc7 =>
    simp only [hsp, hS, sub_sub_ofNat, Nat.reduceAdd]; exact isSome_n' h7
  case vc8 =>
    rename_i _ hz
    simp only [BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    cfg_goto
    · exact (Mid.push hk0.mem hlo hsp rfl rfl hS).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact fn_31 (Mid.push hk0.mem hlo hsp rfl rfl hS) hpre.ok hS rfl hz
    · loop_dec
  case vc9 =>
    rename_i _ hz
    simp only [BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    cfg_goto
    · exact (Mid.push hk0.mem hlo hsp rfl rfl hS).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact fn_26 (Mid.push hk0.mem hlo hsp rfl rfl hS) hpre.ok hpre.args hS rfl hz rfl
    · loop_dec
      exact Or.inl (fn_V (Mid.push hk0.mem hlo hsp rfl rfl hS) hpre.ok hpre.args rfl)

theorem b_26 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.26" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, h13, hlt, hH, hL⟩ := ht
  have hT : t.regs.r14.toBitVec.toNat < MAX_N := hH.f.lt_max hlt
  have hlen : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.r12.toBitVec + 32#64) 8).get!
      = g'.h.len := by
    rw [hM.r12]; exact rd_len' hM.mem
  have hd : BitVec.ofInt 64 (Mem.loadInt t.dmem
      (t.regs.r12.toBitVec + t.regs.r14.toBitVec * 8#64 + 56#64) 8).get!
      = Flat.get g'.h.dest t.regs.r14.toBitVec := by
    rw [hM.r12]; exact rd_dest' hM.mem hT
  have hB : Flat.kfin (Flat.body (flat g') t.regs.r14.toBitVec) = Flat.buildBottomUp (flat g) := by
    rw [← hL, Flat.loop_lt (st := flat g') hlt]
  kvcgen64
  all_goals try symexec_norm
  · rw [hM.r12]; exact isSome_len' hM.mem
  · rename_i hc
    simp only [hlen, Idioms.cf_sub, Bool.not_eq_true', decide_eq_false_iff_not] at hc
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, h13, hlen, hlt, hH, ?_⟩
      rw [← hB, Flat.body_eq, ite_eq_right]
      rintro ⟨h, -⟩; exact hc (BitVec.lt_def.mp h)
    · loop_dec
      simp only [H]
      exact Or.inr ⟨trivial, by decide⟩
  · rw [hM.r12]; exact isSome_dest' hM.mem hT
  · rename_i hc hq
    simp only [hlen, Idioms.cf_sub, Bool.not_eq_false', decide_eq_true_eq] at hc
    simp only [hd, BitVec.zero_eq, Idioms.sub_beq_zero, beq_iff_eq] at hq
    have hs : t.regs.r14.toBitVec < (flat g').size := BitVec.lt_def.mpr hc
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hH.succ hs, ?_⟩
      rw [← hB, Flat.body_eq, ite_eq_left ⟨hs, by simp [Flat.isFinal, flat, hq]⟩]
      rfl
    · loop_dec
      first
        | exact Or.inl (H_succ rfl hT (by decide))
        | exact H_succ rfl hT (by decide)
  · rename_i hc hq
    simp only [hlen, Idioms.cf_sub, Bool.not_eq_false', decide_eq_true_eq] at hc
    simp only [hd, BitVec.zero_eq, Idioms.sub_beq_zero, beq_eq_false_iff_ne] at hq
    simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, h13, hlen, hlt, hH, ?_⟩
    rw [← hB, Flat.body_eq, ite_eq_right]
    rintro ⟨-, h⟩
    simp [Flat.isFinal, flat] at h
    exact hq h
  · loop_dec
    simp only [H]
    exact Or.inr ⟨trivial, by decide⟩

theorem b_25 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.25" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hH, hL⟩ := ht
  have hn : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.r12.toBitVec + 8#64) 8).get! = g'.h.n := by
    rw [hM.r12]; exact rd_n' hM.mem
  kvcgen64
  all_goals try symexec_norm
  · rw [hM.r12]; exact isSome_n' hM.mem
  · rename_i hc
    simp only [hn, Idioms.cf_sub, Bool.not_eq_true', decide_eq_false_iff_not] at hc
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hn, ?_⟩
      rw [← hL]
      refine Flat.loop_ge ?_
      show ¬ t.regs.r14.toBitVec + 1#64 < g'.h.n
      rw [BitVec.add_comm, BitVec.lt_def]; exact hc
    · loop_dec
  · rename_i hc
    simp only [hn, Idioms.cf_sub, Bool.not_eq_false', decide_eq_true_eq] at hc
    simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hn, ?_, ?_, ?_⟩
    · show 1#64 + t.regs.r14.toBitVec < g'.h.n
      rw [BitVec.lt_def]; exact hc
    · show Flat.HInv (flat g') (1#64 + t.regs.r14.toBitVec) g'.xo
      rw [BitVec.add_comm]; exact hH
    · show Flat.loop (flat g') (1#64 + t.regs.r14.toBitVec) = _
      rw [BitVec.add_comm]; exact hL
  · loop_dec
    simp only [H, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

-- A load of the local array `A` after the store of `v` at the slot `i`.
private theorem rdA_store {S : Addr} {g' : G} {F : MProp 64} {s : MachineData} {ra : Int64}
    {x0 : Word} {x2 : Lc} {lo : List Word} {w u : Word} {t : MachineData}
    (h : Mid S g' F s ra x0 x2 lo w u t) {i : Nat} (hi : i < MAX_N) {a : Addr}
    (ha : a = rsp s - 8256#64 + BitVec.ofNat 64 (8 * i)) (v : Word) {j : Nat} (hj : j < MAX_N)
    {b : Addr} (hb : b = rsp s - 8256#64 + BitVec.ofNat 64 (8 * j)) :
    rd (t.dmem.storeInt a 8 v.toInt) b = (x2.A.set i v hi)[j] :=
  (h.storeA (P := { t with dmem := t.dmem.storeInt a 8 v.toInt }) hi ha v rfl rfl rfl).rdA hj hb

theorem b_27 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.27" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, h13, h15, hlt, hH, hK⟩ := ht
  have hpend : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.r12.toBitVec + 16440#64) 8).get!
      = g'.h.pend := by
    rw [hM.r12]; exact rd_pend' hM.mem
  -- The store of `NONE` to `8(%rsp)` keeps `pend`.
  have e1 : rd (Mem.storeInt t.dmem (t.regs.rsp.toBitVec + 8#64) 8 (-1)) (Fld.pendingGenerations S)
      = g'.h.pend :=
    Loop.rd_pend (hM.setU (P := { t with dmem := Mem.storeInt t.dmem (t.regs.rsp.toBitVec + 8#64) 8 (-1) })
      Flat.NONE rfl rfl rfl).mem
  kvcgen64
  all_goals try symexec_norm
  · rw [hM.r12]; exact isSome_pend' hM.mem
  · rename_i hp
    simp only [hpend, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hp
    have hp' : (flat g').pend = 0 := hp
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, t.regs.r14.toBitVec, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, h13, h15, hH,
        hp, ?_, hlt, ?_⟩
      · show BitVec.ofInt 64 _ = _
        rw [hpend]; exact hp
      · rw [← hK, Flat.kPend, ite_eq_left hp']
        split <;> rfl
    · loop_dec
  · exact hM.isSome_u
  · rename_i hp hc
    simp only [hpend, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hp
    have hp' : ¬ (flat g').pend = 0 := hp
    cfg_goto
    · exact hM.stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', Flat.NONE, ⟨x0, x2, lo, w, hM.setU Flat.NONE rfl rfl rfl, hok, hk⟩,
        ⟨h13, h15, hlt, hH, hp⟩, hlt, ?_⟩
      rw [← hK, Flat.kPend, ite_eq_right hp']
    · loop_dec
      simp only [H, e1, hM.rd_pend]
      omega
  · rename_i hp hc
    exfalso
    simp only [Idioms.cf_sub, decide_eq_false_iff_not, h13] at hc
    exact hc (BitVec.lt_def.mp hlt)

theorem b_0 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.0" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, T, ⟨x0, x2, lo, w, hM, hok, hk⟩, h13, h15, hH, hp, hdx, hTn, hR⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  · rename_i hc
    simp only [BitVec.zero_eq, Idioms.sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne, h13,
      h15] at hc
    have hc' : (flat g').size ≠ (flat g').targetSize := hc
    cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hk, by rw [hR, if_pos hc'],
        by rw [hR, if_pos hc']; rfl⟩
    · loop_dec
  · rename_i hc
    simp only [BitVec.zero_eq, Idioms.sub_beq_zero, Bool.not_eq_false', beq_iff_eq, h13, h15] at hc
    have hc' : (flat g').size = (flat g').targetSize := hc
    simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    refine ⟨g', u, T, x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk, h13, hc, ?_, hH, hp, ?_, ?_⟩
    · show t.regs.rdx.toBitVec < g'.h.n
      rw [hdx]; bv_omega
    · intro j _ hj
      change j < t.regs.rdx.toBitVec.toNat at hj
      simp [hdx] at hj
    · rw [hR, if_neg (fun h => h hc')]
  · loop_dec

theorem b_1 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s)
    (hperm : ∀ p, Sep.SpecW Names.permute permW (permuteA p) 1034 (permuteQ p)) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.1" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, T, x0, x2, lo, w, hM, hok, hk, h13, hln, hdx, hH, hp, hA, hR⟩ := ht
  have hn : g'.h.n.toNat ≤ 1024 := hok.n
  have hr : t.regs.rdx.toBitVec.toNat < 1024 := by bv_omega
  have hi : t.regs.rdx.toBitVec.toNat < MAX_N := by rw [Flat.max_n]; exact hr
  have hd : BitVec.ofInt 64 (Mem.loadInt t.dmem
      (t.regs.r12.toBitVec + t.regs.rdx.toBitVec * 8#64 + 56#64) 8).get!
      = Flat.get g'.h.dest t.regs.rdx.toBitVec := by
    rw [hM.r12]; exact rd_dest' hM.mem hi
  have ha : t.regs.rsp.toBitVec + t.regs.rdx.toBitVec * 8#64 + 16#64
      = rsp s - 8256#64 + BitVec.ofNat 64 (8 * t.regs.rdx.toBitVec.toNat) := by
    rw [hM.sp]; bv_omega
  have hlt : Flat.get g'.h.dest t.regs.rdx.toBitVec < g'.h.n :=
    hH.f.dest _ (show t.regs.rdx.toBitVec < g'.h.len by rw [hln]; exact hdx)
  -- The new entry at `rdx` and the old entries below `rdx`.
  have hset : ∀ j (hj : j < MAX_N), j < t.regs.rdx.toBitVec.toNat + 1 →
      (x2.A.set t.regs.rdx.toBitVec.toNat (BitVec.ofInt 64 (Mem.loadInt t.dmem
        (t.regs.r12.toBitVec + t.regs.rdx.toBitVec * 8#64 + 56#64) 8).get!) hi)[j]
        = Flat.get g'.h.dest (BitVec.ofNat 64 j) := by
    intro j hj hjl
    rw [Vector.getElem_set]
    split
    · rename_i e; subst e; rw [hd]; simp
    · exact hA j hj (by omega)
  obtain ⟨p0, hrd⟩ := Permute.rd_some_of_permOk (st := flat g') (Nat.le_trans hok.len hok.xs)
    (hH.f.permOk (hH.f.size_eq hp))
  have hperm := hperm p0
  simp only [Names.permute] at hperm
  kvcgen64 [hperm]
  all_goals try symexec_norm
  · rw [hM.r12]; exact isSome_dest' hM.mem hi
  · rename_i hc
    exfalso
    simp only [hd, BitVec.zero_eq, Idioms.sub_beq_zero, beq_iff_eq] at hc
    rw [hc] at hlt
    bv_omega
  · exact hM.isSomeA hi ha
  · rename_i hc _
    simp only [BitVec.zero_eq, Idioms.sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne,
      h13] at hc
    have e1 : (1#64 + t.regs.rdx.toBitVec).toNat = t.regs.rdx.toBitVec.toNat + 1 := by bv_omega
    cfg_goto
    · exact hM.stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, T, x0, _, lo, w, hM.storeA hi ha _ rfl rfl rfl, hok, hk, h13, hln, ?_, hH, hp,
        ?_, hR⟩
      · show 1#64 + t.regs.rdx.toBitVec < g'.h.n
        bv_omega
      · intro j hj hjl
        change j < (1#64 + t.regs.rdx.toBitVec).toNat at hjl
        exact hset j hj (by omega)
    · loop_dec
  · rename_i hc _
    simp only [BitVec.zero_eq, Idioms.sub_beq_zero, Bool.not_eq_false', beq_iff_eq, h13] at hc
    have e1 : g'.h.len.toNat = t.regs.rdx.toBitVec.toNat + 1 := by rw [hln, hc]; bv_omega
    have hs0 : t.regs.rsp.toBitVec + 16#64 = rsp s - 8256#64 := by rw [hM.sp]; bv_omega
    refine Mid.callW (hM.storeA hi ha ?v ?_ ?_ ?_) hM.r12 ?_ hok ?_ ?_
    case v => exact BitVec.ofInt 64 (Mem.loadInt t.dmem
      (t.regs.r12.toBitVec + t.regs.rdx.toBitVec * 8#64 + 56#64) 8).get!
    case refine_1 => exact rfl
    case refine_2 => exact rfl
    case refine_3 => exact rfl
    case refine_4 => exact hs0
    case refine_5 =>
      refine permuteA_of hok hH hp hrd fun j hj => ?_
      have hj' : j < MAX_N := by rw [Flat.max_n]; omega
      have ea : t.regs.rsp.toBitVec + 16#64 + BitVec.ofNat 64 (8 * j)
          = rsp s - 8256#64 + BitVec.ofNat 64 (8 * j) := by rw [hs0]
      have e := (rdA_store hM hi ha (BitVec.ofInt 64 (Mem.loadInt t.dmem
        (t.regs.r12.toBitVec + t.regs.rdx.toBitVec * 8#64 + 56#64) 8).get!) hj' ea).trans
        (hset j hj' (by omega))
      exact e
    case refine_6 =>
      intro t2 g'' L lo' w' _ hmid hQ hok' _
      obtain ⟨hk2, hfl, hal2⟩ := hQ
      kvcgen64
      all_goals try symexec_norm
      cfg_goto
      · exact (hmid.next rfl rfl rfl).stack
      · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
        exact ⟨g'', u, ⟨x0, L, lo', w', hmid.next rfl rfl rfl, hok', keep_trans hk hk2⟩,
          keep_trans hk hk2, by rw [hR, Permute.permuteMapping_of hrd]; exact hfl,
          by rw [hR, Permute.permuteMapping_of hrd]; exact hal2⟩
      · loop_dec

theorem b_2 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.2" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht

theorem b_31 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.31" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, h13, hR⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  · rw [hM.r12]; exact isSome_len' hM.mem
  · cfg_goto
    · exact (hM.next rfl rfl rfl).stack
    · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
      refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hk, by rw [hR]; split <;> rfl, ?_⟩
      rw [hR]
      simp only [hM.r12, rd_len' hM.mem, h13, al, rax]
      by_cases hc : g'.h.len = g'.h.n
      · simp [hc, flat, code, al_add_self]
      · simp [hc, flat, code, al_add_self, beq_false_of_ne hc]
    · loop_dec

theorem b_13 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.13" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hQ⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  · exact isSome_pop' hM (k := 0) (by decide) (by bv_omega)
  · exact isSome_pop' hM (k := 1) (by decide) (by bv_omega)
  · exact isSome_pop' hM (k := 2) (by decide) (by bv_omega)
  · exact isSome_pop' hM (k := 3) (by decide) (by bv_omega)
  · exact isSome_pop' hM (k := 4) (by decide) (by bv_omega)
  · exact isSome_pop' hM (k := 5) (by decide) (by bv_omega)
  · refine (congrArg Option.isSome (hM.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).retAddr).trans rfl
    all_goals rfl
  · refine Kp.ret (hM.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by
      simp only [List.length_cons, List.length_append, Vector.length_toList, List.length_nil, hM.len]
      rfl) hok fun t' _ hax =>
      ⟨hQ.1, hQ.2.1, by show (rax t').setWidth 8 = _; rw [hax]; exact hQ.2.2⟩
    all_goals rfl

theorem b_28 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.28" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hR⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  cfg_goto
  · exact (hM.next rfl rfl rfl).stack
  · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hk, by rw [hR], by rw [hR]; rfl⟩
  · loop_dec

theorem b_29 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.29" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hR⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  cfg_goto
  · exact (hM.next rfl rfl rfl).stack
  · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hk, by rw [hR], by rw [hR]; rfl⟩
  · loop_dec

theorem b_30 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.30" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hR⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  cfg_goto
  · exact (hM.next rfl rfl rfl).stack
  · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    exact ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, hk, by rw [hR], by rw [hR]; rfl⟩
  · loop_dec

theorem b_24 [Host] [FunDecls] (S g F s ra) (_hpre : Sep.Pre S g F loopA 2068 s) :
    Program.ForallBlocks loopAsm fun blk => blk.label = .label ".LB.Emission.buildBottomUp.24" →
      Obl S g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', u, ⟨x0, x2, lo, w, hM, hok, hk⟩, hrax, hlt, hH, hL⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  · simp only [LInv, Names.buildBottomUp, String.reduceEq, ↓reduceIte]
    refine ⟨g', u, ⟨x0, x2, lo, w, hM.next rfl rfl rfl, hok, hk⟩, ?_, ?_⟩
    · show Flat.HInv (flat g') (t.regs.rax.toBitVec + 1#64) g'.xo
      rw [hrax]; exact hH
    · show Flat.loop (flat g') (t.regs.rax.toBitVec + 1#64) = _
      rw [hrax]; exact hL
  · loop_dec
    rw [hrax]
    exact Or.inl (H_succ rfl (lt_1024 hH.f hlt) (by decide))

end Loop
end Bbu.Unit
