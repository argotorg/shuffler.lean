module

public import FlatShuffler.Unit.ExitDefs
import all FlatShuffler.Unit.ExitDefs
public import FlatShuffler.Sep.Stores
import all FlatShuffler.Sep.Stores
public import ProofKit.Cfg
import all ProofKit.Cfg

@[expose] public section

/-!
# `dup`

`Names.dup` in `build/kraken/c/build_bottom_up.S`: one stack word for alignment. If the slot at `copy` is not a return label, it stores
the operation to record `traceSize`, copies `m_stack[copy]` to `m_stack[size]`, increments the
two counters, and then binds the new slot to the destination if `m_positionOf[destination]` is
`-1`.

The caller is `produce`. The copy is a result of `shallowestCopyPosition` that is not `-1`, so it
is below `size ≤ n`; the destination is `t < n`; `produceA` gives `len < n` and `nops < 6n`
(`dupA`). `produce` uses the flat result (`dupQ`).

The two assertion paths call `exit(1)`. A used destination retains the record and stack
copy made before the check. The two free stack words cover alignment and the call return slot.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit

open FlatShuffler.Sep

namespace Dup

/-! ## Words and flags -/

-- `leaq 1(%r)` below a bound does not wrap.
theorem succ_le {x : Word} {b : Nat} (h : x.toNat < b) : (x + 1#64).toNat ≤ b := by
  bv_omega

-- `cmp`: `zf` is set iff the two values are equal.
theorem sub_beq_zero {w : Nat} (x y : BitVec w) : (x - y == BitVec.zero w) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.zero_eq, BitVec.sub_eq_iff_eq_add,
    BitVec.zero_add]

-- `movl %edx, %eax`: `al` is the low byte of `edx`.
theorem al_movl (x : Word) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (x.take 32)) = BitVec.setWidth 8 x := by
  ext i hi; simp [BitVec.take]; omega

/-! ## The buffers of the flat state -/

theorem get_vec {α : Type} [Inhabited α] {l : List α} {i : Word} (hi : i.toNat < l.length)
    (hl : l.length ≤ MAX_N) : Flat.get (vec l) i = l[i.toNat] := by
  simp [Flat.get, vec, Nat.lt_of_lt_of_le hi hl, hi]

theorem vec_set {α : Type} [Inhabited α] {l : List α} {i : Nat} (hi : i < l.length) (x : α) :
    vec (l.set i x) = (vec l).setIfInBounds i x := by
  ext j hj
  simp only [vec, Vector.getElem_ofFn, Vector.getElem_setIfInBounds, List.getElem?_set, hi]
  split <;> simp

theorem put_eq {α : Type} (v : Vector α MAX_N) {i : Word} (hi : i.toNat < MAX_N) (x : α) :
    Flat.put v i x = v.set i.toNat x hi := by
  ext j hj; simp [Flat.put, Vector.getElem_set, Vector.getElem_setIfInBounds]

theorem get_data {g : G} (hok : g.Ok) {c : Word} (hc : c.toNat < g.h.n.toNat) :
    Flat.get (flat g).data c = StackSlot.ofWord g.stk[c.toNat] := by
  rw [flat, get_vec (by simpa using Nat.lt_add_right g.xs hc) (by simpa using hok.xs)]
  simp

-- The records below `N + 1` after a store to record `N`.
theorem trace_set {n N : Nat} (ops : Vector OpR n) (hN : N < n) (r : OpR) :
    ((ops.set N r hN).toList.take (N + 1)).map OpR.op
      = (ops.toList.take N).map OpR.op ++ [r.op] := by
  rw [Vector.toList_set, List.take_add_one, List.take_set,
    List.set_eq_of_length_le (List.length_take_le _ _), List.getElem?_set_self (by simpa using hN)]
  simp

/-! ## The three results of `Flat.dup` -/

theorem none_eq : Flat.NONE = 18446744073709551615#64 := rfl

-- `cmpb $3, 4(%rdi,%rsi,8); je .LB.Emission.dup.0`: the copy is a return label.
theorem dup_frl {g : G} (hok : g.Ok) {c d : Word} (hc : c.toNat < g.h.n.toNat)
    (h : (BitVec.extractLsb' 32 8 g.stk[c.toNat] - 3#8 == BitVec.zero 8) = true) :
    Flat.dup (flat g) c d = (.assertionFailed, flat g) := by
  rw [sub_beq_zero, decide_eq_true_iff] at h
  have : (Flat.get (flat g).data c).kind = FunctionReturnLabel := by
    rw [get_data hok hc]; exact h
  simp [Flat.dup, this]

theorem dup_nfrl {g : G} (hok : g.Ok) {c d : Word} (hc : c.toNat < g.h.n.toNat)
    (h : (BitVec.extractLsb' 32 8 g.stk[c.toNat] - 3#8 == BitVec.zero 8) = false) :
    Flat.dup (flat g) c d =
      let st := Flat.stackDup (flat g) c
      if Flat.get st.pos d ≠ Flat.NONE then (.assertionFailed, st)
      else (.done, Flat.bind st (st.size - 1) d) := by
  rw [sub_beq_zero, decide_eq_false_iff_not] at h
  have : ¬(Flat.get (flat g).data c).kind = FunctionReturnLabel := by
    rw [get_data hok hc]; exact h
  simp only [Flat.dup, this, ↓reduceIte]

theorem pos_dup {g : G} {c d : Word} (hd : d.toNat < MAX_N) :
    Flat.get (Flat.stackDup (flat g) c).pos d = g.h.pos[d.toNat] := by
  simp [Flat.get, Flat.stackDup, flat, hd]

-- `cmpq $-1, 8248(%rax,%rcx,8); jne .LB.Emission.dup.0`: the destination is used.
theorem dup_used {g : G} (hok : g.Ok) {c d : Word} (hc : c.toNat < g.h.n.toNat)
    (hd : d.toNat < MAX_N)
    (h : (BitVec.extractLsb' 32 8 g.stk[c.toNat] - 3#8 == BitVec.zero 8) = false)
    (hp : (!(g.h.pos[d.toNat] - 18446744073709551615#64 == BitVec.zero 64)) = true) :
    Flat.dup (flat g) c d = (.assertionFailed, Flat.stackDup (flat g) c) := by
  rw [sub_beq_zero, Bool.not_eq_true', decide_eq_false_iff_not, ← none_eq] at hp
  rw [dup_nfrl hok hc h]
  simp only [pos_dup hd, ne_eq, hp, not_false_eq_true, ↓reduceIte]

-- The fall-through: the destination is free.
theorem dup_done {g : G} (hok : g.Ok) {c d : Word} (hc : c.toNat < g.h.n.toNat)
    (hd : d.toNat < MAX_N)
    (h : (BitVec.extractLsb' 32 8 g.stk[c.toNat] - 3#8 == BitVec.zero 8) = false)
    (hp : (!(g.h.pos[d.toNat] - 18446744073709551615#64 == BitVec.zero 64)) = false) :
    Flat.dup (flat g) c d = (.done, Flat.bind (Flat.stackDup (flat g) c) g.h.len d) := by
  rw [sub_beq_zero, Bool.not_eq_false', decide_eq_true_iff, ← none_eq] at hp
  rw [dup_nfrl hok hc h]
  simp only [pos_dup hd, ne_eq, hp, not_true_eq_false, ↓reduceIte]
  exact congrArg (fun L => (Flat.Status.done, Flat.bind _ L d)) (BitVec.add_sub_cancel _ _)

/-! ## The ghosts after the stores -/

-- The record of `dup`: `Op.dupW` of the depth `size - 1 - copy + 1`.
theorem dupW_eq (L c : Word) :
    Op.dupW (L - 1 - c + 1) = ⟨1#8, BitVec.extractLsb' 0 8 (L - c), ⟨0#32, 1#8, 5#8⟩⟩ := by
  have e : L - 1 - c + 1 = L - c := by bv_omega
  rw [Op.dupW, e]
  simp [Dup, StackSlot.junk, Junk, Unreachable]
  ext i hi; simp

-- The ghost after the record, the copy and the size: `Stack::dup`.
theorem flat_dup {g : G} (hok : g.Ok) {c : Word} (hc : c.toNat < g.h.n.toNat)
    (hL : g.h.len.toNat < g.h.n.toNat) (hN : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo) :
    flat { h := { g.h with len := g.h.len + 1#64, nops := g.h.nops + 1#64 },
           xs := g.xs, xo := g.xo,
           stk := g.stk.set g.h.len.toNat g.stk[c.toNat] (Nat.lt_add_right _ hL),
           ops := g.ops.set g.h.nops.toNat
             ⟨⟨1#8, BitVec.extractLsb' 0 8 (g.h.len - c), ⟨0#32, 1#8, 5#8⟩⟩,
               g.ops[g.h.nops.toNat].pad2, g.ops[g.h.nops.toNat].pad10⟩ hN,
           tgt := g.tgt, spl := g.spl }
      = Flat.stackDup (flat g) c := by
  have hn := hok.n
  have hx := hok.xo
  have e : (g.h.nops + 1#64).toNat = g.h.nops.toNat + 1 := by
    simp only [MAX_N] at hn hx; bv_omega
  simp only [flat, Flat.stackDup, Flat.put, Flat.St.mk.injEq, true_and, and_true]
  refine ⟨?_, rfl, ?_⟩
  · rw [Vector.toList_set, List.map_set, vec_set (by simpa using Nat.lt_add_right g.xs hL)]
    exact congrArg _ (get_data hok hc).symm
  · rw [e, trace_set, dupW_eq]

-- `Mapping::bind`: the two stores of the fall-through.
theorem flat_bind (g : G) {L d : Word} (hL : L.toNat < MAX_N) (hd : d.toNat < MAX_N) :
    flat { g with h := { g.h with dest := g.h.dest.set L.toNat d hL,
                                  pos := g.h.pos.set d.toNat L hd } }
      = Flat.bind (flat g) L d := by
  simp only [flat, Flat.bind, put_eq _ hL, put_eq _ hd]

-- The ghost after `dup`: `Stack::dup` and `Mapping::bind`.
theorem flat_dup_bind {g : G} (hok : g.Ok) {c d : Word} (hc : c.toNat < g.h.n.toNat)
    (hL : g.h.len.toNat < g.h.n.toNat) (hN : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo)
    (hLM : g.h.len.toNat < MAX_N) (hd : d.toNat < MAX_N) :
    flat { h := { g.h with len := g.h.len + 1#64, nops := g.h.nops + 1#64,
                           dest := g.h.dest.set g.h.len.toNat d hLM,
                           pos := g.h.pos.set d.toNat g.h.len hd },
           xs := g.xs, xo := g.xo,
           stk := g.stk.set g.h.len.toNat g.stk[c.toNat] (Nat.lt_add_right _ hL),
           ops := g.ops.set g.h.nops.toNat
             ⟨⟨1#8, BitVec.extractLsb' 0 8 (g.h.len - c), ⟨0#32, 1#8, 5#8⟩⟩,
               g.ops[g.h.nops.toNat].pad2, g.ops[g.h.nops.toNat].pad10⟩ hN,
           tgt := g.tgt, spl := g.spl }
      = Flat.bind (Flat.stackDup (flat g) c) g.h.len d := by
  rw [← flat_dup hok hc hL hN, ← flat_bind _ hLM hd]

-- The slot address fold can occur before the field address fold.
theorem slot_pos (S : Addr) (i : Nat) :
    slotAt S i + 8248#64 = Fld.mapping_positionOf S i := by
  unfold slotAt Fld.mapping_positionOf
  ac_rfl

-- The size reload before `leaq 1` is the size in the view.
theorem bump_len {m : Mem 64} {a : Addr} {v : Word} (h : rd m a = v) :
    Mem.storeInt m a 8 (rd m a + 1#64).toInt = Mem.storeInt m a 8 (v + 1#64).toInt :=
  congrArg (fun w : Word => Mem.storeInt m a 8 (w + 1#64).toInt) h

-- Undo the alignment word in a state used by `Kp`.
def unpad (t : MachineData) : MachineData :=
  { t with regs := t.regs.set64 .rsp (t.regs.get64 .rsp + 8#64) }

end Dup

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem dup_unit [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels dupAsm, label l ≠ label "exit") :
    UnitThmWithExit dupAsm dupA 2 dupQ dupX := by
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  obtain ⟨x, y, rfl⟩ : ∃ x y, fr = [x, y] := by
    match fr, hfr with
    | [x, y], _ => exact ⟨x, y, rfl⟩
  have hk0 : Kp S g F s ra [x, y] (s.pushRa ra) := Kp.init hm
  have he := ProofKit.external_call_spec "exit" hexit
  have hcN : s.regs.rsi.toBitVec.toNat < g.h.n.toNat + g.xs := Nat.lt_add_right _ hpre.args.1
  have hdN : s.regs.rdx.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hpre.args.2.2.2 hpre.ok.n
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t =>
        if l = Names.dup then t = s.pushRa ra
        else if l = ".LB.Emission.dup.0" then
          Kp S g F s ra [x, y] (Dup.unpad t) ∧
          ((g.stk[(rsi s).toNat]'hcN |>.extractLsb' 32 8) - 3#8 == BitVec.zero 8) = true
        else if l = ".LB.Emission.dup.1" then
          ∃ g', Kp S g' F s ra [x, y] (Dup.unpad t) ∧ g'.Ok ∧ Keep g g'
            ∧ flat g' = Flat.stackDup (flat g) (rsi s)
            ∧ rax t = S ∧ rdx t = rdx s ∧ rcx t = g.h.len
            ∧ ((g.stk[(rsi s).toNat]'hcN |>.extractLsb' 32 8) - 3#8 == BitVec.zero 8) = false
            ∧ (g.h.pos[(rdx s).toNat]'hdN - 18446744073709551615#64 == BitVec.zero 64) = true
        else False
      | .exit, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht =>
    subst ht
    kvcgen64
    simp only [Names.dup, ↓reduceIte]
  case «.LB.Emission.dup.0» t ht =>
    simp only [Names.dup, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨hk, hkind⟩ := ht
    have hsp : t.regs.rsp.toBitVec + 8#64 = rsp s - 8#64 := by
      exact congrArg UInt64.toBitVec hk.sp
    have haddr : t.regs.rsp.toBitVec - 8#64 = rsp s - 24#64 := by bv_omega
    have hmem := Stk.two (rsp s) x y ra.toBitVec _ F ▸ hk.mem
    dsimp only [Dup.unpad] at hmem
    kvcgen64 [he]
    all_goals symexec_norm
    vc_by_shape
    | load => simpa only [haddr] using Wd.isSome hmem
    | jumpOut =>
      rename_i exitra _
      refine Or.inr ⟨Or.inr ⟨rfl, rfl, ?_⟩, ?_⟩
      · refine ⟨g, [exitra.toBitVec, y], ra.toBitVec, ?_, hpre.ok, rfl, ?_⟩
        · change ExitRes (Flat.dup · (rsi s) (rdx s)) g g
          dsimp only [ExitRes]
          rw [Dup.dup_frl hpre.ok hpre.args.1 hkind]
          exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
        · rw [Stk.two]
          change (Wd (rsp s - 24#64) exitra.toBitVec ∗ _).get
            (Mem.storeInt _ (t.regs.rsp.toBitVec - 8#64) 8 exitra.toBitVec.toInt)
          rw [haddr]
          exact Wd.store hmem exitra.toBitVec
      · intro l hl ha
        exact False.elim (hout l hl ha)
  case «.LB.Emission.dup.1» t ht =>
    simp only [Names.dup, String.reduceEq, ↓reduceIte] at ht
    obtain ⟨g', hk, hok, hkeep, hf, ha, hd, hc, hkind, hpos⟩ := ht
    have hLM := Nat.lt_of_lt_of_le hpre.args.2.1 hpre.ok.n
    have hdM := Nat.lt_of_lt_of_le hpre.args.2.2.2 hpre.ok.n
    have hsp : UInt64.ofBitVec (8#64 + t.regs.rsp.toBitVec) = (s.pushRa ra).regs.rsp := by
      rw [BitVec.add_comm]
      exact hk.sp
    have hdone := Dup.dup_done hpre.ok hpre.args.1 hdN hkind
      (show (!(g.h.pos[(rdx s).toNat]'hdN - 18446744073709551615#64 == BitVec.zero 64)) = false from
        congrArg Bool.not hpos)
    have hmem0 := hk.mem
    dsimp only [Dup.unpad] at hmem0
    have hmem1 := View.store_dest hmem0 hLM s.regs.rdx.toBitVec
    have hmem2 := View.store_pos hmem1 hdN g.h.len
    dsimp only at hmem1 hmem2
    kvcgen64
    all_goals symexec_norm
    all_goals try simp only [ha, hd, hc, Fld.fold_mapping_destinationOf,
      Fld.fold_mapping_positionOf]
    vc_by_shape
    | load => view_load
    | retAddr =>
      exact Option.isSome_iff_exists.mpr
        ⟨ra, Kp.retAddr ⟨hmem2, hsp, hk.bx, hk.bp, hk.r12, hk.r13, hk.r14, hk.r15⟩⟩
    | ret =>
      refine ProofKit.intercept_mono_exit
        (E := fun a t => a = ra ∧ Sep.Post S F 2 (fun g' t => dupQ g g' s t) s t
          ∧ Sep.mod.Agree s t) ?_ (fun h => Or.inl h)
      refine Kp.ret ⟨hmem2, hsp, hk.bx, hk.bp, hk.r12, hk.r13, hk.r14, hk.r15⟩ rfl
        (Keep.ok (g := g') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok hok.len hok.nops) ?_
      intro t' _ hax
      refine ⟨?_, ?_⟩
      · refine ⟨⟨hkeep.tgtp, hkeep.n, hkeep.splp, hkeep.data, hkeep.ops,
          hkeep.xs, hkeep.xo, hkeep.tgt, hkeep.spl⟩, ?_, ?_⟩
        · dsimp only [rsi, rdx, Reg64s.get64_rsi, Reg64s.get64_rdx] at hf ⊢
          rw [hdone, Dup.flat_bind g' (d := s.regs.rdx.toBitVec) hLM hdN, hf]
        · dsimp only [rsi, rdx, Reg64s.get64_rsi, Reg64s.get64_rdx] at hf ⊢
          rw [hdone]
          show (rax t').setWidth 8 = 0#8
          rw [hax]; rfl
      · show (rax t').setWidth 8 ≠ 2#8
        rw [hax]; change 0#8 ≠ 2#8; decide
  case «_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_» t ht =>
    simp only [Names.dup, ↓reduceIte] at ht
    subst ht
    have hS : (s.pushRa ra).regs.rdi.toBitVec = S := by simpa [MachineData.pushRa] using hpre.rdi
    let c := (s.pushRa ra).regs.rsi.toBitVec
    let d := (s.pushRa ra).regs.rdx.toBitVec
    have hC : (s.pushRa ra).regs.rsi.toBitVec = c := rfl
    have hD : (s.pushRa ra).regs.rdx.toBitVec = d := rfl
    have hcs : rsi s = c := hC
    have hds : rdx s = d := hD
    obtain ⟨hc, hL, hN, hd⟩ := hpre.args
    rw [hcs] at hc
    rw [hds] at hd
    have hok := hpre.ok
    have hdM : d.toNat < MAX_N := Nat.lt_of_lt_of_le hd hok.n
    have hLM : g.h.len.toNat < MAX_N := Nat.lt_of_lt_of_le hL hok.n
    -- The loads of the entry memory.
    have h0 := hk0.mem
    have rD : BitVec.ofInt 64 (Mem.loadInt (s.pushRa ra).dmem (Fld.stack_data S) 8).get!
      = g.h.data := View.rd_data h0
    have rL : BitVec.ofInt 64 (Mem.loadInt (s.pushRa ra).dmem (Fld.stack_size S) 8).get!
      = g.h.len := View.rd_len h0
    have rN : BitVec.ofInt 64 (Mem.loadInt (s.pushRa ra).dmem (Fld.stack_traceSize S) 8).get!
      = g.h.nops := View.rd_nops h0
    have rK : BitVec.ofInt 8 (Mem.loadInt (s.pushRa ra).dmem (slotAt g.h.data c.toNat + 4#64) 1).get!
      = g.stk[c.toNat].extractLsb' 32 8 := View.rdb_slot h0 (Nat.lt_add_right _ hc) (j := 4) (by decide)
    -- `traceSize + 1`, then the 5 stores of the record.
    have h2 := View.store_nops h0 (g.h.nops + 1#64)
    have rO := View.rd_ops h2
    dsimp only [rd] at rO
    have h3 := View.focus h2 (i := g.h.nops.toNat) hN
    dsimp only at h3
    have h3a := OpM.store_kind h3 1
    have h3b := OpM.store_depth h3a (BitVec.extractLsb' 0 8 (g.h.len - c)).toInt
    have h3c := OpM.store_payload h3b 0
    have h3d := OpM.store_skind h3c 1
    have h3e : (OpM (Sep.opAt g.h.ops g.h.nops.toNat)
        ⟨⟨BitVec.ofInt 8 1, BitVec.ofInt 8 (BitVec.extractLsb' 0 8 (g.h.len - c)).toInt,
          ⟨BitVec.ofInt 32 0, BitVec.ofInt 8 1, BitVec.ofInt 8 5⟩⟩,
          g.ops[g.h.nops.toNat].pad2, g.ops[g.h.nops.toNat].pad10⟩ ∗ _).get _ :=
      OpM.store_sop h3d 5
    have h4 := View.unfocus (g := { g with h := { g.h with nops := g.h.nops + 1#64 } }) h3e hN
    have rD4 := View.rd_data h4
    have rL4 := View.rd_len h4
    have rC4 := View.rd_slot h4 (Nat.lt_add_right _ hc)
    dsimp only [rd] at rD4 rL4 rC4
    -- The copy and `size + 1`.
    have h7 := View.store_stk h4 (i := g.h.len.toNat) (Nat.lt_add_right _ hL) g.stk[c.toNat]
    have rL7 := View.rd_len h7
    dsimp only [rd] at rL7
    have h9 := View.store_len h7 (g.h.len + 1#64)
    have rP9 := View.rd_pos h9 hdM
    dsimp only [rd] at rP9
    -- `bind`.
    have hmlen := Dup.bump_len rL7
    have h9actual := hmlen.symm ▸ h9
    have rP9actual := hmlen.symm ▸ rP9
    have h9x := Stk.two (rsp s) x y ra.toBitVec _ F ▸ h9actual
    have haddr : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 = rsp s - 24#64 := by
      change rsp s - 8#64 - 8#64 - 8#64 = rsp s - 24#64
      bv_omega
    let gd : G := { g with
      h := { g.h with len := g.h.len + 1#64, nops := g.h.nops + 1#64 },
      stk := g.stk.set g.h.len.toNat (g.stk[c.toNat]'(Nat.lt_add_right _ hc)) (Nat.lt_add_right _ hL),
      ops := g.ops.set g.h.nops.toNat
        ⟨⟨1#8, BitVec.extractLsb' 0 8 (g.h.len - c), ⟨0#32, 1#8, 5#8⟩⟩,
          (g.ops[g.h.nops.toNat]'hN).pad2, (g.ops[g.h.nops.toNat]'hN).pad10⟩ hN }
    have hgdok : gd.Ok := Keep.ok (g := g) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok
      (Nat.le_add_right_of_le (Dup.succ_le hL)) (Dup.succ_le hN)
    kvcgen64 [he]
    all_goals try symexec_norm
    all_goals try simp only [hS, hC, hD,
      Fld.fold_mapping_positionOf]
    all_goals try simp only [Fld.fold_stack_data, Fld.fold_stack_size, Fld.fold_stack_trace,
      Fld.fold_stack_traceSize, fold_slot, fold_op, rD, rL, rN, rK, rO, rD4, rL4, rC4]
    all_goals try rw [Dup.slot_pos]
    vc_by_shape
    | load =>
      first
      | view_load
      | with_reducible exact View.isSome_len h7
      | with_reducible exact View.isSome_slot_byte h0 (Nat.lt_add_right _ hc) (j := 4) (by decide)
      | rw [haddr]; exact Wd.isSome h9x
      | exact View.isSome_pos h9actual hdM
    | closed => decide
    | goto ".LB.Emission.dup.0" =>
      rename_i hkind
      simp only [hS, hC, Fld.fold_stack_data, fold_slot, rD, rK] at hkind
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        symexec_norm
        have hs : ∀ a : Word, a - (a - 8#64) = 8#64 := by intro a; bv_omega
        rw [hs]
        decide
      · simp only [Names.dup, String.reduceEq, ↓reduceIte]
        refine ⟨⟨h0, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
        · change UInt64.ofBitVec (_ - 8#64 + 8#64) = _
          rw [BitVec.sub_add_cancel]
        · exact ‹_›
      · simp
    | goto ".LB.Emission.dup.1" =>
      rename_i hkind hpos
      simp only [hS, hC, hD,
        Fld.fold_stack_data, Fld.fold_stack_size, Fld.fold_stack_trace,
        Fld.fold_stack_traceSize, fold_slot, fold_op, rD, rL, rN, rK, rO, rD4, rL4,
        rC4] at hkind hpos
      simp only [Dup.slot_pos] at hpos
      have hpos' := (congrArg
        (fun v : Word => v - 18446744073709551615#64 == BitVec.zero 64) rP9actual).symm.trans hpos
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        symexec_norm
        have hs : ∀ a : Word, a - (a - 8#64) = 8#64 := by intro a; bv_omega
        rw [hs]
        decide
      · simp only [Names.dup, String.reduceEq, ↓reduceIte, hcs, hds]
        refine ⟨gd, ⟨h9actual, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩, hgdok,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          Dup.flat_dup hok hc hL hN, hpre.rdi, rfl, rL7, ‹_›, hpos' ⟩
        change UInt64.ofBitVec (_ - 8#64 + 8#64) = _
        rw [BitVec.sub_add_cancel]
      · simp
    | jumpOut =>
      rename_i exitra _ hkind hused
      simp only [hS, hC, hD,
        Fld.fold_stack_data, Fld.fold_stack_size, Fld.fold_stack_trace,
        Fld.fold_stack_traceSize, fold_slot, fold_op, rD, rL, rN, rK, rO, rD4, rL4,
        rC4] at hkind hused
      simp only [Dup.slot_pos] at hused
      have hused' := (congrArg
        (fun v : Word => v - 18446744073709551615#64 == BitVec.zero 64) rP9actual).symm.trans hused
      refine Or.inr ⟨Or.inr ⟨rfl, rfl, ?_⟩, ?_⟩
      · refine ⟨gd, [exitra.toBitVec, y], ra.toBitVec, ?_, hgdok, rfl, ?_⟩
        · change ExitRes (Flat.dup · (rsi s) (rdx s)) g gd
          dsimp only [ExitRes]
          change Keep g gd ∧ flat gd = (Flat.dup (flat g) c d).2 ∧
            (Flat.dup (flat g) c d).1 = .assertionFailed
          rw [Dup.dup_used hok hc hdM hkind (congrArg Bool.not hused')]
          exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
            Dup.flat_dup hok hc hL hN, rfl⟩
        · rw [Stk.two]
          change (Wd (rsp s - 24#64) exitra.toBitVec ∗ _).get
            (Mem.storeInt _ ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64) 8 exitra.toBitVec.toInt)
          rw [haddr]
          exact Wd.store h9x exitra.toBitVec
      · intro l hl ha
        exact False.elim (hout l hl ha)

end FlatShuffler.Unit
