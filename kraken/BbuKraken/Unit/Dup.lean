import BbuKraken.Unit.Defs
import BbuKraken.Sep.Stores
import ProofKit.Cfg

/-!
# `dup`

`c/bbu/<Names.dup>.S`: no frame, no call. If the slot at `copy` is not a return label, it stores
the operation to record `traceSize`, copies `m_stack[copy]` to `m_stack[size]`, increments the
two counters, and then binds the new slot to the destination if `m_positionOf[destination]` is
`-1`.

The caller is `produce`. The copy is a result of `shallowestCopyPosition` that is not `-1`, so it
is below `size ≤ n`; the destination is `t < n`; `produceA` gives `len < n` and `nops < 6n`
(`dupA`). `produce` uses the flat result (`dupQ`).

The proof has one block for the body and one for `.LB.Emission.dup.0` (`movl %edx, %eax; ret`). The invariant
of `.LB.Emission.dup.0` is the result: a ghost `g'` in the memory, `edx` the code of the `Status`. The three
jumps to `.LB.Emission.dup.0` are the return label (`g' = g`), a used destination (`g'` after `Stack::dup`) and
the fall-through (`g'` after `Stack::dup` and `Mapping::bind`). The body names each store of the
view (`View.store_*`, `OpM.store_*`) before `kvcgen64`, so each load and each exit has its view.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

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

end Dup

theorem dup_unit [Host] [FunDecls] : UnitThm dupAsm dupA 0 dupQ := by
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  obtain rfl : fr = [] := List.eq_nil_of_length_eq_zero hfr
  have hk0 : Kp S g F s ra [] (s.pushRa ra) := Kp.init hm
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label l, t =>
        if l = Names.dup then t = s.pushRa ra
        else if l = ".LB.Emission.dup.0" then ∃ g', Kp S g' F s ra [] t ∧ g'.Ok ∧ Keep g g'
          ∧ flat g' = (Flat.dup (flat g) (rsi s) (rdx s)).2
          ∧ (rdx t).setWidth 8 = code (Flat.dup (flat g) (rsi s) (rdx s)).1
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
    obtain ⟨g', hk, hok', hkeep, hflat, hcode⟩ := ht
    kvcgen64
    vc_by_shape
    | retAddr =>
      exact Option.isSome_iff_exists.mpr
        ⟨ra, Kp.retAddr (hk.next rfl rfl rfl rfl rfl rfl rfl rfl)⟩
    | ret =>
      exact Kp.ret (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) rfl hok' fun t' _ hax =>
        ⟨hkeep, hflat, by show (rax t').setWidth 8 = _; rw [hax]; exact (Dup.al_movl _).trans hcode⟩
  case «_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_» t ht =>
    simp only [Names.dup, ↓reduceIte] at ht
    subst ht
    have hS : (s.pushRa ra).regs.rdi.toBitVec = S := by simpa [MachineData.pushRa] using hpre.rdi
    obtain ⟨c, hC⟩ : ∃ c, (s.pushRa ra).regs.rsi.toBitVec = c := ⟨_, rfl⟩
    obtain ⟨d, hD⟩ : ∃ d, (s.pushRa ra).regs.rdx.toBitVec = d := ⟨_, rfl⟩
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
    have h10 := View.store_dest h9 hLM d
    have h11 := View.store_pos h10 hdM g.h.len
    kvcgen64
    all_goals try symexec_norm
    all_goals try simp only [hS, hC, hD, Fld.fold_mapping_destinationOf,
      Fld.fold_mapping_positionOf] at *
    all_goals try simp only [Fld.fold_stack_data, Fld.fold_stack_size, Fld.fold_stack_trace,
      Fld.fold_stack_traceSize, fold_slot, fold_op, rD, rL, rN, rK, rO, rD4, rL4, rC4, rL7,
      rP9] at *
    vc_by_shape
    | load =>
      first
      | view_load
      | with_reducible exact View.isSome_slot_byte h0 (Nat.lt_add_right _ hc) (j := 4) (by decide)
    | closed => decide
    | goto ".LB.Emission.dup.0" =>
      cfg_goto
      · exact hk0.stack
      · simp only [Names.dup, String.reduceEq, ↓reduceIte, hcs, hds]
        first
        | rw [Dup.dup_frl hok hc ‹_›]
          exact ⟨g, hk0.next rfl rfl rfl rfl rfl rfl rfl rfl, hok,
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
        | rw [Dup.dup_used hok hc hdM ‹_› ‹_›]
          exact ⟨_, ⟨h9, hk0.sp, hk0.bx, hk0.bp, hk0.r12, hk0.r13, hk0.r14, hk0.r15⟩,
            Keep.ok (g := g) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok (Nat.le_add_right_of_le (Dup.succ_le hL))
              (Dup.succ_le hN),
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Dup.flat_dup hok hc hL hN, rfl⟩
      · simp
    | other =>
      simp only [Names.dup, String.reduceEq, ↓reduceIte, hcs, hds]
      rw [Dup.dup_done hok hc hdM ‹_› ‹_›]
      exact ⟨_, ⟨h11, hk0.sp, hk0.bx, hk0.bp, hk0.r12, hk0.r13, hk0.r14, hk0.r15⟩,
        Keep.ok (g := g) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok (Nat.le_add_right_of_le (Dup.succ_le hL)) (Dup.succ_le hN),
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Dup.flat_dup_bind hok hc hL hN hLM hdM, rfl⟩

end Bbu.Unit
