module

public import BbuKraken.Unit.Defs
import all BbuKraken.Unit.Defs
public import BbuKraken.Unit.Push
import all BbuKraken.Unit.Push
public import BbuKraken.FlatPop
import all BbuKraken.FlatPop
public import BbuKraken.Sep.Stores
import all BbuKraken.Sep.Stores
public import ProofKit.Cfg
import all ProofKit.Cfg
public import ProofKit.Idioms
import all ProofKit.Idioms

@[expose] public section

/-!
# `pop`

`Names.pop` in `build/kraken/c/build_bottom_up.S`: if `m_size` is 0, it calls `exit(1)`. Else it decrements `m_size`, stores the record `Pop` at `m_traceSize`,
increments `m_traceSize`, and then stores `-1` to `m_positionOf[d]` if the destination `d` of
the old top is not `-1`. It returns `0`.

The record is in the view if `nops < 6n` (`popA`). The store to `m_positionOf` is in the view if
the destination of the top is `-1` or below `n` (`DestOk`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

-- `pop()`: room for the record if the stack is not empty, and destinations below `n`.
def popA (g : G) (_s : MachineData) : Prop :=
  (g.h.len ≠ 0 → g.h.nops.toNat < 6 * g.h.n.toNat + g.xo) ∧ DestOk (flat g)
def popQ (g g' : G) (_s t : MachineData) : Prop := Res Flat.pop g g' t

namespace Pop

open Push

/-! ## The three cases of `Flat.pop` -/

theorem pop_zero (fs : Flat.St) (h : fs.size = 0) : Flat.pop fs = (.assertionFailed, fs) := by
  simp [Flat.pop, Flat.stackPop, h]

theorem pop_none (fs : Flat.St) (h : fs.size ≠ 0) (hd : Flat.get fs.dest (fs.size - 1) = Flat.NONE) :
    Flat.pop fs = (.done, { fs with size := fs.size - 1, trace := fs.trace ++ [Op.pop] }) := by
  unfold Flat.pop Flat.stackPop Flat.mappingPop
  rw [ite_eq_right h]
  dsimp only
  simp only [ne_eq, not_true_eq_false, ite_false, hd]

theorem pop_some (fs : Flat.St) (h : fs.size ≠ 0) (hd : Flat.get fs.dest (fs.size - 1) ≠ Flat.NONE) :
    Flat.pop fs = (.done, { fs with size := fs.size - 1, trace := fs.trace ++ [Op.pop],
                                    pos := Flat.put fs.pos (Flat.get fs.dest (fs.size - 1)) Flat.NONE }) := by
  unfold Flat.pop Flat.stackPop Flat.mappingPop
  rw [ite_eq_right h]
  dsimp only
  simp only [ne_eq, not_true_eq_false, ite_false, hd, not_false_eq_true, ite_true]

/-! ## `flat` of the ghost after the stores -/

-- `leaq -1(%rax)`
theorem add_neg_one (x : Word) : x + BitVec.ofInt 64 (-1) = x - 1 := by
  bv_omega

-- The index of the top in the form of `Flat.pop`. (`symexec_norm` changes the form of `1` in the
-- hypotheses, so a local equation does not match.)
theorem size_sub_one {g : G} {w : Word} (hw : g.h.len + BitVec.ofInt 64 (-1) = w) :
    (flat g).size - 1 = w := by
  rw [← hw]; exact (add_neg_one _).symm

-- The store to `m_size` and the record: `Flat.stackPop`. The size `w` is in the form of the asm
-- (`add_neg_one`): `simp` on `flat` of `len + BitVec.ofInt 64 (-1)` gives a term that the
-- kernel does not check in the heartbeat limit.
theorem flat_pop (g : G) (hok : g.Ok) (hn : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo)
    (r : OpR) (hr : r.op = Op.pop) (w : Word) :
    flat { h := { g.h with len := w, nops := g.h.nops + 1#64 },
           xs := g.xs, xo := g.xo,
           stk := g.stk, ops := g.ops.set g.h.nops.toNat r hn, tgt := g.tgt, spl := g.spl }
      = { flat g with size := w, trace := (flat g).trace ++ [Op.pop] } := by
  have hN := hok.n
  have hx := hok.xo
  have ht : ((g.ops.set g.h.nops.toNat r hn).toList.take (g.h.nops + 1#64).toNat).map OpR.op
      = (g.ops.toList.take g.h.nops.toNat).map OpR.op ++ [Op.pop] := by
    rw [toNat_succ g.h.nops hn (by omega), Vector.toList_set,
      take_set_succ _ _ _ (by simpa using hn), List.map_append, List.map_singleton, hr]
  simp only [flat, ht]

-- The store to `m_positionOf`.
theorem flat_pos (g : G) (d : Word) (hd : d.toNat < MAX_N) :
    flat { g with h := { g.h with pos := g.h.pos.set d.toNat Flat.NONE hd } }
      = { flat g with pos := Flat.put g.h.pos d Flat.NONE } := by
  simp only [flat, put_eq_set _ _ _ hd]

-- The store to `m_size`, the record and the store to `m_positionOf`.
theorem flat_pop_pos (g : G) (hok : g.Ok) (hn : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo)
    (r : OpR) (hr : r.op = Op.pop) (w d : Word) (hd : d.toNat < MAX_N) :
    flat { h := { g.h with len := w, nops := g.h.nops + 1#64,
                           pos := g.h.pos.set d.toNat Flat.NONE hd },
           xs := g.xs, xo := g.xo,
           stk := g.stk, ops := g.ops.set g.h.nops.toNat r hn, tgt := g.tgt, spl := g.spl }
      = { flat g with size := w, trace := (flat g).trace ++ [Op.pop],
                      pos := Flat.put g.h.pos d Flat.NONE } := by
  have e := flat_pos
    { h := { g.h with len := w, nops := g.h.nops + 1#64 },
      xs := g.xs, xo := g.xo,
      stk := g.stk, ops := g.ops.set g.h.nops.toNat r hn, tgt := g.tgt, spl := g.spl } d hd
  rw [flat_pop g hok hn r hr w] at e
  exact e

/-! ## The asm forms -/

-- `movq $-1`: the word `NONE`.
theorem none_toInt : Flat.NONE.toInt = -1 := rfl

theorem rd_dest {S : Addr} {g : G} {F : MProp 64} {m : Mem 64} (h : (View S g ∗ F).get m) {i : Nat}
    (hi : i < MAX_N) :
    rd m (Fld.mapping_destinationOf S i) = g.h.dest[i] := by
  obtain ⟨R, h'⟩ := View.arr_dest h
  exact (Arr.rd h' (by simpa using hi)).trans (by simp)

-- The destination of a slot below the size, if it is not `NONE`, is below `MAX_N` (`DestOk`).
theorem dest_lt (g : G) (hok : g.Ok) (hd : DestOk (flat g)) {w : Word} (hwN : w.toNat < MAX_N)
    (hw : w.toNat < g.h.len.toNat) (hne : g.h.dest[w.toNat] ≠ Flat.NONE) :
    g.h.dest[w.toNat].toNat < MAX_N := by
  have h := hd w.toNat hw
  change Flat.get g.h.dest (BitVec.ofNat 64 w.toNat) = Flat.NONE
    ∨ (Flat.get g.h.dest (BitVec.ofNat 64 w.toNat)).toNat < g.h.n.toNat at h
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, get_eq _ _ hwN] at h
  rcases h with h | h
  · exact absurd h hne
  · exact Nat.lt_of_lt_of_le h hok.n

/-- The state at `.LB.Emission.pop.0`: the stores of `pop` are done, and the status is `done`. -/
def doneInv (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (fr : List Word) (t : MachineData) :
    Prop :=
  ∃ g', Kp S g' F s ra fr t ∧ g'.Ok ∧ Keep g g'
    ∧ flat g' = (Flat.pop (flat g)).2 ∧ (Flat.pop (flat g)).1 = .done

end Pop

open Push Pop in
theorem pop_unit [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels popAsm, label l ≠ label "exit") :
    UnitThmWithExit popAsm popA 2 popQ (fun g g' _ _ => ExitRes Flat.pop g g') := by
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  obtain ⟨x, y, rfl⟩ : ∃ x y, fr = [x, y] := by
    match fr, hfr with
    | [x, y], _ => exact ⟨x, y, rfl⟩
  have hk0 : Kp S g F s ra [x, y] (s.pushRa ra) := Kp.init hm
  have he := ProofKit.external_call_spec "exit" hexit
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label "_ZN12_GLOBAL__N_18Emission3popEv", t => t = s.pushRa ra
      | .label ".LB.Emission.pop.0", t => doneInv S g F s ra [x, y] t
      | .label ".LB.Emission.pop.1", t => Kp S g F s ra [x, y] t ∧ g.h.len = 0
      | _, _ => False)
    (fun | _, _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht => subst ht; kvcgen64
  case «_ZN12_GLOBAL__N_18Emission3popEv» t ht =>
    subst ht
    have hS : (s.pushRa ra).regs.rdi.toBitVec = S := hpre.rdi
    have hok := hpre.ok
    have hm0 := hk0.mem
    obtain ⟨hn, hdest⟩ := hpre.args
    have hN := hok.n
    by_cases hl0 : g.h.len = 0
    · -- The empty stack branches to the external exit call.
      have hz : (BitVec.ofInt 64 (Mem.loadInt (s.pushRa ra).dmem
            ((s.pushRa ra).regs.rdi.toBitVec + 32#64) 8).get! &&&
          BitVec.ofInt 64 (Mem.loadInt (s.pushRa ra).dmem
            ((s.pushRa ra).regs.rdi.toBitVec + 32#64) 8).get! == BitVec.zero 64) = true := by
        simp only [hS, rd_eq, Fld.fold_stack_size, View.rd_len hm0, hl0, BitVec.and_self,
          BitVec.zero_eq]
        rfl
      kvcgen64
      all_goals symexec_norm
      all_goals try (simp only [hz, Bool.true_eq_false] at *; done)
      all_goals try simp only [hS, rd_eq, Fld.fold_stack_size]
      vc_by_shape
      | closed => decide
      | load => view_load
      | goto ".LB.Emission.pop.1" =>
        cfg_goto
        · exact Kp.stack (fr := [x, y]) ⟨hm0, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact ⟨⟨hm0, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hl0⟩
        · simp
    · -- The fall-through: the size `w` is `len - 1`, the slot of the top.
      have hn := hn hl0
      have hlen := hok.len
      have hxs := hok.xs
      have hx := hok.xo
      obtain ⟨w, hw⟩ : ∃ w, g.h.len + BitVec.ofInt 64 (-1) = w := ⟨_, rfl⟩
      have hw' : w = (flat g).size - 1 := hw ▸ add_neg_one _
      have hwl : w.toNat < g.h.len.toNat := by
        have : g.h.len.toNat ≠ 0 := fun h => hl0 (BitVec.eq_of_toNat_eq (by simpa using h))
        rw [hw']; show (g.h.len - 1).toNat < g.h.len.toNat; bv_omega
      have hwN : w.toNat < MAX_N := by omega
      have hz : (BitVec.ofInt 64 (Mem.loadInt (s.pushRa ra).dmem
            ((s.pushRa ra).regs.rdi.toBitVec + 32#64) 8).get! &&&
          BitVec.ofInt 64 (Mem.loadInt (s.pushRa ra).dmem
            ((s.pushRa ra).regs.rdi.toBitVec + 32#64) 8).get! == BitVec.zero 64) = false := by
        simp only [hS, rd_eq, Fld.fold_stack_size, View.rd_len hm0, BitVec.and_self,
          beq_eq_false_iff_ne, BitVec.zero_eq, ne_eq]
        exact hl0
      -- The view after each store of the asm, in the order of the asm.
      have h1 := View.store_len hm0 w
      have h2 := View.store_nops h1 (g.h.nops + 1#64)
      have hf := View.focus h2 (i := g.h.nops.toNat) hn
      have hr1 := OpM.store_kind hf 2
      have hr2 := OpM.store_depth hr1 0
      have hr3 := OpM.store_payload hr2 0
      have hr4 := OpM.store_skind hr3 1
      have hr5 := OpM.store_sop hr4 5
      have h8 := View.unfocus hr5 hn
      dsimp only at h2 hf hr1 hr2 hr3 hr4 hr5 h8
      kvcgen64
      all_goals symexec_norm
      all_goals try (simp only [hz, Bool.false_eq_true] at *; done)
      all_goals try simp only [hS, rd_eq, ↓Fld.fold_mapping_positionOf,
        ↓Fld.fold_mapping_destinationOf, Fld.fold_stack_size,
        Fld.fold_stack_trace, Fld.fold_stack_traceSize, fold_op,
        View.rd_len hm0, hw, View.rd_nops h1, View.rd_ops h2, rd_dest h8 hwN]
      vc_by_shape
      | closed => decide
      | load =>
        first
        | view_load
        | (rename_i hc
           simp only [hS, rd_eq, ↓Fld.fold_mapping_destinationOf, Fld.fold_stack_size,
             Fld.fold_stack_trace, Fld.fold_stack_traceSize, fold_op,
             View.rd_len hm0, hw, View.rd_nops h1, View.rd_ops h2, rd_dest h8 hwN, cmp_none] at hc
           have hc' : g.h.dest[w.toNat] ≠ Flat.NONE := by simpa using hc
           exact View.isSome_pos h8 (dest_lt g hok hdest hwN hwl hc'))
      | goto ".LB.Emission.pop.0" =>
        -- `je`: the destination of the top is `-1`, the view `h8`.
        rename_i hc
        simp only [hS, rd_eq, ↓Fld.fold_mapping_destinationOf, Fld.fold_stack_size,
          Fld.fold_stack_trace, Fld.fold_stack_traceSize, fold_op,
          View.rd_len hm0, hw, View.rd_nops h1, View.rd_ops h2, rd_dest h8 hwN, cmp_none] at hc
        have hc' : g.h.dest[w.toNat] = Flat.NONE := by simpa using hc
        have hd : Flat.get (flat g).dest ((flat g).size - 1) = Flat.NONE := by
          rw [size_sub_one hw, get_eq _ _ hwN]; exact hc'
        cfg_goto
        · exact Kp.stack (fr := [x, y]) ⟨h8, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · show doneInv S g F s ra [x, y] _
          refine ⟨_, ⟨h8, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_,
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
          · exact Keep.ok (g := g) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok
              (by show w.toNat ≤ g.h.n.toNat + g.xs; omega)
              (by show (g.h.nops + 1#64).toNat ≤ 6 * g.h.n.toNat + g.xo
                  rw [toNat_succ _ hn (by omega)]; omega)
          · rw [pop_none (flat g) hl0 hd, size_sub_one hw]; exact flat_pop g hok hn _ (by rfl) w
          · rw [pop_none (flat g) hl0 hd]
        · simp
      | other =>
        -- The fall-through to `.LB.Emission.pop.0`: `m_positionOf[d] = -1`, the view `h9`.
        rename_i hc
        simp only [hS, rd_eq, ↓Fld.fold_mapping_destinationOf, Fld.fold_stack_size,
          Fld.fold_stack_trace, Fld.fold_stack_traceSize, fold_op,
          View.rd_len hm0, hw, View.rd_nops h1, View.rd_ops h2, rd_dest h8 hwN, cmp_none] at hc
        have hc' : g.h.dest[w.toNat] ≠ Flat.NONE := by simpa using hc
        have hdN := dest_lt g hok hdest hwN hwl hc'
        have hd : Flat.get (flat g).dest ((flat g).size - 1) ≠ Flat.NONE := by
          rw [size_sub_one hw, get_eq _ _ hwN]; exact hc'
        have h9 := View.store_pos h8 hdN Flat.NONE
        dsimp only at h9
        rw [none_toInt] at h9
        show doneInv S g F s ra [x, y] _
        refine ⟨_, ⟨h9, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
        · exact Keep.ok (g := g) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok
            (by show w.toNat ≤ g.h.n.toNat + g.xs; omega)
            (by show (g.h.nops + 1#64).toNat ≤ 6 * g.h.n.toNat + g.xo
                rw [toNat_succ _ hn (by omega)]; omega)
        · rw [pop_some (flat g) hl0 hd, size_sub_one hw, get_eq _ _ hwN]
          exact flat_pop_pos g hok hn _ (by rfl) w _ hdN
        · rw [pop_some (flat g) hl0 hd]
  case «.LB.Emission.pop.0» t ht =>
    obtain ⟨g', hk, hok, hkeep, hflat, hdone⟩ := ht
    kvcgen64
    vc_by_shape
    | retAddr => exact (show t.retAddr.isSome = true by simp [hk.retAddr])
    | ret =>
      refine ProofKit.intercept_mono_exit
        (E := fun a t => a = ra ∧ Sep.Post S F 2 (fun g' t => popQ g g' s t) s t
          ∧ Sep.mod.Agree s t) ?_ (fun h => Or.inl h)
      exact Kp.ret (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) rfl hok fun t' _ hax =>
        ⟨hkeep, hflat, by show (rax t').setWidth 8 = _; rw [hax, hdone]; rfl⟩
  case «.LB.Emission.pop.1» t ht =>
    obtain ⟨hk, hzero⟩ := ht
    have hmem := Stk.two (rsp s) x y ra.toBitVec _ F ▸ hk.mem
    have haddr : t.regs.rsp.toBitVec - 8#64 - 8#64 = rsp s - 24#64 := by
      change t.regs.get64 .rsp - 8#64 - 8#64 = rsp s - 24#64
      rw [hk.sp64]
      bv_omega
    kvcgen64 [he]
    all_goals symexec_norm
    vc_by_shape
    | load => simpa only [haddr] using Wd.isSome hmem
    | jumpOut =>
      rename_i exitra _
      refine Or.inr ⟨Or.inr ⟨rfl, rfl, ?_⟩, ?_⟩
      · refine ⟨g, [exitra.toBitVec, y], ra.toBitVec, ?_, hpre.ok, rfl, ?_⟩
        · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
            by rw [pop_zero _ hzero], by rw [pop_zero _ hzero]⟩
        · rw [Stk.two]
          change (Wd (rsp s - 24#64) exitra.toBitVec ∗ _).get
            (Mem.storeInt _ (t.regs.rsp.toBitVec - 8#64 - 8#64) 8 exitra.toBitVec.toInt)
          rw [haddr]
          exact Wd.store hmem exitra.toBitVec
      · intro l hl ha
        exact False.elim (hout l hl ha)

end Bbu.Unit
