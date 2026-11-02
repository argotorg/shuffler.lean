module

public import FlatShuffler.Unit.ExitDefs
import all FlatShuffler.Unit.ExitDefs
public import FlatShuffler.Sep.Stores
import all FlatShuffler.Sep.Stores
public import ProofKit.Cfg
import all ProofKit.Cfg
public import ProofKit.Idioms
import all ProofKit.Idioms

@[expose] public section

/-!
# `push`

`Names.push` in `build/kraken/c/build_bottom_up.S` stores the slot and its trace record, then checks the destination.
If the destination is free, it binds the slot and returns `Done`. Otherwise it calls `exit(1)`.
The exit contract retains the stores made before that check and relates them to `Flat.push`.
The two free stack words cover alignment and the return address of the external call.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit

open FlatShuffler.Sep

namespace Push

/-! ## Indexes in bounds

`Flat.get` and `Flat.put` take a `Word` index and do nothing out of bounds. The ghost uses
`Vector.set` with a proof of the bound. -/

theorem put_eq_set {α : Type} (v : Vector α MAX_N) (i : Word) (x : α) (h : i.toNat < MAX_N) :
    Flat.put v i x = v.set i.toNat x h := by
  apply Vector.ext; intro j hj
  simp only [Flat.put, Vector.getElem_setIfInBounds hj, Vector.getElem_set h hj]

theorem get_eq {α : Type} [Inhabited α] (v : Vector α MAX_N) (i : Word) (h : i.toNat < MAX_N) :
    Flat.get v i = v[i.toNat] := by
  simp [Flat.get, h]

theorem vec_set {α : Type} [Inhabited α] (l : List α) (i : Nat) (x : α) (hi : i < l.length)
    (hn : i < MAX_N) : vec (l.set i x) = (vec l).set i x hn := by
  apply Vector.ext; intro j hj
  simp only [vec, Vector.getElem_ofFn, Vector.getElem_set, List.getElem?_set]
  by_cases e : i = j
  · subst e; simp [hi]
  · simp [e]

theorem take_set_succ {α : Type} (l : List α) (i : Nat) (r : α) (hi : i < l.length) :
    (l.set i r).take (i + 1) = l.take i ++ [r] := by
  rw [List.take_add_one, List.getElem?_set_self hi, List.take_set_of_le (Nat.le_refl i)]
  rfl

theorem toNat_succ (x : Word) {k : Nat} (h : x.toNat < k) (hk : k ≤ 10 * MAX_N) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [MAX_N] at hk
  omega

/-! ## The two cases of `Flat.push` -/

-- The destination has a slot: `assertionFailed`, and no `bind`.
theorem push_fail (fs : Flat.St) (x : StackSlot) (d : Word) (h : Flat.get fs.pos d ≠ Flat.NONE) :
    Flat.push fs x d = (.assertionFailed, Flat.stackPush fs x) := by
  simp [Flat.push, Flat.stackPush, h]

-- The destination has no slot: `done`, and `bind` of the new slot (index `size` before the push).
theorem push_ok (fs : Flat.St) (x : StackSlot) (d : Word) (h : Flat.get fs.pos d = Flat.NONE) :
    Flat.push fs x d = (.done, Flat.bind (Flat.stackPush fs x) fs.size d) := by
  simp [Flat.push, Flat.stackPush, h, BitVec.add_sub_cancel]

/-! ## `flat` of the ghost after the stores -/

-- The two stores and the two counters: `Flat.stackPush`.
theorem flat_push (g : G) (hok : g.Ok) (hl : g.h.len.toNat < g.h.n.toNat)
    (hn : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo) (w : Word) (r : OpR)
    (hr : r.op = Op.push (StackSlot.ofWord w)) :
    flat { h := { g.h with len := g.h.len + 1#64, nops := g.h.nops + 1#64 },
           xs := g.xs, xo := g.xo, stk := g.stk.set g.h.len.toNat w (Nat.lt_add_right _ hl),
           ops := g.ops.set g.h.nops.toNat r hn,
           tgt := g.tgt, spl := g.spl }
      = Flat.stackPush (flat g) (StackSlot.ofWord w) := by
  have hN := hok.n
  have hx := hok.xo
  have hlN : g.h.len.toNat < MAX_N := by omega
  have hd : vec ((g.stk.set g.h.len.toNat w (Nat.lt_add_right _ hl)).toList.map StackSlot.ofWord)
      = Flat.put (vec (g.stk.toList.map StackSlot.ofWord)) g.h.len (StackSlot.ofWord w) := by
    rw [Vector.toList_set, List.map_set,
      vec_set _ _ _ (by simpa using Nat.lt_add_right g.xs hl) hlN,
      put_eq_set _ _ _ hlN]
  have ht : ((g.ops.set g.h.nops.toNat r hn).toList.take (g.h.nops + 1#64).toNat).map OpR.op
      = (g.ops.toList.take g.h.nops.toNat).map OpR.op ++ [Op.push (StackSlot.ofWord w)] := by
    rw [toNat_succ g.h.nops hn (by omega), Vector.toList_set,
      take_set_succ _ _ _ (by simpa using hn), List.map_append, List.map_singleton, hr]
  simp only [flat, Flat.stackPush, hd, ht]
  rfl

-- The two stores of `bind`.
theorem flat_bind (g : G) (p d : Word) (hp : p.toNat < MAX_N) (hd : d.toNat < MAX_N) :
    flat { g with h := { g.h with dest := g.h.dest.set p.toNat d hp,
                                  pos := g.h.pos.set d.toNat p hd } }
      = Flat.bind (flat g) p d := by
  simp only [flat, Flat.bind, put_eq_set _ _ _ hp, put_eq_set _ _ _ hd]

-- The ghost of the fall-through path: `Flat.stackPush`, then `Flat.bind`.
theorem flat_push_bind (g : G) (hok : g.Ok) (hl : g.h.len.toNat < g.h.n.toNat)
    (hn : g.h.nops.toNat < 6 * g.h.n.toNat + g.xo) (w : Word) (r : OpR)
    (hr : r.op = Op.push (StackSlot.ofWord w)) (d : Word)
    (hp : g.h.len.toNat < MAX_N) (hd : d.toNat < MAX_N) :
    flat { h := { g.h with len := g.h.len + 1#64, nops := g.h.nops + 1#64,
                           dest := g.h.dest.set g.h.len.toNat d hp,
                           pos := g.h.pos.set d.toNat g.h.len hd },
           xs := g.xs, xo := g.xo, stk := g.stk.set g.h.len.toNat w (Nat.lt_add_right _ hl),
           ops := g.ops.set g.h.nops.toNat r hn,
           tgt := g.tgt, spl := g.spl }
      = Flat.bind (Flat.stackPush (flat g) (StackSlot.ofWord w)) g.h.len d := by
  rw [← flat_push g hok hl hn w r hr]
  exact flat_bind { h := { g.h with len := g.h.len + 1#64, nops := g.h.nops + 1#64 },
                    xs := g.xs, xo := g.xo,
                    stk := g.stk.set g.h.len.toNat w (Nat.lt_add_right _ hl),
                    ops := g.ops.set g.h.nops.toNat r hn,
                    tgt := g.tgt, spl := g.spl } g.h.len d hp hd

/-! ## The asm forms after `symexec_norm` -/

-- An 8-byte load.
theorem rd_eq (m : Mem 64) (a : Addr) : BitVec.ofInt 64 (Mem.loadInt m a 8).get! = rd m a := rfl

-- `shrq $i` and then the low `n` bits.
theorem ext_ushr (w : Word) (i n : Nat) :
    BitVec.extractLsb' 0 n (w.ushiftRight i) = w.extractLsb' i n :=
  Idioms.take_ushiftRight w i n

-- `cmpq $-1, m_positionOf[d]` gives `x - (2^64 - 1) == 0`: the test for `NONE`.
theorem cmp_none (x : Word) :
    (x - 18446744073709551615#64 == BitVec.zero 64) = (x == Flat.NONE) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, Flat.NONE, BitVec.zero_eq]
  constructor <;> intro h <;> bv_omega

-- `size + 1 - 1` in the fall-through path: the index of the new slot.
theorem add_one_sub (x : Word) : x + 1#64 + BitVec.ofInt 64 (-1) = x := by
  bv_omega

-- The `ShuffleOp` kind byte that the asm stores: the kind of `Op.push`.
theorem push_kind (x y w : Word) :
    BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (3#32 +
      (BitVec.extractLsb' 0 32 (x.replaceLow (BitVec.ofNat 8
          (!(w.extractLsb' 40 8 &&& w.extractLsb' 40 8 == BitVec.zero 8)).toNat)) &&&
        BitVec.extractLsb' 0 32 (y.replaceLow (BitVec.ofNat 8
          (w.extractLsb' 32 8 &&& w.extractLsb' 32 8 == BitVec.zero 8).toNat)))))
      = (Op.push (StackSlot.ofWord w)).kind := by
  refine (Idioms.kind_sel x y _ _).trans ?_
  simp only [Op.push, isLiteralValue, StackSlot.ofWord, BitVec.and_self, Value, Const, Load, Push,
    BitVec.zero_eq, Bool.and_comm]
  rfl

-- `movl %edx, %eax`: the low byte of `eax` is the low byte of `rdx`.
theorem al_movl (x : Word) : (BitVec.setWidth 64 (x.take 32)).setWidth 8 = x.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

/-- The stores before the destination test are complete. -/
def lbInv (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (fr : List Word) (t : MachineData) : Prop :=
  ∃ g', Kp S g' F s ra fr t ∧ g'.Ok ∧ Keep g g'
    ∧ flat g' = Flat.stackPush (flat g) (StackSlot.ofWord (rsi s))
    ∧ g'.h.len = g.h.len + 1#64 ∧ rax t = S ∧ rdi t = rdx s
    ∧ Flat.get (flat g).pos (rdx s) = Flat.NONE

end Push

open Push in
theorem push_unit [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels pushAsm, label l ≠ label "exit") :
    UnitThmWithExit pushAsm pushA 2 pushQ pushX := by
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
      | .label "_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset", t => t = s.pushRa ra
      | .label ".LB.Emission.push.0", t => lbInv S g F s ra [x, y] t
      | _, _ => False)
    (fun | _, _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht => subst ht; kvcgen64
  case «_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset» t ht =>
    subst ht
    have hS : (s.pushRa ra).regs.rdi.toBitVec = S := hpre.rdi
    have hok := hpre.ok
    have hm0 := hk0.mem
    obtain ⟨hl, hn, hdn⟩ := hpre.args
    have hN := hok.n
    have hx := hok.xo
    have hd' : (s.pushRa ra).regs.rdx.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hdn hN
    have hlN : g.h.len.toNat < MAX_N := Nat.lt_of_lt_of_le hl hN
    have hl1 : (g.h.len + 1#64).toNat = g.h.len.toNat + 1 := toNat_succ _ hl (by omega)
    have hn1 : (g.h.nops + 1#64).toNat = g.h.nops.toNat + 1 := toNat_succ _ hn (by omega)
    have h1 := View.store_len hm0 (g.h.len + 1#64)
    have h2 := View.store_stk h1 (i := g.h.len.toNat)
      (Nat.lt_add_right _ hl) (s.pushRa ra).regs.rsi.toBitVec
    have h3 := View.store_nops h2 (g.h.nops + 1#64)
    have hf := View.focus h3 (i := g.h.nops.toNat) hn
    have hr1 := OpM.store_kind hf
      (Op.push (StackSlot.ofWord (s.pushRa ra).regs.rsi.toBitVec)).kind.toInt
    have hr2 := OpM.store_depth hr1 0
    have hr3 := OpM.store_payload hr2 ((s.pushRa ra).regs.rsi.toBitVec.extractLsb' 0 32).toInt
    have hr4 := OpM.store_skind hr3 ((s.pushRa ra).regs.rsi.toBitVec.extractLsb' 32 8).toInt
    have hr5 := OpM.store_sop hr4 ((s.pushRa ra).regs.rsi.toBitVec.extractLsb' 40 8).toInt
    have h8 := View.unfocus hr5 hn
    dsimp only at h2 h3 hf hr1 hr2 hr3 hr4 hr5 h8
    simp only [BitVec.ofInt_toInt, show BitVec.ofInt 8 0 = (0 : BitVec 8) by decide] at h8
    let gp : G := { g with
      h := { g.h with len := g.h.len + 1#64, nops := g.h.nops + 1#64 },
      stk := g.stk.set g.h.len.toNat (rsi s) (Nat.lt_add_right _ hl),
      ops := g.ops.set g.h.nops.toNat
        ⟨Op.push (StackSlot.ofWord (rsi s)), g.ops[g.h.nops.toNat].pad2,
          g.ops[g.h.nops.toNat].pad10⟩ hn }
    have h8x := Stk.two (rsp s) x y ra.toBitVec _ F ▸ h8
    have haddr : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 = rsp s - 24#64 := by
      change rsp s - 8#64 - 8#64 - 8#64 = rsp s - 24#64
      bv_omega
    kvcgen64 [he]
    all_goals symexec_norm
    all_goals try simp only [hS, rd_eq, ext_ushr, ↓Fld.fold_mapping_positionOf,
      Fld.fold_stack_size, Fld.fold_stack_data,
      Fld.fold_stack_trace, Fld.fold_stack_traceSize, fold_slot, fold_op,
      View.rd_len hm0, View.rd_data hm0, View.rd_nops h2, View.rd_ops h3, push_kind,
      View.rd_pos h8 hd']
    vc_by_shape
    | closed => decide
    | load =>
      first
      | view_load
      | simpa only [haddr] using Wd.isSome h8x
    | goto ".LB.Emission.push.0" =>
      rename_i hc
      simp only [hS, rd_eq, ext_ushr, ↓Fld.fold_mapping_positionOf,
        Fld.fold_stack_size, Fld.fold_stack_data,
        Fld.fold_stack_trace, Fld.fold_stack_traceSize, fold_slot, fold_op,
        View.rd_len hm0, View.rd_data hm0, View.rd_nops h2, View.rd_ops h3, push_kind,
        View.rd_pos h8 hd', cmp_none] at hc
      have hc' : g.h.pos[(s.pushRa ra).regs.rdx.toBitVec.toNat] = Flat.NONE := by simpa using hc
      have heq : Flat.get (flat g).pos (rdx s) = Flat.NONE := by
        rw [get_eq _ (rdx s) hd']; exact hc'
      cfg_goto
      · exact Kp.stack (fr := [x, y]) ⟨h8, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · refine ⟨_, ⟨h8, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          flat_push g hok hl hn _ _ (by rfl), rfl, hS, rfl, heq⟩
        exact Keep.ok (g := g) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok
          (by show (g.h.len + 1#64).toNat ≤ g.h.n.toNat + g.xs; omega)
          (by show (g.h.nops + 1#64).toNat ≤ 6 * g.h.n.toNat + g.xo; omega)
      · simp
    | jumpOut =>
      rename_i exitra _ hc
      simp only [hS, rd_eq, ext_ushr, ↓Fld.fold_mapping_positionOf,
        Fld.fold_stack_size, Fld.fold_stack_data,
        Fld.fold_stack_trace, Fld.fold_stack_traceSize, fold_slot, fold_op,
        View.rd_len hm0, View.rd_data hm0, View.rd_nops h2, View.rd_ops h3, push_kind,
        View.rd_pos h8 hd', cmp_none] at hc
      have hc' : g.h.pos[(s.pushRa ra).regs.rdx.toBitVec.toNat] ≠ Flat.NONE := by simpa using hc
      have hne : Flat.get (flat g).pos (rdx s) ≠ Flat.NONE := by
        rw [get_eq _ (rdx s) hd']; exact hc'
      refine Or.inr ⟨Or.inr ⟨rfl, rfl, ?_⟩, ?_⟩
      · refine ⟨gp, [exitra.toBitVec, y], ra.toBitVec, ?_, ?_, rfl, ?_⟩
        · show pushX g _ s _
          refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
          · dsimp only
            rw [push_fail (flat g) (StackSlot.ofWord (rsi s)) (rdx s) hne]
            exact flat_push g hok hl hn _ _ (by rfl)
          · dsimp only
            rw [push_fail (flat g) (StackSlot.ofWord (rsi s)) (rdx s) hne]
        · exact Keep.ok (g := g) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok
            (by show (g.h.len + 1#64).toNat ≤ g.h.n.toNat + g.xs; omega)
            (by show (g.h.nops + 1#64).toNat ≤ 6 * g.h.n.toNat + g.xo; omega)
        · rw [Stk.two]
          change (Wd (rsp s - 24#64) exitra.toBitVec ∗ _).get
            (Mem.storeInt _ ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64) 8 exitra.toBitVec.toInt)
          rw [haddr]
          have hstored := Wd.store h8x exitra.toBitVec
          dsimp only [gp, Op.push, StackSlot.ofWord, MachineData.pushRa,
            Reg64s.set64_rsp, rsi, rsp, Reg64s.get64_rsi, Reg64s.get64_rsp] at hstored ⊢
          exact hstored
      · intro l hl ha
        exact False.elim (hout l hl ha)
  case «.LB.Emission.push.0» t ht =>
    obtain ⟨g', hk, hok, hkeep, hflat, hlen, hax, hdi, heq⟩ := ht
    obtain ⟨hl, hn, hd⟩ := hpre.args
    have hL : g.h.len.toNat < MAX_N := Nat.lt_of_lt_of_le hl hpre.ok.n
    have hD : (rdx s).toNat < MAX_N := Nat.lt_of_lt_of_le hd hpre.ok.n
    have hidx : g'.h.len + BitVec.ofInt 64 (-1) = g.h.len := by rw [hlen]; bv_omega
    have hm0 := hk.mem
    have h1 := View.store_dest hm0 hL (rdx s)
    have h2 := View.store_pos h1 hD g.h.len
    dsimp only at h1 h2
    kvcgen64
    all_goals symexec_norm
    all_goals try simp only [hax, hdi, rd_eq, Fld.fold_stack_size, View.rd_len hm0,
      hidx, ↓Fld.fold_mapping_destinationOf, ↓Fld.fold_mapping_positionOf]
    vc_by_shape
    | load => view_load
    | retAddr =>
      exact Option.isSome_iff_exists.mpr
        ⟨ra, Kp.retAddr (S := S) (g := _) (F := F) (s := s) (fr := [x,y])
          ⟨h2, hk.sp, hk.bx, hk.bp, hk.r12, hk.r13, hk.r14, hk.r15⟩⟩
    | ret =>
      refine ProofKit.intercept_mono_exit
        (E := fun a t => a = ra ∧ Sep.Post S F 2 (fun g' t => pushQ g g' s t) s t
          ∧ Sep.mod.Agree s t) ?_ (fun h => Or.inl h)
      refine Kp.ret (S := S) (F := F) (s := s) (fr := [x, y]) (g := { g' with h := { g'.h with
          dest := g'.h.dest.set g.h.len.toNat (rdx s) hL,
          pos := g'.h.pos.set (rdx s).toNat g.h.len hD } }) ?_ rfl ?_ ?_
      · exact ⟨h2, hk.sp, hk.bx, hk.bp, hk.r12, hk.r13, hk.r14, hk.r15⟩
      · exact Keep.ok (g := g') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hok hok.len hok.nops
      · intro t' _ hr
        refine ⟨?_, ?_⟩
        · refine ⟨⟨hkeep.tgtp, hkeep.n, hkeep.splp, hkeep.data, hkeep.ops,
            hkeep.xs, hkeep.xo, hkeep.tgt, hkeep.spl⟩, ?_, ?_⟩
          · dsimp only
            rw [push_ok (flat g) (StackSlot.ofWord (rsi s)) (rdx s) heq,
              flat_bind _ _ _ hL hD, hflat]
            rfl
          · dsimp only
            rw [push_ok (flat g) (StackSlot.ofWord (rsi s)) (rdx s) heq]
            show (rax t').setWidth 8 = 0#8
            rw [hr]; rfl
        · show (rax t').setWidth 8 ≠ 2#8
          rw [hr]; change 0#8 ≠ 2#8; decide

end FlatShuffler.Unit
