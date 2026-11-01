module

public import BbuKraken.Unit.Plan.Call
import all BbuKraken.Unit.Plan.Call
public import BbuKraken.Unit.Plan.ClosestCopy
import all BbuKraken.Unit.Plan.ClosestCopy
public import BbuKraken.Unit.Plan.Map
import all BbuKraken.Unit.Plan.Map

@[expose] public section

/-!
# `MappingBuilder::mapInPlace`

`c/bbu/<Names.mapInPlace>.S`: if `commonSize = 0` it returns `DONE` at once. Else it pushes
`rbp`, `rbx` and runs the loop over the positions `rbx < commonSize`. `rbp` is the builder. Each
turn of the loop is one unfold of `Flat.inPlaceFrom`: a position with the same slot in the source
and the target that `map` can take is given to `map`. A status other than `DONE` stops the loop.
The frame of the loop is the return slot of `map` and the saved `rbx`, `rbp`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

def mapInPlaceA (_ : BG) (_ : MachineData) : Prop := True

def mapInPlaceQ (b b' : BG) (_ t : MachineData) : Prop :=
  al t = code (Flat.mapInPlace b.fl b.M).1 ∧ b' = { b with M := (Flat.mapInPlace b.fl b.M).2 }

namespace InPlaceU

-- The frame of the body: the return slot of `map`, then the saved `rbx` and `rbp`.
def fr (s : MachineData) (w : Word) : List Word := [w, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]

-- The registers in the loop. `M` is the `Mapping` so far.
structure LI (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (M : Flat.Mapping) (w : Word) (t : MachineData) : Prop where
  kb : Kb (BView B { b with M := M } ∗ F) s ra (fr s w) 16#64 t
  rbp : t.regs.rbp.toBitVec = B
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

/-! ### One turn of the loop -/

section
variable {fb : Flat.Builder} {M : Flat.Mapping} {j : Word}

theorem cs_le_m (fb : Flat.Builder) : (Flat.commonSize fb).toNat ≤ fb.m.toNat := by
  unfold Flat.commonSize; split <;> bv_omega

theorem cs_le_n (fb : Flat.Builder) : (Flat.commonSize fb).toNat ≤ fb.n.toNat := by
  unfold Flat.commonSize; split <;> bv_omega

-- The carry flag of `cmp b, a`.
theorem cf_lt (a b : Word) :
    ((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int)) = true) ↔ a.toNat < b.toNat := by
  rw [bne_iff_ne, ne_eq, BitVec.toNat_sub]
  have := a.isLt; have := b.isLt
  constructor <;> intro h <;> omega

theorem cf_ge (a b : Word) :
    ((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int)) = false) ↔ b.toNat ≤ a.toNat := by
  rw [← Bool.not_eq_true, cf_lt]; omega

-- `cmpq b, a; jnb`.
theorem jnb_true (a b : Word)
    (h : (!(((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))) = true) :
    b.toNat ≤ a.toNat :=
  (cf_ge a b).1 (by rw [Bool.not_eq_true'] at h; exact h)

theorem jnb_false (a b : Word)
    (h : (!(((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))) = false) :
    a.toNat < b.toNat :=
  (cf_lt a b).1 (by rw [Bool.not_eq_false'] at h; exact h)

-- `cmpq %rdx, %rax; cmova %rdx, %rax` with `rax = m`, `rdx = n`.
theorem cmova (m n : Word) :
    (if (!(((m - n).toNat : Int) != (m.toNat : Int) - (n.toNat : Int)) && !(m - n == BitVec.zero 64))
      = true then n else m) = if m < n then m else n := by
  by_cases h : m.toNat < n.toNat
  · rw [(cf_lt m n).2 h, ite_eq_left (BitVec.lt_def.2 h)]; rfl
  · rw [(cf_ge m n).2 (by omega), ite_eq_right (fun e => h (BitVec.lt_def.1 e))]
    by_cases e : m = n
    · subst e; simp
    · have : (m - n == BitVec.zero 64) = false := by
        rw [beq_eq_false_iff_ne]; intro h'; apply e; have h0 : m - n = 0#64 := h'; bv_omega
      rw [this]; rfl

theorem from_ge (h : ¬ j < Flat.commonSize fb) : Flat.inPlaceFrom fb M j = (.done, M) := by
  rw [Flat.inPlaceFrom, dite_eq_right h]

theorem from_skip (h : j < Flat.commonSize fb)
    (hc : (Flat.get fb.source j = Flat.get fb.target j && Flat.mappable fb M j) = false) :
    Flat.inPlaceFrom fb M j = Flat.inPlaceFrom fb M (j + 1) := by
  rw [Flat.inPlaceFrom, dite_eq_left h, hc]; rfl

theorem from_done (h : j < Flat.commonSize fb)
    (hc : (Flat.get fb.source j = Flat.get fb.target j && Flat.mappable fb M j) = true)
    (hd : (Flat.mbMap fb M j j).1 = .done) :
    Flat.inPlaceFrom fb M j = Flat.inPlaceFrom fb (Flat.mbMap fb M j j).2 (j + 1) := by
  rw [Flat.inPlaceFrom, dite_eq_left h, ite_eq_left hc]
  dsimp only
  rw [ite_eq_right (by simp [hd])]

theorem from_fail (h : j < Flat.commonSize fb)
    (hc : (Flat.get fb.source j = Flat.get fb.target j && Flat.mappable fb M j) = true)
    (hd : (Flat.mbMap fb M j j).1 ≠ .done) :
    Flat.inPlaceFrom fb M j = Flat.mbMap fb M j j := by
  rw [Flat.inPlaceFrom, dite_eq_left h, ite_eq_left hc]
  dsimp only
  rw [ite_eq_left hd]

theorem skip_slot (h : j < Flat.commonSize fb) (hs : Flat.get fb.target j ≠ Flat.get fb.source j) :
    Flat.inPlaceFrom fb M j = Flat.inPlaceFrom fb M (j + 1) :=
  from_skip h (by simp [Ne.symm hs])

theorem skip_drop (h : j < Flat.commonSize fb) (hd : (!(Flat.get fb.dropped j == 0)) = true) :
    Flat.inPlaceFrom fb M j = Flat.inPlaceFrom fb M (j + 1) := by
  rw [Bool.not_eq_true'] at hd
  exact from_skip h (by simp only [Flat.mappable, hd, Bool.false_and, Bool.and_false])

theorem skip_dest (h : j < Flat.commonSize fb) (hd : (!(Flat.get M.dest j == Flat.NONE)) = true) :
    Flat.inPlaceFrom fb M j = Flat.inPlaceFrom fb M (j + 1) := by
  rw [Bool.not_eq_true'] at hd
  exact from_skip h (by simp only [Flat.mappable, hd, Bool.and_false])

theorem cand_of (hs : Flat.get fb.target j = Flat.get fb.source j)
    (hd : (!(Flat.get fb.dropped j == 0)) = false) (hm : (!(Flat.get M.dest j == Flat.NONE)) = false) :
    (Flat.get fb.source j = Flat.get fb.target j && Flat.mappable fb M j) = true := by
  rw [ClosestU.mappable_of hd hm, hs]; simp
end

/-! ### The registers -/

section
variable {B : Addr} {b : BG} {F : MProp 64} {s t t' : MachineData} {ra : Int64}
  {M : Flat.Mapping} {w : Word}

theorem LI.next (h : LI B b F s ra M w t) (hm : t'.dmem = t.dmem) (hsp : t'.regs.rsp = t.regs.rsp)
    (hbp : t'.regs.rbp = t.regs.rbp) (h12 : t'.regs.r12 = t.regs.r12)
    (h13 : t'.regs.r13 = t.regs.r13) (h14 : t'.regs.r14 = t.regs.r14)
    (h15 : t'.regs.r15 = t.regs.r15) : LI B b F s ra M w t' :=
  ⟨h.kb.next hm hsp, by rw [hbp]; exact h.rbp, h12 ▸ h.r12, h13 ▸ h.r13, h14 ▸ h.r14,
    h15 ▸ h.r15⟩

theorem LI.stk (h : LI B b F s ra M w t) (hm : t'.dmem = t.dmem) (hsp : t'.regs.rsp = t.regs.rsp) :
    t'.StackAtOrBelow (s.pushRa ra) :=
  (h.kb.next hm hsp).stack (by decide)

-- The state after `call map`: `map` keeps `rbx`, `rbp` and `r12`…`r15`.
theorem LI.after {c : MachineData} {M' : Flat.Mapping} {a' : BG} {lo' : List Word} {w' : Word}
    (hag : Sep.mod.Agree c t) (h : LI B b F s ra M w c)
    (hkb : Kb (BView B a' ∗ F) s ra (lo' ++ w' :: [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) 16#64 t)
    (hl : lo'.length = 0) (ha : a' = { b with M := M' }) :
    LI B b F s ra M' w' t ∧ t.regs.rbx = c.regs.rbx := by
  obtain rfl := List.eq_nil_of_length_eq_zero hl
  subst ha
  refine ⟨⟨hkb, ?_, ?_, ?_, ?_, ?_⟩, mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx⟩
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]; exact h.rbp
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact h.r12
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13]; exact h.r13
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]; exact h.r14
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15]; exact h.r15

-- The addresses of `popq %rbx; popq %rbp`.
theorem pop_addr (a : Word) :
    a = a + BitVec.ofNat 64 (8 * 0) ∧ a + 8#64 = a + BitVec.ofNat 64 (8 * 1) := by
  constructor <;> bv_omega

theorem LI.pop_isSome (h : LI B b F s ra M w t) :
    (t.dmem.loadInt t.regs.rsp.toBitVec 8).isSome = true
      ∧ (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome = true := by
  obtain ⟨e0, e1⟩ := pop_addr t.regs.rsp.toBitVec
  refine ⟨?_, ?_⟩
  · rw [e0]; exact Kb.isSome_hi (lo := [w]) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec])
      h.kb rfl (by simp)
  · rw [e1]; exact Kb.isSome_hi (lo := [w]) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec])
      h.kb rfl (by simp)

-- The state after the pops.
theorem LI.pop_kg (h : LI B b F s ra M w t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64)
    (hbx : t'.regs.rbx.toBitVec = rd t.dmem t.regs.rsp.toBitVec)
    (hbp : t'.regs.rbp.toBitVec = rd t.dmem (t.regs.rsp.toBitVec + 8#64))
    (h12 : t'.regs.r12 = t.regs.r12) (h13 : t'.regs.r13 = t.regs.r13)
    (h14 : t'.regs.r14 = t.regs.r14) (h15 : t'.regs.r15 = t.regs.r15) :
    Kg (BView B { b with M := M } ∗ F) s ra (fr s w) t' := by
  obtain ⟨e0, e1⟩ := pop_addr t.regs.rsp.toBitVec
  refine h.kb.kg hm ?_ ?_ ?_ (h12.trans h.r12) (h13.trans h.r13) (h14.trans h.r14)
    (h15.trans h.r15) <;> (try apply UInt64.toBitVec_inj.mp)
  · rw [hsp, h.kb.sp]; bv_omega
  · rw [hbx, e0]
    exact Kb.rd_hi (lo := [w]) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) h.kb rfl
      (i := 0) (by simp)
  · rw [hbp, e1]
    exact Kb.rd_hi (lo := [w]) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) h.kb rfl
      (i := 1) (by simp)
end

/-! ### The invariant, the variant and the obligation of a block -/

def Inv (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) (fr₀ : List Word) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.mapInPlace then t = s.pushRa ra
    else if l = ".LB.MappingBuilder.mapInPlace.0" then ∃ M w, LI B b F s ra M w t
      ∧ t.regs.rbx.toBitVec.toNat < (Flat.commonSize b.fl).toNat
      ∧ Flat.inPlaceFrom b.fl M (t.regs.rbx.toBitVec + 1#64) = Flat.mapInPlace b.fl b.M
    else if l = ".LB.MappingBuilder.mapInPlace.1" then ∃ M w, LI B b F s ra M w t
      ∧ t.regs.rbx.toBitVec.toNat < (Flat.commonSize b.fl).toNat
      ∧ Flat.inPlaceFrom b.fl M t.regs.rbx.toBitVec = Flat.mapInPlace b.fl b.M
    else if l = ".LB.MappingBuilder.mapInPlace.2" then ∃ M w, LI B b F s ra M w t
      ∧ Flat.mapInPlace b.fl b.M = (.done, M)
    else if l = ".LB.MappingBuilder.mapInPlace.3" then ∃ M w, LI B b F s ra M w t
      ∧ al t = code (Flat.mapInPlace b.fl b.M).1 ∧ (Flat.mapInPlace b.fl b.M).2 = M
    else if l = ".LB.MappingBuilder.mapInPlace.4" then Kg (BView B b ∗ F) s ra fr₀ t
      ∧ Flat.mapInPlace b.fl b.M = (.done, b.M)
    else False

-- The variant. A turn of the loop decreases `commonSize - rbx`.
def V (b : BG) (l : Label) (t : MachineData) : Nat :=
  if l = Names.mapInPlace then 2 ^ 70
  else if l = ".LB.MappingBuilder.mapInPlace.0" then
    2 * ((Flat.commonSize b.fl).toNat - t.regs.rbx.toBitVec.toNat)
  else if l = ".LB.MappingBuilder.mapInPlace.1" then
    2 * ((Flat.commonSize b.fl).toNat - t.regs.rbx.toBitVec.toNat) + 1
  else 0

def E (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost BView BG.Ok B F 3 (fun a' t => mapInPlaceQ b a' s t) s t
    ∧ Sep.mod.Agree s t

def Obl [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (fr₀ : List Word) (blk : Program.Block) : Prop :=
  ∀ t, Inv B b F s ra fr₀ blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv B b F s ra fr₀ c u ∧ Program.Decreases (V b) blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels mapInPlaceAsm) (s.pushRa ra) I' (E B b F s ra)) t

def labels : List CfgLabel :=
  [.entry, .label Names.mapInPlace,
    .label ".LB.MappingBuilder.mapInPlace.0", .label ".LB.MappingBuilder.mapInPlace.1",
    .label ".LB.MappingBuilder.mapInPlace.2", .label ".LB.MappingBuilder.mapInPlace.3",
    .label ".LB.MappingBuilder.mapInPlace.4"]

theorem labels_cover : mapInPlaceAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.mapInPlace]
  cfg_labels

macro "mi_inv" : tactic => `(tactic|
  simp only [Inv, Names.mapInPlace, String.reduceEq, ↓reduceIte])
macro "mi_inv" "at" h:ident : tactic => `(tactic|
  simp only [Inv, Names.mapInPlace, String.reduceEq, ↓reduceIte] at $h:ident)
macro "mi_var" : tactic => `(tactic|
  simp only [V, Names.mapInPlace, String.reduceEq, ↓reduceIte])

/-! ### The blocks -/

open ShallowestCopy

section
variable [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (fr₀ : List Word)

set_option maxHeartbeats 100000 in
theorem b_entry : mapInPlaceAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  mi_inv
  exact ht

set_option maxHeartbeats 100000 in
theorem b_fn (hpre : VPre BView BG.Ok B b F mapInPlaceA 3 s) (w₀ w₁ w₂ : Word)
    (hk0 : Kg (BView B b ∗ F) s ra [w₀, w₁, w₂] (s.pushRa ra)) :
    mapInPlaceAsm.ForallBlocks fun blk =>
      blk.label = .label Names.mapInPlace → Obl B b F s ra [w₀, w₁, w₂] blk := by
  cfg_block [Obl, Names.mapInPlace]
  intro t ht
  mi_inv at ht
  subst ht
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = B := by
    simpa [MachineData.pushRa] using hpre.rdi
  have hm0 := hk0.vmem
  have hq : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by
    rw [← Reg64s.get64_rsp, hk0.sp64]
  have hsp2 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 = rsp s - 8#64 - 16#64 := by
    rw [hq]; bv_omega
  obtain ⟨hpo, hpm⟩ := hk0.pushes (xs := [(s.pushRa ra).regs.rbp.toBitVec,
    (s.pushRa ra).regs.rbx.toBitVec]) (by simp)
  simp only [pushes] at hpm
  change (Stk (rsp s) (fr s w₀) ra.toBitVec ∗ BView B b ∗ F).get _ at hpm
  simp only [PushOk] at hpo
  obtain ⟨p1, p2, -⟩ := hpo
  have h_m := BView.rd_m hm0
  have h_n := BView.rd_n hm0
  unfold rd at h_m h_n
  have k_m := BView.isSome_m hm0
  have k_n := BView.isSome_n hm0
  clear hm0
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hrdi, h_m, h_n] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_m
    | with_reducible exact k_n
    | with_reducible exact p1
    | with_reducible exact p2
  | goto ".LB.MappingBuilder.mapInPlace.4" =>
    rename_i hc
    have h0 := zf_true hc
    rw [cmova] at h0
    cfg_goto
    · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
    · mi_inv
      exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl,
        from_ge (by show ¬ (0 : Word) < (if b.m < b.n then b.m else b.n); rw [h0]; decide)⟩
    · simp [V, Names.mapInPlace]
  | goto ".LB.MappingBuilder.mapInPlace.1" =>
    rename_i hc
    have h0 := zf_false hc
    rw [cmova] at h0
    have hcs : 0 < (Flat.commonSize b.fl).toNat :=
      Nat.pos_of_ne_zero fun h => h0 (BitVec.eq_of_toNat_eq h)
    cfg_goto
    · exact Kb.stack ⟨hpm, hsp2⟩ (by decide)
    · mi_inv
      exact ⟨b.M, w₀, ⟨⟨hpm, hsp2⟩, by simpa [MachineData.pushRa] using hpre.rdi, rfl, rfl, rfl, rfl⟩,
        hcs, rfl⟩
    · left; have := (Flat.commonSize b.fl).isLt; simp [V, Names.mapInPlace]; omega

set_option maxHeartbeats 100000 in
theorem b_0 : mapInPlaceAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapInPlace.0" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mi_inv at ht
  obtain ⟨M, w, hli, hlt, hrest⟩ := ht
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  have hbp := hli.rbp
  have h_m := BView.rd_m hb
  have h_n := BView.rd_n hb
  unfold rd at h_m h_n
  have k_m := BView.isSome_m hb
  have k_n := BView.isSome_n hb
  clear hb
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hbp, h_m, h_n] at *
  all_goals try rw [cmova] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_m
    | with_reducible exact k_n
  | goto ".LB.MappingBuilder.mapInPlace.2" =>
    have hge := jnb_true _ _ (by assumption)
    rw [BitVec.add_comm] at hge
    cfg_goto
    · exact hli.stk rfl rfl
    · mi_inv
      exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl,
        hrest.symm.trans (from_ge fun h => absurd (BitVec.lt_def.1 h) (Nat.not_lt.2 hge))⟩
    · left; mi_var; omega
  | other =>
    have hlt' := jnb_false _ _ (by assumption)
    first
    | (left
       mi_var
       have e : (1#64 + t.regs.rbx.toBitVec).toNat = t.regs.rbx.toBitVec.toNat + 1 := by bv_omega
       omega)
    | (mi_inv
       refine ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt', ?_⟩
       rw [BitVec.add_comm]
       exact hrest)

theorem b_1 (hmap : BSpec Names.map mapA 0 mapQ) (hok : b.Ok) : mapInPlaceAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapInPlace.1" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mi_inv at ht
  obtain ⟨M, w, hli, hlt, hrest⟩ := ht
  have hokM : BG.Ok { b with M := M } := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  have hbp := hli.rbp
  have hm : t.regs.rbx.toBitVec.toNat < b.m.toNat := Nat.lt_of_lt_of_le hlt (cs_le_m b.fl)
  have hn : t.regs.rbx.toBitVec.toNat < b.n.toNat := Nat.lt_of_lt_of_le hlt (cs_le_n b.fl)
  have hmax : t.regs.rbx.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hm hok.m
  obtain ⟨_, hM⟩ := BView.mapM hb
  have h_src := BView.rd_src hb
  have h_tgt := BView.rd_tgt hb
  have h_drp := BView.rd_drp hb
  have h_mp := BView.rd_mp hb
  have h_db : rdb t.dmem (b.drp + t.regs.rbx.toBitVec) = Flat.get b.fl.dropped t.regs.rbx.toBitVec :=
    BView.rdb_drp (b := { b with M := M }) hb hokM hm
  have h_dst := MapM.rd_dest hM hmax
  have h_sw : StackSlot.ofWord (rd t.dmem (slotAt b.src t.regs.rbx.toBitVec.toNat))
      = Flat.get b.fl.source t.regs.rbx.toBitVec := BView.rd_sw (b := { b with M := M }) hb hokM hm
  have h_tw : StackSlot.ofWord (rd t.dmem (slotAt b.tgt t.regs.rbx.toBitVec.toNat))
      = Flat.get b.fl.target t.regs.rbx.toBitVec := BView.rd_tw (b := { b with M := M }) hb hokM hn
  unfold rd at h_src h_tgt h_drp h_mp h_dst h_sw h_tw
  unfold rdb at h_db
  have k_src := BView.isSome_src hb
  have k_tgt := BView.isSome_tgt hb
  have k_sw := BView.isSome_sw hb hokM hm
  have k_tw := BView.isSome_tw hb hokM hn
  have k_drp := BView.isSome_drp hb
  have k_db := BView.isSome_drp_byte hb hokM hm
  have k_mp := BView.isSome_mp hb
  have k_dst := MapM.isSome_dest hM hmax
  clear hb hM
  simp only [Names.map] at hmap
  kvcgen64 [hmap]
  all_goals try symexec_norm
  all_goals try simp only [hbp, h_src, h_tgt, h_drp, h_mp, h_db, h_dst, fold_slot, sub_beq_zero,
    neg_one_eq_none, ClosestU.byte_ne0] at *
  vc_by_shape
  | load =>
    first
    | exact k_src
    | exact k_tgt
    | exact k_sw
    | exact k_tw
    | exact k_drp
    | exact k_db
    | exact k_mp
    | exact k_dst
  | closed => decide
  | goto ".LB.MappingBuilder.mapInPlace.0" =>
    have hskip : Flat.inPlaceFrom b.fl M t.regs.rbx.toBitVec
        = Flat.inPlaceFrom b.fl M (t.regs.rbx.toBitVec + 1#64) := by
      first
      | (refine skip_dest (BitVec.lt_def.2 hlt) ?_; with_reducible assumption)
      | (refine skip_drop (BitVec.lt_def.2 hlt) ?_; with_reducible assumption)
      | (refine skip_slot (BitVec.lt_def.2 hlt) (ClosestU.slot_ne h_tw h_sw (jne_true ?_))
         with_reducible assumption)
    cfg_goto
    · exact hli.stk rfl rfl
    · mi_inv
      exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt, hskip.symm.trans hrest⟩
    · left; mi_var; omega
  | other =>
    have hcand := cand_of (fb := b.fl) (M := M) (j := t.regs.rbx.toBitVec)
      (ClosestU.slot_eq h_tw h_sw (jne_false (by with_reducible assumption)))
      (by with_reducible assumption) (by with_reducible assumption)
    refine Kb.vcall (V := BView) (A := mapA) (Q := mapQ) (S := B) (s := s) (ra := ra) (w := w) (F := F) (lo := []) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) (k := 0)
      ?kb rfl rfl ?rdi hokM ?A ?_
    case kb => exact Kb.next hli.kb rfl rfl
    case rdi => exact hli.rbp
    case A => exact ⟨hm, hn⟩
    intro t2 a' lo' w' hkb hl hQ hok' hag
    obtain ⟨hli2, hbx⟩ := LI.after hag (hli.next rfl rfl rfl rfl rfl rfl rfl) hkb hl hQ.2
    have hal : al t2 = code (Flat.mbMap b.fl M t.regs.rbx.toBitVec t.regs.rbx.toBitVec).1 := hQ.1
    clear hQ hkb
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | goto ".LB.MappingBuilder.mapInPlace.0" =>
      have hd := code_eq_zero (hal.symm.trans (al_zero (by rw [Bool.not_eq_false']; with_reducible assumption)))
      cfg_goto
      · exact hli2.stk rfl rfl
      · mi_inv
        refine ⟨_, w', hli2.next rfl rfl rfl rfl rfl rfl rfl, ?_, ?_⟩
        · show t2.regs.rbx.toBitVec.toNat < _; rw [hbx]; exact hlt
        · show Flat.inPlaceFrom _ _ (t2.regs.rbx.toBitVec + 1#64) = _
          rw [hbx]
          exact (from_done (BitVec.lt_def.2 hlt) hcand hd).symm.trans hrest
      · left; mi_var; rw [hbx]; omega
    | goto ".LB.MappingBuilder.mapInPlace.3" =>
      have hd := code_ne_zero fun e => al_ne (by rw [Bool.not_eq_true']; with_reducible assumption) (hal.trans e)
      have hf := hrest.symm.trans (from_fail (BitVec.lt_def.2 hlt) hcand hd)
      cfg_goto
      · exact hli2.stk rfl rfl
      · mi_inv
        exact ⟨_, w', hli2.next rfl rfl rfl rfl rfl rfl rfl, by rw [hf]; exact hal, by rw [hf]; rfl⟩
      · left; mi_var; omega

set_option maxHeartbeats 100000 in
theorem b_2 : mapInPlaceAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapInPlace.2" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mi_inv at ht
  obtain ⟨M, w, hli, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | other =>
    first
    | (right; exact ⟨by mi_var, Nat.lt_succ_self _⟩)
    | (mi_inv
       exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, by rw [hd]; rfl, by rw [hd]⟩)

set_option maxHeartbeats 100000 in
theorem b_3 (hok : b.Ok) : mapInPlaceAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapInPlace.3" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mi_inv at ht
  obtain ⟨M, w, hli, hal, hM⟩ := ht
  obtain ⟨p0, p1⟩ := hli.pop_isSome
  have hokM : BG.Ok { b with M := M } := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact p0
    | with_reducible exact p1
  | retAddr =>
    refine Option.isSome_iff_exists.mpr ⟨ra, Kg.retAddr (P := BView B { b with M := M } ∗ F) (s := s) (fr := fr s w) ?_⟩
    exact hli.pop_kg rfl (by bv_omega) rfl rfl rfl rfl rfl rfl
  | ret =>
    refine Kg.vret (ok := BG.Ok) (a' := { b with M := M })
      (hli.pop_kg rfl (by bv_omega) rfl rfl rfl rfl rfl rfl) rfl hokM
      fun t' _ hax => ⟨?_, by rw [hM]⟩
    simp only [al] at hal ⊢
    rw [hax]
    exact hal

set_option maxHeartbeats 100000 in
theorem b_4 (hok : b.Ok) (hfr : fr₀.length = 3) : mapInPlaceAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapInPlace.4" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mi_inv at ht
  obtain ⟨hk, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | retAddr =>
    exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
  | ret =>
    refine Kg.vret (ok := BG.Ok) (a' := b) (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) hfr hok
      fun t' _ hax => ⟨?_, by rw [hd]⟩
    simp only [al]
    rw [hax, hd]
    rfl

end

end InPlaceU

open InPlaceU in
theorem mapInPlace_unit [Host] [FunDecls] (hmap : BSpec Names.map mapA 0 mapQ) :
    BThm mapInPlaceAsm mapInPlaceA 3 mapInPlaceQ := by
  intro B b F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr₀, hfr, hk0⟩ := hpre.kg ra
  match fr₀, hfr, hk0 with
  | [w₀, w₁, w₂], hfr, hk0 =>
  refine Program.WP.cfg (InPlaceU.Inv B b F s ra [w₀, w₁, w₂]) (InPlaceU.V b) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry B b F s ra _
  · exact b_fn B b F s ra hpre w₀ w₁ w₂ hk0
  · exact b_0 B b F s ra _
  · exact b_1 B b F s ra _ hmap hpre.ok
  · exact b_2 B b F s ra _
  · exact b_3 B b F s ra _ hpre.ok
  · exact b_4 B b F s ra _ hpre.ok hfr

end Bbu.Unit
