import BbuKraken.Unit.TopCall
import BbuKraken.Unit.Loop.Ctor

/-!
# The call of `buildBottomUp` in `build_bottom_up`

Before the call, the memory is the struct and the rest `R0` (`TS`). `topG` is the ghost of the
callee: the struct, the working stack and the target of the inputs, the ops buffer at the entry,
and the spilled bytes `topSpill`. The rest `R0` splits into the working stack, the ops buffer,
the target, the spilled bytes that are not in the target, the stack of the callee and the rest
`FR` (`Carve`). After the call, the bytes outside the struct, the working stack, the ops buffer
and the stack of the callee hold their values of the entry (`get?_call`).
-/

namespace Bbu.Unit
open Bbu.Sep

namespace Top

/-! ## Lists and bytes -/

theorem sep_mk_of {A B : MProp 64} {m mB : Mem 64} (h : (A ∗ MProp.mk (Eq mB)).get m)
    (hB : B.get mB) : (A ∗ B).get m := by
  rw [MProp.get_sep_apply_iff] at h ⊢
  obtain ⟨m₁, m₂, hu, hd, ha, hb⟩ := h
  rw [MProp.get_mk] at hb; subst hb
  exact ⟨m₁, _, hu, hd, ha, hB⟩

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] : (l : List α) → l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: xs => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_eraseDups _⟩
    rw [List.mem_eraseDups, List.mem_filter] at hm
    simp at hm
termination_by l => l.length
decreasing_by all_goals simp_wf; have := List.length_filter_le (fun b => !b == a) xs; omega

theorem spillId_lt {x : StackSlot} {i : Nat} (h : spillId x = some i) : i < 2 ^ 32 := by
  unfold spillId at h; split at h
  · cases h; exact x.payload.isLt
  · cases h

theorem mem_splIds {l : List Word} {i : Nat} (h : i ∈ splIds l) :
    ∃ w ∈ l, spillId (StackSlot.ofWord w) = some i := by
  unfold splIds at h; rw [List.mem_eraseDups, List.mem_filterMap] at h; exact h

theorem inside_of_mem {bs : List (Addr × Nat)} {a b : Addr} {k : Nat} (hm : (a, k) ∈ bs)
    (h : In a k b) : Mem.Blocks.Inside b 1 bs := by
  induction bs with
  | nil => cases hm
  | cons p bs ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact inside_one.mpr (Or.inl h)
    · exact Mem.Blocks.Inside.tail (ih hm)

theorem setWidth_ofNat32 {i : Nat} (hi : i < 2 ^ 32) :
    (BitVec.ofNat 32 i).setWidth 64 = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]; omega

-- Byte `j` of the word at `W`.
theorem rdb_of_rd {m : Mem 64} {W : Addr} (h : (m.loadInt W 8).isSome) {j : Nat} (hj : j < 8) :
    rdb m (W + BitVec.ofNat 64 j) = (rd m W).extractLsb' (8 * j) 8 :=
  Wd.rdb_byte (sep_cut_frame (Wd.cut h)) hj

/-! ## The memory at the entry -/

section
variable {s : MachineData} {ra : Int64}

-- The blocks of the inputs that are not in the frame.
abbrev topNf (s : MachineData) : List (Addr × Nat) := topOut s ++ (dstArg s, 8 * mArg s) :: topRd s

theorem mem_topIn {p : Addr × Nat} (h : p ∈ topNf s) : p ∈ topOut s ++ topIn s := by
  simp only [topIn, List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

-- `pushRa` changes only the frame.
theorem get?_m0 (hp : TopPre s) {b : Addr} (hb : ¬In (rsp s - BitVec.ofNat 64 topF) topF b) :
    (s.pushRa ra).dmem.get? b = s.dmem.get? b := by
  have := hp.rsp_ge
  simp only [In, topF_eq] at hb
  rw [MachineData.dmem_pushRa]
  exact Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj => by simp only [rsp] at *; bv_omega

theorem get?_nf (hp : TopPre s) (hm : TopMem s) {A b : Addr} {N : Nat} (hA : (A, N) ∈ topNf s)
    (hb : In A N b) : (s.pushRa ra).dmem.get? b = s.dmem.get? b :=
  get?_m0 hp fun hf => hm.disj_frame b (inside_one_nil.mpr hf) (inside_of_mem hA hb)

theorem ld_m0 (hp : TopPre s) (hm : TopMem s) {A a : Addr} {N k : Nat} (hA : (A, N) ∈ topNf s)
    (hin : (a - A).toNat + k ≤ N) : (s.pushRa ra).dmem.loadInt a k = s.dmem.loadInt a k :=
  ld_eq (fun _ hb => get?_nf hp hm hA hb) hin

theorem rd_m0 (hp : TopPre s) (hm : TopMem s) {A a : Addr} {N : Nat} (hA : (A, N) ∈ topNf s)
    (hin : (a - A).toNat + 8 ≤ N) : rd (s.pushRa ra).dmem a = rd s.dmem a :=
  rd_eq (fun _ hb => get?_nf hp hm hA hb) hin

theorem rdb_m0 (hp : TopPre s) (hm : TopMem s) {A a : Addr} {N : Nat} (hA : (A, N) ∈ topNf s)
    (hin : (a - A).toNat + 1 ≤ N) : rdb (s.pushRa ra).dmem a = rdb s.dmem a :=
  rdb_eq (fun _ hb => get?_nf hp hm hA hb) hin

theorem isSome_s (hm : TopMem s) {A a : Addr} {N k : Nat} (hA : (A, N) ∈ topNf s)
    (hin : (a - A).toNat + k ≤ N) : (s.dmem.loadInt a k).isSome :=
  Mem.Mapped.loadInt_isSome (bs := [(A, N)])
    (fun b hb => hm.mapped b (inside_of_mem (mem_topIn hA) (inside_one_nil.mp hb))) (Or.inl hin)

theorem isSome_m0 (hp : TopPre s) (hm : TopMem s) {A a : Addr} {N k : Nat} (hA : (A, N) ∈ topNf s)
    (hin : (a - A).toNat + k ≤ N) : ((s.pushRa ra).dmem.loadInt a k).isSome := by
  rw [ld_m0 hp hm hA hin]; exact isSome_s hm hA hin

theorem data_nf : (dataArg s, 8 * nArg s) ∈ topNf s := by simp [topOut]
theorem ops_nf : (opsArg s, 72 * nArg s) ∈ topNf s := by simp [topOut]
theorem tgt_nf : (tgtArg s, 8 * nArg s) ∈ topNf s := by simp [topRd]

end

/-! ## The records of the ops buffer -/

-- The word at byte 4 of a record: payload, kind, valueOpcode and the padding.
def pack (p : BitVec 32) (k o : BitVec 8) (q : BitVec 16) : Word := q ++ o ++ k ++ p

section
variable (p : BitVec 32) (k o : BitVec 8) (q : BitVec 16)

theorem pack_0 : (pack p k o q).extractLsb' 0 32 = p := by unfold pack; bv_decide
theorem pack_32 : (pack p k o q).extractLsb' 32 8 = k := by unfold pack; bv_decide
theorem pack_40 : (pack p k o q).extractLsb' 40 8 = o := by unfold pack; bv_decide
theorem pack_48 : (pack p k o q).extractLsb' 48 16 = q := by unfold pack; bv_decide

end

theorem OpM.wd (a : Addr) (r : OpR) :
    OpM a r = B8 a r.op.kind ∗ B8 (a + 1#64) r.op.depth ∗ B16 (a + 2#64) r.pad2
      ∗ Wd (a + 4#64) (pack r.op.slot.payload r.op.slot.kind r.op.slot.valueOpcode r.pad10) := by
  have a8 : a + 4#64 + 4#64 = a + 8#64 := by bv_decide
  have a9 : a + 4#64 + 5#64 = a + 9#64 := by bv_decide
  have a10 : a + 4#64 + 6#64 = a + 10#64 := by bv_decide
  rw [Wd.split, pack_0, pack_32, pack_40, pack_48, a8, a9, a10]; rfl

section
variable {a : Addr} {r : OpR} {F : MProp 64} {m : Mem 64}

theorem OpM.rd_slot (h : (OpM a r ∗ F).get m) : StackSlot.ofWord (rd m (a + 4#64)) = r.op.slot := by
  rw [rd_of_eq h (by rw [OpM.wd]; ecancel)]
  simp only [StackSlot.ofWord, pack_0, pack_32, pack_40]

theorem OpM.rdb_kind (h : (OpM a r ∗ F).get m) : rdb m a = r.op.kind := by
  obtain ⟨R, e⟩ : ∃ R, OpM a r ∗ F = B8 a r.op.kind ∗ R := ⟨_, by unfold OpM; ecancel⟩
  exact B8.rdb (e ▸ h)

theorem OpM.rdb_depth (h : (OpM a r ∗ F).get m) : rdb m (a + 1#64) = r.op.depth := by
  obtain ⟨R, e⟩ : ∃ R, OpM a r ∗ F = B8 (a + 1#64) r.op.depth ∗ R := ⟨_, by unfold OpM; ecancel⟩
  exact B8.rdb (e ▸ h)

end

/-! ## The ghost at the call -/

section
variable (s : MachineData) (ra : Int64)

def stkV : Vector Word (nArg s) := Vector.ofFn fun i => rd s.dmem (wordAt (dataArg s) i)
def tgtV : Vector Word (nArg s) := Vector.ofFn fun i => rd s.dmem (wordAt (tgtArg s) i)
def opsV : Vector OpR (6 * nArg s) :=
  Vector.ofFn fun i => rdOp (s.pushRa ra).dmem (Sep.opAt (opsArg s) i)

def topG : G :=
  ⟨hdr s ra (Dm s ra) (Pm s ra) (Flat.countNone (Pm s ra) (nArg s) 0), 0, 0, stkV s, opsV s ra,
    tgtV s,
    topSpill s⟩

theorem View_topG : View (topS s) (topG s ra) =
    Em (topS s) (hdr s ra (Dm s ra) (Pm s ra) (Flat.countNone (Pm s ra) (nArg s) 0))
      ∗ Arr (dataArg s) (stkV s).toList ∗ Ops (opsArg s) 0 (opsV s ra).toList
      ∗ Arr (tgtArg s) (tgtV s).toList
      ∗ Spl (splArg s) (topSpill s) (splOut (tgtArg s) (splArg s) (nArg s) (splIds (tgtV s).toList)) :=
  rfl

theorem vec_map {n : Nat} (v : Vector Word n) :
    vec (v.toList.map StackSlot.ofWord) =
      Vector.ofFn fun i : Fin MAX_N => if h : i.val < n then StackSlot.ofWord v[i.val] else default := by
  ext i hi
  by_cases h : i < n <;> simp [vec, h]

theorem data_topG : (flat (topG s ra)).data = flatData s := by
  show vec ((stkV s).toList.map StackSlot.ofWord) = _
  rw [vec_map]; ext i hi
  by_cases h : i < nArg s <;> simp [h, stkV, flatData]

theorem tgt_topG : (flat (topG s ra)).target = flatTgt s := by
  show vec ((tgtV s).toList.map StackSlot.ofWord) = _
  rw [vec_map]; ext i hi
  by_cases h : i < nArg s <;> simp [h, tgtV, flatTgt]

theorem flat_topG : flat (topG s ra) = topCtor s (u0 s ra) := by
  unfold topCtor; rw [Flat.ctor_folds, ← data_topG s ra, ← tgt_topG s ra]
  rfl

end

/-! ## The parts of the memory at the entry -/

section
variable (s : MachineData) (ra : Int64)

-- The stack of the callee: 2068 free words and the return slot, under the struct.
def rStk (b : Addr) : Prop := In (topS s - 8#64 - BitVec.ofNat 64 (8 * 2068)) (8 * 2068 + 8) b

-- The spilled bytes that are not in the target.
def rSpl (b : Addr) : Prop :=
  ∃ i ∈ splOut (tgtArg s) (splArg s) (nArg s) (splIds (tgtV s).toList),
    b = splArg s + BitVec.ofNat 64 i

-- The parts of the callee outside the struct.
def rIn (b : Addr) : Prop :=
  In (dataArg s) (8 * nArg s) b ∨ In (opsArg s) (72 * nArg s) b ∨ In (tgtArg s) (8 * nArg s) b
    ∨ rSpl s b ∨ rStk s b

-- The frame `F` of the call: the bytes outside the struct and outside the parts of the callee.
def RF (b : Addr) : Prop := ¬In (topS s) offLoc b ∧ ¬rIn s b

noncomputable def FR : MProp 64 := MProp.mk (Eq (cut (s.pushRa ra).dmem (RF s)))

-- The free words of the callee at the entry.
def frL : List Word := (List.range 2068).map fun i =>
  rd (s.pushRa ra).dmem (topS s - 8#64 - BitVec.ofNat 64 (8 * 2068) + BitVec.ofNat 64 (8 * i))

theorem frL_length : (frL s ra).length = 2068 := by simp [frL]

end

section
variable {s : MachineData} {ra : Int64}

theorem tgt_rd : (tgtArg s, 8 * nArg s) ∈ topRd s := by simp [topRd]

theorem spl_spl {i : Nat} (h : i ∈ splIds (tgtV s).toList) :
    (splArg s + BitVec.ofNat 64 i, 1) ∈ topSpl s := by
  obtain ⟨w, hw, he⟩ := mem_splIds h
  simp only [tgtV, Vector.toList_ofFn, List.mem_ofFn] at hw
  obtain ⟨k, rfl⟩ := hw
  unfold topSpl
  rw [List.mem_filterMap]
  exact ⟨k.val, List.mem_range.mpr k.isLt, by unfold topTgt; rw [he]; rfl⟩

theorem spl_rd {i : Nat} (h : i ∈ splIds (tgtV s).toList) :
    (splArg s + BitVec.ofNat 64 i, 1) ∈ topRd s := by
  unfold topRd; exact List.mem_cons_of_mem _ (spl_spl h)

theorem spl_mem {i : Nat} (h : i ∈ splIds (tgtV s).toList) :
    (splArg s + BitVec.ofNat 64 i, 1) ∈ topNf s :=
  List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (spl_rd h)))

theorem spl_in {b : Addr} (h : rSpl s b) :
    ∃ i ∈ splIds (tgtV s).toList, b = splArg s + BitVec.ofNat 64 i := by
  obtain ⟨i, hi, rfl⟩ := h
  unfold splOut at hi
  exact ⟨i, (List.mem_filter.mp hi).1, rfl⟩

theorem nf_fr (hm : TopMem s) {A b : Addr} {N : Nat} (hA : (A, N) ∈ topNf s) (hb : In A N b) :
    ¬In (rsp s - BitVec.ofNat 64 topF) topF b :=
  fun hf => hm.disj_frame b (inside_one_nil.mpr hf) (inside_of_mem hA hb)

theorem stk_fr (hp : TopPre s) {b : Addr} (h : rStk s b) : In (rsp s - BitVec.ofNat 64 topF) topF b := by
  have := hp.rsp_ge
  unfold rStk In topS at *; simp only [topF_eq, offOps] at *; bv_omega

theorem stk_S {b : Addr} (h : rStk s b) : ¬In (topS s) offLoc b := by
  unfold rStk In at *; simp only [offLoc] at *; bv_omega

theorem S_fr (hp : TopPre s) {b : Addr} (h : In (topS s) offLoc b) :
    In (rsp s - BitVec.ofNat 64 topF) topF b :=
  in_frame_of_S hp (by unfold In at h ⊢; simp only [offLoc, offOps] at h ⊢; omega)

theorem nf_S (hp : TopPre s) (hm : TopMem s) {A b : Addr} {N : Nat} (hA : (A, N) ∈ topNf s)
    (hb : In A N b) : ¬In (topS s) offLoc b :=
  fun h => nf_fr hm hA hb (S_fr hp h)

theorem nf_stk (hp : TopPre s) (hm : TopMem s) {A b : Addr} {N : Nat} (hA : (A, N) ∈ topNf s)
    (hb : In A N b) : ¬rStk s b :=
  fun h => nf_fr hm hA hb (stk_fr hp h)

theorem spl_stk (hp : TopPre s) (hm : TopMem s) {b : Addr} (h1 : rSpl s b) (h2 : rStk s b) : False := by
  obtain ⟨i, hi, rfl⟩ := spl_in h1
  exact nf_stk hp hm (spl_mem hi) (in_one.mpr rfl) h2

theorem tgt_spl {b : Addr} (h1 : In (tgtArg s) (8 * nArg s) b) (h2 : rSpl s b) : False := by
  obtain ⟨i, hi, rfl⟩ := h2
  unfold splOut at hi
  have := of_decide_eq_true (List.mem_filter.mp hi).2
  unfold In at h1; omega

theorem rIn_S (hp : TopPre s) (hm : TopMem s) {b : Addr} (h : rIn s b) : ¬In (topS s) offLoc b := by
  rcases h with h | h | h | h | h
  · exact nf_S hp hm data_nf h
  · exact nf_S hp hm ops_nf h
  · exact nf_S hp hm tgt_nf h
  · obtain ⟨i, hi, rfl⟩ := spl_in h
    exact nf_S hp hm (spl_mem hi) (in_one.mpr rfl)
  · exact stk_S h

/-! ## The parts as atoms -/

theorem data_cut (hp : TopPre s) (hm : TopMem s) :
    (Arr (dataArg s) (stkV s).toList).get (cut (s.pushRa ra).dmem (In (dataArg s) (8 * nArg s))) := by
  have hl := hm.data_lt
  have h := Arr.cut (m := (s.pushRa ra).dmem) (a := dataArg s) (stkV s).toList
    (by rw [Vector.length_toList]; omega) fun i hi => by
      have hi' : i < nArg s := by simpa using hi
      have hin : (dataArg s + BitVec.ofNat 64 (8 * i) - dataArg s).toNat + 8 ≤ 8 * nArg s := by
        rw [add_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      refine ⟨isSome_m0 hp hm data_nf hin, ?_⟩
      rw [rd_m0 hp hm data_nf hin]; simp [stkV]
  rwa [Vector.length_toList] at h

theorem tgt_cut (hp : TopPre s) (hm : TopMem s) :
    (Arr (tgtArg s) (tgtV s).toList).get (cut (s.pushRa ra).dmem (In (tgtArg s) (8 * nArg s))) := by
  have hl := hm.tgt_lt
  have h := Arr.cut (m := (s.pushRa ra).dmem) (a := tgtArg s) (tgtV s).toList
    (by rw [Vector.length_toList]; omega) fun i hi => by
      have hi' : i < nArg s := by simpa using hi
      have hin : (tgtArg s + BitVec.ofNat 64 (8 * i) - tgtArg s).toNat + 8 ≤ 8 * nArg s := by
        rw [add_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      refine ⟨isSome_m0 hp hm tgt_nf hin, ?_⟩
      rw [rd_m0 hp hm tgt_nf hin]; simp [tgtV]
  rwa [Vector.length_toList] at h

theorem ops_cut (hp : TopPre s) (hm : TopMem s) :
    (Ops (opsArg s) 0 (opsV s ra).toList).get (cut (s.pushRa ra).dmem (In (opsArg s) (72 * nArg s))) := by
  have hl := hm.ops_lt
  have h := Ops.cut (m := (s.pushRa ra).dmem) (o := opsArg s) 0 (opsV s ra).toList
    (by rw [Vector.length_toList]; omega) fun i hi => by
      have hi' : i < 6 * nArg s := by simpa using hi
      have hin : (Sep.opAt (opsArg s) (0 + i) - opsArg s).toNat + 12 ≤ 72 * nArg s := by
        unfold Sep.opAt
        rw [add_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      exact ⟨isSome_m0 hp hm ops_nf hin, by simp [opsV]⟩
  have e : ∀ b, Rng (opsArg s) (12 * 0) (12 * (opsV s ra).toList.length) b ↔ In (opsArg s) (72 * nArg s) b :=
    fun b => by
      simp only [Rng, In, Vector.length_toList]
      constructor <;> intro h <;> omega
  rwa [cut_congr _ e] at h

theorem spl_cut (hp : TopPre s) (hm : TopMem s) :
    (Spl (splArg s) (topSpill s) (splOut (tgtArg s) (splArg s) (nArg s) (splIds (tgtV s).toList))).get
      (cut (s.pushRa ra).dmem (rSpl s)) :=
  Spl.cut _ (by unfold splOut splIds; exact List.Pairwise.filter _ (nodup_eraseDups _)) fun i hi => by
    have hi' : i ∈ splIds (tgtV s).toList := by unfold splOut at hi; exact (List.mem_filter.mp hi).1
    obtain ⟨w, -, he⟩ := mem_splIds hi'
    have h32 := spillId_lt he
    have hin : (splArg s + BitVec.ofNat 64 i - (splArg s + BitVec.ofNat 64 i)).toNat + 1 ≤ 1 := by simp
    refine ⟨by omega, isSome_m0 hp hm (spl_mem hi') hin, ?_⟩
    rw [rdb_m0 hp hm (spl_mem hi') hin]; unfold topSpill; rw [setWidth_ofNat32 h32]

theorem stk_cut (hp : TopPre s) :
    (Stk (topS s) (frL s ra) (rd (s.pushRa ra).dmem (topS s - 8#64))).get
      (cut (s.pushRa ra).dmem (rStk s)) := by
  have := hp.rsp_ge
  have ld : ∀ a : Addr, (a - (rsp s - BitVec.ofNat 64 topF)).toNat + 8 ≤ topF →
      ((s.pushRa ra).dmem.loadInt a 8).isSome := fun a ha =>
    (frame0 hp).loadInt_isSome (Or.inl ha)
  have hf : ∀ i (hi : i < (frL s ra).length),
      ((s.pushRa ra).dmem.loadInt (topS s - 8#64 - BitVec.ofNat 64 (8 * (frL s ra).length)
        + BitVec.ofNat 64 (8 * i)) 8).isSome ∧
      rd (s.pushRa ra).dmem (topS s - 8#64 - BitVec.ofNat 64 (8 * (frL s ra).length)
        + BitVec.ofNat 64 (8 * i)) = (frL s ra)[i] := by
    intro i hi
    have hi' : i < 2068 := frL_length s ra ▸ hi
    simp only [frL_length]
    refine ⟨ld _ ?_, by simp [frL]⟩
    unfold topS; simp only [topF_eq, offOps]; bv_omega
  have hv := ld (topS s - 8#64) (by unfold topS; simp only [topF_eq, offOps]; bv_omega)
  have h := Stk.cut (by rw [frL_length]; decide) hf hv
  rw [frL_length] at h; exact h

theorem fr_cut : (FR s ra).get (cut (s.pushRa ra).dmem (RF s)) := by
  unfold FR; rw [MProp.get_mk]

-- The rest `R0` at the entry splits into the parts of the callee and the frame `FR`.
theorem rest_cut (hp : TopPre s) (hg : TopGuard s) :
    (Arr (dataArg s) (stkV s).toList ∗ Ops (opsArg s) 0 (opsV s ra).toList
      ∗ Arr (tgtArg s) (tgtV s).toList
      ∗ Spl (splArg s) (topSpill s) (splOut (tgtArg s) (splArg s) (nArg s) (splIds (tgtV s).toList))
      ∗ Stk (topS s) (frL s ra) (rd (s.pushRa ra).dmem (topS s - 8#64)) ∗ FR s ra).get
      (cut (s.pushRa ra).dmem fun b => ¬In (topS s) offLoc b) := by
  have hm := hp.mem hg
  have h5 := sep_cut (R := fun b => rStk s b ∨ RF s b) (stk_cut (ra := ra) hp) (fr_cut (ra := ra))
    (fun b h1 h2 => h2.2 (Or.inr (Or.inr (Or.inr (Or.inr h1))))) (fun _ => Iff.rfl)
  have h4 := sep_cut (R := fun b => rSpl s b ∨ rStk s b ∨ RF s b) (spl_cut (ra := ra) hp hm) h5
    (fun b h1 h2 => by
      rcases h2 with h2 | h2
      · exact spl_stk hp hm h1 h2
      · exact h2.2 (Or.inr (Or.inr (Or.inr (Or.inl h1))))) (fun _ => Iff.rfl)
  have h3 := sep_cut (R := fun b => In (tgtArg s) (8 * nArg s) b ∨ rSpl s b ∨ rStk s b ∨ RF s b)
    (tgt_cut (ra := ra) hp hm) h4
    (fun b h1 h2 => by
      rcases h2 with h2 | h2 | h2
      · exact tgt_spl h1 h2
      · exact nf_stk hp hm tgt_nf h1 h2
      · exact h2.2 (Or.inr (Or.inr (Or.inl h1)))) (fun _ => Iff.rfl)
  have h2 := sep_cut (R := fun b => In (opsArg s) (72 * nArg s) b ∨ In (tgtArg s) (8 * nArg s) b
      ∨ rSpl s b ∨ rStk s b ∨ RF s b)
    (ops_cut (ra := ra) hp hm) h3
    (fun b h1 h2 => by
      rcases h2 with h2 | h2 | h2 | h2
      · exact hm.disj_ops b (inside_one_nil.mpr h1) (inside_of_mem tgt_rd h2)
      · obtain ⟨i, hi, rfl⟩ := spl_in h2
        exact hm.disj_ops _ (inside_one_nil.mpr h1) (inside_of_mem (spl_rd hi) (in_one.mpr rfl))
      · exact nf_stk hp hm ops_nf h1 h2
      · exact h2.2 (Or.inr (Or.inl h1))) (fun _ => Iff.rfl)
  refine sep_cut (data_cut (ra := ra) hp hm) h2 (fun b h1 h2 => ?_) (fun b => ?_)
  · rcases h2 with h2 | h2 | h2 | h2 | h2
    · exact hm.disj_data b (inside_one_nil.mpr h1) (inside_one.mpr (Or.inl h2))
    · exact hm.disj_data b (inside_one_nil.mpr h1) (inside_one.mpr (Or.inr (inside_of_mem tgt_rd h2)))
    · obtain ⟨i, hi, rfl⟩ := spl_in h2
      exact hm.disj_data _ (inside_one_nil.mpr h1)
        (inside_one.mpr (Or.inr (inside_of_mem (spl_rd hi) (in_one.mpr rfl))))
    · exact nf_stk hp hm data_nf h1 h2
    · exact h2.2 (Or.inl h1)
  · constructor
    · intro hS
      by_cases hr : rIn s b
      · rcases hr with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hS, hr⟩))))
    · intro h
      rcases h with h | h | h | h | h | h
      · exact rIn_S hp hm (Or.inl h)
      · exact rIn_S hp hm (Or.inr (Or.inl h))
      · exact rIn_S hp hm (Or.inr (Or.inr (Or.inl h)))
      · exact rIn_S hp hm (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact rIn_S hp hm (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact h.1

/-! ## The precondition of the callee -/

theorem topG_ok (hp : TopPre s) (hg : TopGuard s) : (topG s ra).Ok where
  len := hg.1
  n := hg.2
  xs := hg.2
  xo := Nat.zero_le _
  nops := by simp [topG, hdr]
  spl := by
    have hm := hp.mem hg
    have hl := hm.tgt_lt
    intro i hi k hk j hj he
    have hk' : k < nArg s := hk
    show topSpill s (BitVec.ofNat 32 i) = (tgtV s)[k].extractLsb' (8 * j) 8
    obtain ⟨w, -, hw⟩ := mem_splIds hi
    have h32 := spillId_lt hw
    unfold topSpill; rw [setWidth_ofNat32 h32]
    change splArg s + BitVec.ofNat 64 i = tgtArg s + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j at he
    rw [he]
    have hin : (wordAt (tgtArg s) k - tgtArg s).toNat + 8 ≤ 8 * nArg s := by
      unfold wordAt; rw [add_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [rdb_of_rd (isSome_s hm tgt_nf hin) hj]
    simp [tgtV]

variable {t : MachineData} {L : Loc}

theorem get_congr {X Y : MProp 64} {m : Mem 64} (h : X.get m) (e : X = Y) : Y.get m := e ▸ h

theorem Lc.single (S : Addr) (L : Loc) : Single (Lc S L) :=
  (Wd.single _ _).sep ((Wd.single _ _).sep ((Arr.single _ _).sep (Arr.single _ _)))

theorem in_loc {S b : Addr} (h : In S EmSize b) : In S offLoc b := by
  unfold In at *; simp only [EmSize, offLoc] at *; omega

-- The frame of the call: the locals `Lc` and the bytes `FR`.
noncomputable abbrev FL (s : MachineData) (ra : Int64) (L : Loc) : MProp 64 := Lc (topS s) L ∗ FR s ra

theorem pre_mem (hs : TS s ra (hdr s ra (Dm s ra) (Pm s ra) (Flat.countNone (Pm s ra) (nArg s) 0)) L t)
    (hp : TopPre s) :
    (View (topS s) (topG s ra) ∗ Stk (topS s) (frL s ra) (rd (s.pushRa ra).dmem (topS s - 8#64))
      ∗ FL s ra L).get t.dmem := by
  have h1 := sep_mk_of (A := Em (topS s) _ ∗ Lc (topS s) L)
    (by rw [MProp.sep_assoc]; exact hs.mem) (rest_cut hp hs.g)
  rw [View_topG]
  exact get_congr h1 (by unfold FL; ecancel)

theorem topPre (hs : TS s ra (hdr s ra (Dm s ra) (Pm s ra) (Flat.countNone (Pm s ra) (nArg s) 0)) L t)
    (hp : TopPre s) {c : MachineData} (hd : c.dmem = t.dmem) (hdi : c.regs.rdi = t.regs.rsp)
    (hsp : c.regs.rsp = t.regs.rsp) : Sep.Pre (topS s) (topG s ra) (FL s ra L) loopA 2068 c where
  rdi := by show c.regs.rdi.toBitVec = _; rw [hdi]; exact hs.sp
  ok := topG_ok hp hs.g
  mem := by
    have hr : rsp c = topS s := by show c.regs.rsp.toBitVec = _; rw [hsp]; exact hs.sp
    refine ⟨frL s ra, rd (s.pushRa ra).dmem (topS s - 8#64), frL_length s ra, ?_⟩
    rw [hr, hd]; exact pre_mem hs hp
  args := by
    have e : flat (topG s ra) = Flat.ctor (flat (topG s ra)).data (topG s ra).h.len
        (flat (topG s ra)).target (topG s ra).h.n (flatDest s) (topG s ra).spl (u0 s ra) := by
      rw [data_topG, tgt_topG]; exact flat_topG s ra
    have ok := topG_ok (ra := ra) hp hs.g
    show Flat.HInv _ 0#64 _
    rw [e]
    exact Flat.HInv.ctor (BitVec.le_def.mpr ok.len) ok.n (hp.mem hs.g).dests

end

/-! ## The memory after the call -/

-- The parts that the callee writes, and the parts that it keeps.
theorem view_split (S : Addr) (g : G) (sp : Addr) (fr : List Word) (v : Word) (F : MProp 64) :
    View S g ∗ Stk sp fr v ∗ F =
      (Em S g.h ∗ Arr g.h.data g.stk.toList ∗ Ops g.h.ops 0 g.ops.toList ∗ Stk sp fr v)
        ∗ (Arr g.h.tgt g.tgt.toList
          ∗ Spl g.h.spl g.spl (splOut g.h.tgt g.h.spl g.h.n.toNat (splIds g.tgt.toList)) ∗ F) := by
  unfold View; ecancel

theorem own_A (S : Addr) (g : G) (sp : Addr) (fr : List Word) (v : Word) (hn : g.h.n.toNat ≤ MAX_N)
    (hxs : g.xs = 0) (hxo : g.xo = 0)
    (hf : 8 * fr.length + 8 ≤ 2 ^ 64) :
    Own (Em S g.h ∗ Arr g.h.data g.stk.toList ∗ Ops g.h.ops 0 g.ops.toList ∗ Stk sp fr v)
      (fun b => In S EmSize b ∨ In g.h.data (8 * g.h.n.toNat) b ∨ In g.h.ops (72 * g.h.n.toNat) b
        ∨ In (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length)) (8 * fr.length + 8) b) := by
  unfold MAX_N at hn
  have ha := Arr.own g.h.data g.stk.toList (by rw [Vector.length_toList]; omega)
  have ho := Ops.own (o := g.h.ops) 0 g.ops.toList (by rw [Vector.length_toList]; omega)
  rw [Vector.length_toList] at ha ho
  refine ((Em.own S g.h).sep (ha.sep (ho.sep (Stk.own sp fr v hf)))).congr fun b => ?_
  have e : Rng g.h.ops (12 * 0) (12 * (6 * g.h.n.toNat + g.xo)) b ↔ In g.h.ops (72 * g.h.n.toNat) b := by
    unfold Rng In; rw [hxo]; constructor <;> intro h <;> omega
  have d : In g.h.data (8 * (g.h.n.toNat + g.xs)) b ↔ In g.h.data (8 * g.h.n.toNat) b := by rw [hxs]; rfl
  rw [e, d]

section
variable {S sp : Addr} {g g' : G} {fr fr' : List Word} {v v' : Word} {F : MProp 64} {m m' : Mem 64}

-- A call that keeps `Keep g g'` and the frame `F` keeps the bytes outside the struct, the working
-- stack, the ops buffer and the stack of the callee.
theorem call_frame (hk : Keep g g') (hl : fr'.length = fr.length) (hf : 8 * fr.length + 8 ≤ 2 ^ 64)
    (hn : g.h.n.toNat ≤ MAX_N) (hxs : g.xs = 0) (hxo : g.xo = 0) (hF : Single F)
    (h : (View S g ∗ Stk sp fr v ∗ F).get m) (h' : (View S g' ∗ Stk sp fr' v' ∗ F).get m') {b : Addr}
    (hb : ¬(In S EmSize b ∨ In g.h.data (8 * g.h.n.toNat) b ∨ In g.h.ops (72 * g.h.n.toNat) b
      ∨ In (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length)) (8 * fr.length + 8) b)) :
    m'[b]? = m[b]? := by
  rw [view_split] at h h'
  have eB : Arr g'.h.tgt g'.tgt.toList
        ∗ Spl g'.h.spl g'.spl (splOut g'.h.tgt g'.h.spl g'.h.n.toNat (splIds g'.tgt.toList)) ∗ F
      = Arr g.h.tgt g.tgt.toList
        ∗ Spl g.h.spl g.spl (splOut g.h.tgt g.h.spl g.h.n.toNat (splIds g.tgt.toList)) ∗ F := by
    rw [hk.tgt, hk.tgtp, hk.splp, hk.spl, hk.n]
  rw [eB] at h'
  have hA' : Own (Em S g'.h ∗ Arr g'.h.data g'.stk.toList ∗ Ops g'.h.ops 0 g'.ops.toList ∗ Stk sp fr' v')
      (fun b => In S EmSize b ∨ In g.h.data (8 * g.h.n.toNat) b ∨ In g.h.ops (72 * g.h.n.toNat) b
        ∨ In (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length)) (8 * fr.length + 8) b) :=
    (own_A S g' sp fr' v' (by rw [hk.n]; exact hn) (hk.xs.trans hxs) (hk.xo.trans hxo)
      (by rw [hl]; exact hf)).congr fun b => by
      rw [hk.data, hk.ops, hk.n, hl]
  exact get?_call h h' (own_A S g sp fr v hn hxs hxo hf) hA' ((Arr.single _ _).sep ((Spl.single _ _ _).sep hF)) hb

-- The bytes of the struct, the working stack, the ops buffer and the stack are in the memory.
theorem view_mem (hn : g.h.n.toNat ≤ MAX_N) (hxs : g.xs = 0) (hxo : g.xo = 0) (hf : 8 * fr.length + 8 ≤ 2 ^ 64)
    (h : (View S g ∗ Stk sp fr v ∗ F).get m) {b : Addr}
    (hb : In S EmSize b ∨ In g.h.data (8 * g.h.n.toNat) b ∨ In g.h.ops (72 * g.h.n.toNat) b
      ∨ In (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length)) (8 * fr.length + 8) b) : b ∈ m := by
  rw [view_split] at h; exact mem_own h (own_A S g sp fr v hn hxs hxo hf) hb

end

-- The bytes that the callee can write.
def rD (s : MachineData) (b : Addr) : Prop :=
  In (topS s) offLoc b ∨ In (dataArg s) (8 * nArg s) b ∨ In (opsArg s) (72 * nArg s) b ∨ rStk s b

section
variable {s : MachineData} {ra : Int64} {t : MachineData} {L : Loc}

theorem rD_fr (hm : TopMem s) {b : Addr} (hf : In (rsp s - BitVec.ofNat 64 topF) topF b)
    (hS : ¬In (topS s) offLoc b) (hk : ¬rStk s b) : ¬rD s b := by
  rintro (h | h | h | h)
  · exact hS h
  · exact nf_fr hm data_nf h hf
  · exact nf_fr hm ops_nf h hf
  · exact hk h

theorem nfr_D (hp : TopPre s) {b : Addr} (hf : ¬In (rsp s - BitVec.ofNat 64 topF) topF b)
    (hd : ¬In (dataArg s) (8 * nArg s) b) (ho : ¬In (opsArg s) (72 * nArg s) b) : ¬rD s b := by
  rintro (h | h | h | h)
  · exact hf (S_fr hp h)
  · exact hd h
  · exact ho h
  · exact hf (stk_fr hp h)

-- The return address of `build_bottom_up`.
theorem ra_D (hp : TopPre s) (hm : TopMem s) {b : Addr} (hb : In (rsp s - 8#64) 8 b) : ¬rD s b := by
  have := hp.rsp_ge
  refine rD_fr hm ?_ ?_ ?_
  · unfold In at *; simp only [topF_eq]; bv_omega
  · unfold In topS at *; simp only [offLoc, offOps]; bv_omega
  · unfold rStk In topS at *; simp only [offOps] at *; bv_omega

-- The word `blocked` at `rsp + 8`.
theorem blkp_fr (hp : TopPre s) {b : Addr} (hb : In (rsp s + 8#64) 8 b) :
    ¬In (rsp s - BitVec.ofNat 64 topF) topF b := by
  have := hp.rsp_ge
  unfold In at *; simp only [topF_eq]; bv_omega

theorem blkp_D (hp : TopPre s) (hm : TopMem s) {b : Addr} (hb : In (rsp s + 8#64) 8 b) : ¬rD s b := by
  refine nfr_D hp (blkp_fr hp hb) (fun h => ?_) (fun h => ?_)
  · exact hm.disj_blkp b (inside_one_nil.mpr hb) (inside_one.mpr (Or.inl h))
  · exact hm.disj_blkp b (inside_one_nil.mpr hb) (inside_one.mpr (Or.inr (inside_one_nil.mpr h)))

-- The memory `blocked`.
theorem blk_D (hp : TopPre s) (hm : TopMem s) {b : Addr} (hb : Mem.Blocks.Inside b 1 [(blkArg s, 16)]) :
    ¬rD s b := by
  refine nfr_D hp (fun h => fr_blk hm (inside_one_nil.mpr h) hb) (fun h => ?_) (fun h => ?_)
  · exact hm.disj_blk b hb (inside_one.mpr (Or.inl h))
  · exact hm.disj_blk b hb (inside_one.mpr (Or.inr (inside_one_nil.mpr h)))

-- `Sep.Post` of the call gives `TQ`: the bytes outside `rD` keep their values (`call_frame`), and
-- the view of the callee gives the struct words, the ops buffer and the working stack.
theorem topPost (hs : TS s ra (hdr s ra (Dm s ra) (Pm s ra) (Flat.countNone (Pm s ra) (nArg s) 0)) L t)
    (hp : TopPre s) {c : MachineData} (hsp : c.regs.rsp = t.regs.rsp)
    (e1 : c.regs.rbx = t.regs.rbx) (e2 : c.regs.rbp = t.regs.rbp) (e3 : c.regs.r12 = t.regs.r12)
    (e4 : c.regs.r13 = t.regs.r13) (e5 : c.regs.r14 = t.regs.r14) (e6 : c.regs.r15 = t.regs.r15)
    {s' : MachineData}
    (hpost : Sep.Post (topS s) (FL s ra L) 2068 (fun g' t' => loopQ (topG s ra) g' c t') c s')
    (hag : Sep.mod.Agree c s') :
    TQ s ra (Flat.buildBottomUp (flat (topG s ra))).1 (Flat.buildBottomUp (flat (topG s ra))).2 s'
      ∧ al s' = code (Flat.buildBottomUp (flat (topG s ra))).1 := by
  obtain ⟨g', fr', v', ⟨hkeep, hflat, hal⟩, hok', hlen, hmem'⟩ := hpost
  have hm := hp.mem hs.g
  have hok := topG_ok (ra := ra) hp hs.g
  have hr : rsp c = topS s := by show c.regs.rsp.toBitVec = _; rw [hsp]; exact hs.sp
  rw [hr] at hmem'
  have hmem0 := pre_mem hs hp
  have hcall : ∀ b, ¬(In (topS s) EmSize b ∨ In (dataArg s) (8 * nArg s) b
      ∨ In (opsArg s) (72 * nArg s) b ∨ rStk s b) → s'.dmem.get? b = t.dmem.get? b := fun b hb => by
    have e := call_frame (fr := frL s ra) hkeep (by rw [hlen, frL_length]) (by rw [frL_length]; decide)
      hok.n rfl rfl ((Lc.single _ _).sep (Single.mk _)) hmem0 hmem' (b := b) (by rw [frL_length]; exact hb)
    simp only [Std.ExtHashMap.get?_eq_getElem?]
    exact e
  have hout : ∀ b, ¬rD s b → s'.dmem.get? b = (s.pushRa ra).dmem.get? b := fun b hb =>
    (hcall b fun h => hb (h.imp_left in_loc)).trans (get?_R0 hs.mem fun h => hb (Or.inl h))
  have htl : (flat g').trace.length = g'.h.nops.toNat := by
    simp only [flat, List.length_map, List.length_take, Vector.length_toList]
    exact Nat.min_eq_left (by have := hok'.nops; have := hok'.n; unfold MAX_N at *; omega)
  have hn' : g'.h.n.toNat = nArg s := by rw [hkeep.n]; rfl
  have hxs' : g'.xs = 0 := hkeep.xs
  have hxo' : g'.xo = 0 := hkeep.xo
  refine ⟨{ res := ?_, sp := ?_, rbx := ?_, rbp := ?_, r12 := ?_, r13 := ?_, r14 := ?_, r15 := ?_,
            g := hs.g, ra := ?_, mapped := ?_, out := ?_, blkp := ?_, blkm := ?_, nops := ?_, off := ?_,
            exc := ?_, len := ?_, size := ?_, ops := ?_, data := ?_ }, hal⟩
  · rw [← flat_topG s ra]
  · rw [show s'.regs.rsp = c.regs.rsp from mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp, hsp]
    exact hs.sp
  · exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx).trans (e1.trans hs.rbx)
  · exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp).trans (e2.trans hs.rbp)
  · exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12).trans (e3.trans hs.r12)
  · exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13).trans (e4.trans hs.r13)
  · exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14).trans (e5.trans hs.r14)
  · exact (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15).trans (e6.trans hs.r15)
  · exact ld_eq (A := rsp s - 8#64) (N := 8) (fun b hb => hout b (ra_D hp hm hb)) (by simp)
  · intro b hb
    have hf := inside_one_nil.mp hb
    by_cases hD : rD s b
    · have hmem : b ∈ s'.dmem := by
        rcases hD with h | h | h | h
        · by_cases hE : In (topS s) EmSize b
          · exact view_mem hok'.n hxs' hxo' (by rw [hlen]; decide) hmem' (Or.inl hE)
          · have hm2 := hs.mem
            rw [← MProp.sep_assoc] at hm2
            have e := hcall b fun h' => by
              rcases h' with h' | h' | h' | h'
              · exact hE h'
              · exact nf_fr hm data_nf h' hf
              · exact nf_fr hm ops_nf h' hf
              · exact stk_S h' h
            simp only [Std.ExtHashMap.get?_eq_getElem?] at e
            rw [Std.ExtHashMap.mem_iff_isSome_getElem?, e]
            exact Std.ExtHashMap.mem_iff_isSome_getElem?.mp (mem_own hm2 (EmLc.own _ _ _) h)
        · exact absurd hf (nf_fr hm data_nf h)
        · exact absurd hf (nf_fr hm ops_nf h)
        · refine view_mem hok'.n hxs' hxo' (by rw [hlen]; decide) hmem' ?_
          rw [hlen]; exact Or.inr (Or.inr (Or.inr h))
      exact Std.ExtHashMap.mem_iff_isSome_getElem?.mp hmem
    · rw [hout b hD]; exact frame0 hp b hb
  · intro b hb
    have hf : ¬In (rsp s - BitVec.ofNat 64 topF) topF b := fun h => hb (inside_one.mpr (Or.inl h))
    rw [hout b (nfr_D hp hf (fun h => hb (inside_one.mpr (Or.inr (inside_of_mem (by simp [topOut]) h))))
      (fun h => hb (inside_one.mpr (Or.inr (inside_of_mem (by simp [topOut]) h))))), get?_m0 hp hf]
  · have e : topS s + BitVec.ofNat 64 offBlk = rsp s + 8#64 := by unfold topS; simp only [offOps, offBlk]; bv_omega
    rw [e]
    refine ld_eq (A := rsp s + 8#64) (N := 8) (fun b hb => ?_) (by simp)
    rw [hout b (blkp_D hp hm hb), get?_m0 hp (blkp_fr hp hb)]
  · intro b hb
    have hnf : ¬In (rsp s - BitVec.ofNat 64 topF) topF b := fun h => fr_blk hm (inside_one_nil.mpr h) hb
    rw [hout b (blk_D hp hm hb), get?_m0 hp hnf]
    exact hm.mapped b (inside_of_mem (by simp [topOut]) (inside_one_nil.mp hb))
  · rw [← hflat, htl]
    exact ⟨View.isSome_nops hmem', (View.rd_nops hmem').trans (by simp)⟩
  · rw [← hflat]
    exact ⟨isSome_of_eq g'.h.blkOff hmem' (by unfold View Em; ecancel),
      rd_of_eq hmem' (by unfold View Em; ecancel)⟩
  · rw [← hflat]
    exact ⟨isSome_of_eq g'.h.blkExc hmem' (by unfold View Em; ecancel),
      rd_of_eq hmem' (by unfold View Em; ecancel)⟩
  · rw [← hflat, htl, ← hn']; simpa [hxo'] using hok'.nops
  · rw [← hflat, ← hn']; have := hok'.len; rw [hxs'] at this; exact this
  · rw [← hflat, htl]
    refine List.ext_getElem (by simp only [List.length_map, List.length_range, htl]) fun i h1 h2 => ?_
    have hi : i < g'.h.nops.toNat := by simpa using h1
    have hi6 : i < 6 * g'.h.n.toNat + g'.xo := by have := hok'.nops; omega
    have hf := View.focus hmem' hi6
    have k1 : rdb s'.dmem (opsArg s + BitVec.ofNat 64 (12 * i)) = g'.ops[i].op.kind := by
      have := OpM.rdb_kind hf; rw [hkeep.ops] at this; exact this
    have k2 : rdb s'.dmem (opsArg s + BitVec.ofNat 64 (12 * i) + 1#64) = g'.ops[i].op.depth := by
      have := OpM.rdb_depth hf; rw [hkeep.ops] at this; exact this
    have k3 : StackSlot.ofWord (rd s'.dmem (opsArg s + BitVec.ofNat 64 (12 * i) + 4#64))
        = g'.ops[i].op.slot := by
      have := OpM.rd_slot hf; rw [hkeep.ops] at this; exact this
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, Vector.getElem_toList, flat,
      topOp]
    rw [k1, k2, k3]
  · rw [← hflat]
    obtain ⟨R, hR⟩ := View.arr_stk hmem'
    unfold Flat.slotsOf
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < g'.h.len.toNat := by simpa [flat] using hi
    have hin : i < g'.h.n.toNat := by have := hok'.len; omega
    have hmx : i < MAX_N := by have := hok'.n; omega
    have e := Arr.rd hR (i := i) (by simpa using Nat.lt_add_right g'.xs hin)
    have e' : rd s'.dmem (dataArg s + BitVec.ofNat 64 (8 * i))
        = g'.stk.toList[i]'(by simpa using Nat.lt_add_right g'.xs hin) := by
      rw [hkeep.data] at e; exact e
    show topData s s' i = Flat.get (flat g').data (BitVec.ofNat 64 i)
    rw [get_ofNat _ hmx]
    show StackSlot.ofWord (rd s'.dmem (dataArg s + BitVec.ofNat 64 (8 * i)))
      = (vec (g'.stk.toList.map StackSlot.ofWord))[i]
    rw [e']
    simp [vec, Nat.lt_add_right g'.xs hin]

-- The call of `buildBottomUp`: `topPre` gives `Sep.Pre`, and `topPost` gives `TQ` from `Sep.Post`.
theorem TS.call (hs : TS s ra (hdr s ra (Dm s ra) (Pm s ra) (Flat.countNone (Pm s ra) (nArg s) 0)) L t)
    (hp : TopPre s) {c : MachineData} (hd : c.dmem = t.dmem) (hdi : c.regs.rdi = t.regs.rsp)
    (hsp : c.regs.rsp = t.regs.rsp) (e1 : c.regs.rbx = t.regs.rbx) (e2 : c.regs.rbp = t.regs.rbp)
    (e3 : c.regs.r12 = t.regs.r12) (e4 : c.regs.r13 = t.regs.r13) (e5 : c.regs.r14 = t.regs.r14)
    (e6 : c.regs.r15 = t.regs.r15) {K : MachineData → Prop}
    (hk : ∀ t' st fs, TQ s ra st fs t' → al t' = code st → K t') :
    ∃ S g F, Sep.Pre S g F loopA 2068 c ∧
      ∀ s', Sep.Post S F 2068 (fun g' t' => loopQ g g' c t') c s' → Sep.mod.Agree c s' → K s' :=
  ⟨topS s, topG s ra, FL s ra L, topPre hs hp hd hdi hsp, fun s' hpost hag =>
    (topPost hs hp hsp e1 e2 e3 e4 e5 e6 hpost hag).elim fun hq hal => hk s' _ _ hq hal⟩

end

end Top

end Bbu.Unit
