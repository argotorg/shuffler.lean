import BbuKraken.Sep.View
import ProofKit.SepLoad

/-!
# Load and store lemmas of the struct

One lemma for each field: the load (`rd`, `isSome`) and the store, on a hypothesis
`(View S g ∗ F).get m`. The addresses are the names of `Fields.lean`, `slotAt` and `opAt`. Each
proof moves one atom to the front with `ecancel`.

A record of the trace buffer is one `OpM` atom: `View.focus` takes it out of the view, the `OpM`
lemmas load and store its bytes, and `View.unfocus` puts it back.
-/

namespace Bbu.Sep

variable {S : Addr} {g : G} {F : MProp 64} {m : Mem 64}
-- Change the atom `A` to `A'` with the same rest `R`.
theorem swap_of_eq {P P' A A' R : MProp 64} {m' : Mem 64} (h : (P ∗ F).get m)
    (e : P ∗ F = A ∗ R) (e' : P' ∗ F = A' ∗ R) (hA : (A ∗ R).get m → (A' ∗ R).get m') :
    (P' ∗ F).get m' := e' ▸ hA (e ▸ h)

theorem rd_of_eq {P R : MProp 64} {a : Addr} {v : Word} (h : (P ∗ F).get m)
    (e : P ∗ F = Wd a v ∗ R) : rd m a = v := Wd.rd (e ▸ h)

theorem isSome_of_eq {P R : MProp 64} {a : Addr} (v : Word) (h : (P ∗ F).get m)
    (e : P ∗ F = Wd a v ∗ R) : (m.loadInt a 8).isSome = true := Wd.isSome (e ▸ h)

/-! ## Words of the struct -/

theorem View.rd_data (h : (View S g ∗ F).get m) : rd m (Fld.stack_data S) = g.h.data :=
  rd_of_eq h (by unfold View Em; ecancel)
theorem View.rd_len (h : (View S g ∗ F).get m) : rd m (Fld.stack_size S) = g.h.len :=
  rd_of_eq h (by unfold View Em; ecancel)
theorem View.rd_ops (h : (View S g ∗ F).get m) : rd m (Fld.stack_trace S) = g.h.ops :=
  rd_of_eq h (by unfold View Em; ecancel)
theorem View.rd_nops (h : (View S g ∗ F).get m) : rd m (Fld.stack_traceSize S) = g.h.nops :=
  rd_of_eq h (by unfold View Em; ecancel)

theorem View.isSome_data (h : (View S g ∗ F).get m) : (m.loadInt (Fld.stack_data S) 8).isSome = true :=
  isSome_of_eq g.h.data h (by unfold View Em; ecancel)
theorem View.isSome_len (h : (View S g ∗ F).get m) : (m.loadInt (Fld.stack_size S) 8).isSome = true :=
  isSome_of_eq g.h.len h (by unfold View Em; ecancel)
theorem View.isSome_ops (h : (View S g ∗ F).get m) : (m.loadInt (Fld.stack_trace S) 8).isSome = true :=
  isSome_of_eq g.h.ops h (by unfold View Em; ecancel)
theorem View.isSome_nops (h : (View S g ∗ F).get m) :
    (m.loadInt (Fld.stack_traceSize S) 8).isSome = true :=
  isSome_of_eq g.h.nops h (by unfold View Em; ecancel)

theorem View.store_len (h : (View S g ∗ F).get m) (w : Word) :
    (View S { g with h := { g.h with len := w } } ∗ F).get (m.storeInt (Fld.stack_size S) 8 w.toInt) :=
  swap_of_eq h (A := Wd (Fld.stack_size S) g.h.len) (by unfold View Em; ecancel)
    (by unfold View Em; ecancel) (Wd.store · w)

theorem View.store_nops (h : (View S g ∗ F).get m) (w : Word) :
    (View S { g with h := { g.h with nops := w } } ∗ F).get
      (m.storeInt (Fld.stack_traceSize S) 8 w.toInt) :=
  swap_of_eq h (A := Wd (Fld.stack_traceSize S) g.h.nops) (by unfold View Em; ecancel)
    (by unfold View Em; ecancel) (Wd.store · w)

/-! ## Arrays -/

theorem View.arr_stk (h : (View S g ∗ F).get m) : ∃ R, (Arr g.h.data g.stk.toList ∗ R).get m := by
  obtain ⟨R, e⟩ : ∃ R, View S g ∗ F = Arr g.h.data g.stk.toList ∗ R := ⟨_, by unfold View; ecancel⟩
  exact ⟨R, e ▸ h⟩

theorem View.arr_dest (h : (View S g ∗ F).get m) :
    ∃ R, (Arr (S + 56#64) g.h.dest.toList ∗ R).get m := by
  obtain ⟨R, e⟩ : ∃ R, View S g ∗ F = Arr (S + 56#64) g.h.dest.toList ∗ R :=
    ⟨_, by unfold View Em; ecancel⟩
  exact ⟨R, e ▸ h⟩

theorem View.arr_pos (h : (View S g ∗ F).get m) :
    ∃ R, (Arr (S + 8248#64) g.h.pos.toList ∗ R).get m := by
  obtain ⟨R, e⟩ : ∃ R, View S g ∗ F = Arr (S + 8248#64) g.h.pos.toList ∗ R :=
    ⟨_, by unfold View Em; ecancel⟩
  exact ⟨R, e ▸ h⟩

theorem View.rd_pos (h : (View S g ∗ F).get m) {e : Nat} (he : e < MAX_N) :
    rd m (Fld.mapping_positionOf S e) = g.h.pos[e] := by
  obtain ⟨R, h'⟩ := View.arr_pos h
  exact (Arr.rd h' (by simpa using he)).trans (by simp)

theorem View.isSome_pos (h : (View S g ∗ F).get m) {e : Nat} (he : e < MAX_N) :
    (m.loadInt (Fld.mapping_positionOf S e) 8).isSome = true := by
  obtain ⟨R, h'⟩ := View.arr_pos h
  exact Arr.isSome h' (by simpa using he)

theorem View.arr_tgt (h : (View S g ∗ F).get m) : ∃ R, (Arr g.h.tgt g.tgt.toList ∗ R).get m := by
  obtain ⟨R, e⟩ : ∃ R, View S g ∗ F = Arr g.h.tgt g.tgt.toList ∗ R := ⟨_, by unfold View; ecancel⟩
  exact ⟨R, e ▸ h⟩

theorem View.isSome_tgt (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat) :
    (m.loadInt (slotAt g.h.tgt i) 8).isSome = true :=
  let ⟨_, h⟩ := View.arr_tgt h; Arr.isSome h (by simpa using hi)

theorem View.rd_tgt (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat) :
    rd m (slotAt g.h.tgt i) = g.tgt[i] :=
  let ⟨_, h⟩ := View.arr_tgt h; (Arr.rd h (by simpa using hi)).trans (by simp)

-- Byte `j` of target word `k`.
theorem View.b8_tgt (h : (View S g ∗ F).get m) {k : Nat} (hk : k < g.h.n.toNat) {j : Nat}
    (hj : j < 8) :
    ∃ R, (B8 (slotAt g.h.tgt k + BitVec.ofNat 64 j) (g.tgt[k].extractLsb' (8 * j) 8) ∗ R).get m := by
  obtain ⟨R, h⟩ := View.arr_tgt h
  obtain ⟨Q, e⟩ := Arr.focus g.h.tgt g.tgt.toList (i := k) (by simpa using hk)
  obtain ⟨P, e'⟩ := Wd.focus_byte (slotAt g.h.tgt k) g.tgt[k] hj
  rw [e, Vector.getElem_toList] at h
  change ((Wd (slotAt g.h.tgt k) g.tgt[k] ∗ Q) ∗ R).get m at h
  rw [e', MProp.sep_assoc, MProp.sep_assoc] at h
  exact ⟨_, h⟩

theorem View.rdb_tgt_byte (h : (View S g ∗ F).get m) {k : Nat} (hk : k < g.h.n.toNat) {j : Nat}
    (hj : j < 8) : rdb m (slotAt g.h.tgt k + BitVec.ofNat 64 j) = g.tgt[k].extractLsb' (8 * j) 8 :=
  let ⟨_, h⟩ := View.b8_tgt h hk hj; B8.rdb h

-- The spilled byte of an id whose byte is not in the target: a `Spl` atom.
theorem View.b8_splOut (h : (View S g ∗ F).get m) {i : Nat}
    (hi : i ∈ splOut g.h.tgt g.h.spl g.h.n.toNat (splIds g.tgt.toList)) :
    ∃ R, (B8 (g.h.spl + BitVec.ofNat 64 i) (g.spl (BitVec.ofNat 32 i)) ∗ R).get m := by
  obtain ⟨Q, eq⟩ := Spl.focus g.h.spl g.spl hi
  obtain ⟨R, e⟩ : ∃ R, View S g ∗ F
      = B8 (g.h.spl + BitVec.ofNat 64 i) (g.spl (BitVec.ofNat 32 i)) ∗ R :=
    ⟨_, by unfold View; rw [eq]; ecancel⟩
  exact ⟨R, e ▸ h⟩

-- The spilled byte of an id of the target: a `Spl` atom, or a byte of a target word with the value
-- of `G.Ok.spl`.
theorem View.b8_spl (h : (View S g ∗ F).get m) (hok : g.Ok) {i : Nat}
    (hi : i ∈ splIds g.tgt.toList) :
    ∃ R, (B8 (g.h.spl + BitVec.ofNat 64 i) (g.spl (BitVec.ofNat 32 i)) ∗ R).get m := by
  by_cases ho : 8 * g.h.n.toNat ≤ (g.h.spl + BitVec.ofNat 64 i - g.h.tgt).toNat
  · exact View.b8_splOut h (List.mem_filter.mpr ⟨hi, decide_eq_true ho⟩)
  · generalize hd : (g.h.spl + BitVec.ofNat 64 i - g.h.tgt).toNat = d at ho
    have hk : d / 8 < g.h.n.toNat := by omega
    have hj : d % 8 < 8 := Nat.mod_lt _ (by decide)
    have ha : g.h.spl + BitVec.ofNat 64 i = slotAt g.h.tgt (d / 8) + BitVec.ofNat 64 (d % 8) := by
      unfold slotAt; subst hd; bv_omega
    rw [ha, hok.spl i hi _ hk _ hj ha]
    exact View.b8_tgt h hk hj

theorem View.isSome_spl (h : (View S g ∗ F).get m) (hok : g.Ok) {i : Nat}
    (hi : i ∈ splIds g.tgt.toList) : (m.loadInt (g.h.spl + BitVec.ofNat 64 i) 1).isSome = true :=
  let ⟨_, h⟩ := View.b8_spl h hok hi; B8.isSome h

theorem View.rdb_spl (h : (View S g ∗ F).get m) (hok : g.Ok) {i : Nat}
    (hi : i ∈ splIds g.tgt.toList) : rdb m (g.h.spl + BitVec.ofNat 64 i) = g.spl (BitVec.ofNat 32 i) :=
  let ⟨_, h⟩ := View.b8_spl h hok hi; B8.rdb h

theorem View.store_stk (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat) (w : Word) :
    (View S { g with stk := g.stk.set i w } ∗ F).get (m.storeInt (slotAt g.h.data i) 8 w.toInt) :=
  swap_of_eq h (A := Arr g.h.data g.stk.toList) (A' := Arr g.h.data (g.stk.set i w).toList)
    (by unfold View; ecancel) (by unfold View; ecancel)
    fun h => by rw [Vector.toList_set]; exact Arr.store h (by simpa using hi) w

theorem View.store_dest (h : (View S g ∗ F).get m) {i : Nat} (hi : i < MAX_N) (w : Word) :
    (View S { g with h := { g.h with dest := g.h.dest.set i w } } ∗ F).get
      (m.storeInt (Fld.mapping_destinationOf S i) 8 w.toInt) :=
  swap_of_eq h (A := Arr (S + 56#64) g.h.dest.toList) (A' := Arr (S + 56#64) (g.h.dest.set i w).toList)
    (by unfold View Em; ecancel) (by unfold View Em; ecancel)
    fun h => by rw [Vector.toList_set]; exact Arr.store h (by simpa using hi) w

theorem View.store_pos (h : (View S g ∗ F).get m) {i : Nat} (hi : i < MAX_N) (w : Word) :
    (View S { g with h := { g.h with pos := g.h.pos.set i w } } ∗ F).get
      (m.storeInt (Fld.mapping_positionOf S i) 8 w.toInt) :=
  swap_of_eq h (A := Arr (S + 8248#64) g.h.pos.toList) (A' := Arr (S + 8248#64) (g.h.pos.set i w).toList)
    (by unfold View Em; ecancel) (by unfold View Em; ecancel)
    fun h => by rw [Vector.toList_set]; exact Arr.store h (by simpa using hi) w

/-! ## Op records -/

-- The view without record `i`.
def View.rest (S : Addr) (g : G) (i : Nat) : MProp 64 :=
  Em S g.h ∗ Arr g.h.data g.stk.toList ∗ Ops g.h.ops 0 (g.ops.toList.take i)
    ∗ Ops g.h.ops (i + 1) (g.ops.toList.drop (i + 1))
    ∗ Arr g.h.tgt g.tgt.toList
    ∗ Spl g.h.spl g.spl (splOut g.h.tgt g.h.spl g.h.n.toNat (splIds g.tgt.toList))

theorem View.focus (h : (View S g ∗ F).get m) {i : Nat} (hi : i < 6 * g.h.n.toNat) :
    (OpM (opAt g.h.ops i) g.ops[i] ∗ (View.rest S g i ∗ F)).get m := by
  have e : View S g ∗ F = OpM (opAt g.h.ops i) g.ops[i] ∗ (View.rest S g i ∗ F) := by
    unfold View View.rest
    rw [Ops.focus_self _ _ (by simpa using hi), Vector.getElem_toList]
    -- The two `g.ops[i]` carry different bound proofs: make them one term.
    generalize g.ops[i] = r
    ecancel
  exact e ▸ h

theorem View.unfocus {i : Nat} {r : OpR} (h : (OpM (opAt g.h.ops i) r ∗ (View.rest S g i ∗ F)).get m)
    (hi : i < 6 * g.h.n.toNat) : (View S { g with ops := g.ops.set i r } ∗ F).get m := by
  have e : View S { g with ops := g.ops.set i r } ∗ F
      = OpM (opAt g.h.ops i) r ∗ (View.rest S g i ∗ F) := by
    unfold View View.rest
    dsimp only
    rw [Vector.toList_set, Ops.focus _ _ (by simpa using hi)]
    ecancel
  exact e ▸ h

section
variable {a : Addr} {r : OpR}

theorem OpM.isSome_kind (h : (OpM a r ∗ F).get m) : (m.loadInt a 1).isSome = true := by
  obtain ⟨R, e⟩ : ∃ R, OpM a r ∗ F = B8 a r.op.kind ∗ R := ⟨_, by unfold OpM; ecancel⟩
  exact B8.isSome (e ▸ h)

theorem OpM.store_kind (h : (OpM a r ∗ F).get m) (x : Int) :
    (OpM a { r with op := { r.op with kind := BitVec.ofInt 8 x } } ∗ F).get (m.storeInt a 1 x) :=
  swap_of_eq h (A := B8 a r.op.kind) (by unfold OpM; ecancel) (by unfold OpM; ecancel) (B8.store · x)

theorem OpM.store_depth (h : (OpM a r ∗ F).get m) (x : Int) :
    (OpM a { r with op := { r.op with depth := BitVec.ofInt 8 x } } ∗ F).get
      (m.storeInt (a + 1#64) 1 x) :=
  swap_of_eq h (A := B8 (a + 1#64) r.op.depth) (by unfold OpM; ecancel) (by unfold OpM; ecancel)
    (B8.store · x)

theorem OpM.store_payload (h : (OpM a r ∗ F).get m) (x : Int) :
    (OpM a { r with op := { r.op with slot := { r.op.slot with payload := BitVec.ofInt 32 x } } } ∗ F).get
      (m.storeInt (a + 4#64) 4 x) :=
  swap_of_eq h (A := B32 (a + 4#64) r.op.slot.payload) (by unfold OpM; ecancel)
    (by unfold OpM; ecancel) (B32.store · x)

theorem OpM.store_skind (h : (OpM a r ∗ F).get m) (x : Int) :
    (OpM a { r with op := { r.op with slot := { r.op.slot with kind := BitVec.ofInt 8 x } } } ∗ F).get
      (m.storeInt (a + 8#64) 1 x) :=
  swap_of_eq h (A := B8 (a + 8#64) r.op.slot.kind) (by unfold OpM; ecancel) (by unfold OpM; ecancel)
    (B8.store · x)

theorem OpM.store_sop (h : (OpM a r ∗ F).get m) (x : Int) :
    (OpM a { r with op := { r.op with slot := { r.op.slot with valueOpcode := BitVec.ofInt 8 x } } } ∗ F).get
      (m.storeInt (a + 9#64) 1 x) :=
  swap_of_eq h (A := B8 (a + 9#64) r.op.slot.valueOpcode) (by unfold OpM; ecancel)
    (by unfold OpM; ecancel) (B8.store · x)

end

/-! ## Address folds: from the asm forms (after `symexec_norm`) to the names above
The asm literals are `BitVec.ofNat` terms (`8#64`), not `OfNat` terms: the folds use `#64`. The folds
of the struct fields are in `Fields.lean` (`Fld.fold_*`). -/

theorem fold_slot (d x : Word) : d + x * 8#64 = slotAt d x.toNat := by
  unfold slotAt; bv_omega
theorem fold_op (o n : Word) : o + (n + n * 2#64).shiftLeft 2 = opAt o n.toNat := by
  have : (n + n * 2#64).shiftLeft 2 = n * 12 := by bv_decide
  rw [this]; unfold opAt; bv_omega

theorem View.isSome_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat) :
    (m.loadInt (slotAt g.h.data i) 8).isSome = true :=
  let ⟨_, h⟩ := View.arr_stk h; Arr.isSome h (by simpa using hi)

theorem View.rd_slot (h : (View S g ∗ F).get m) {i : Nat} (hi : i < g.h.n.toNat) :
    rd m (slotAt g.h.data i) = g.stk[i] :=
  let ⟨_, h⟩ := View.arr_stk h; (Arr.rd h (by simpa using hi)).trans (by simp)

-- Byte `j` of stack word `k`.
theorem View.b8_slot (h : (View S g ∗ F).get m) {k : Nat} (hk : k < g.h.n.toNat) {j : Nat}
    (hj : j < 8) :
    ∃ R, (B8 (slotAt g.h.data k + BitVec.ofNat 64 j) (g.stk[k].extractLsb' (8 * j) 8) ∗ R).get m := by
  obtain ⟨R, h⟩ := View.arr_stk h
  obtain ⟨Q, e⟩ := Arr.focus g.h.data g.stk.toList (i := k) (by simpa using hk)
  obtain ⟨P, e'⟩ := Wd.focus_byte (slotAt g.h.data k) g.stk[k] hj
  rw [e, Vector.getElem_toList] at h
  change ((Wd (slotAt g.h.data k) g.stk[k] ∗ Q) ∗ R).get m at h
  rw [e', MProp.sep_assoc, MProp.sep_assoc] at h
  exact ⟨_, h⟩

theorem View.isSome_slot_byte (h : (View S g ∗ F).get m) {k : Nat} (hk : k < g.h.n.toNat) {j : Nat}
    (hj : j < 8) : (m.loadInt (slotAt g.h.data k + BitVec.ofNat 64 j) 1).isSome = true :=
  let ⟨_, h⟩ := View.b8_slot h hk hj; B8.isSome h

theorem View.rdb_slot (h : (View S g ∗ F).get m) {k : Nat} (hk : k < g.h.n.toNat) {j : Nat}
    (hj : j < 8) : rdb m (slotAt g.h.data k + BitVec.ofNat 64 j) = g.stk[k].extractLsb' (8 * j) 8 :=
  let ⟨_, h⟩ := View.b8_slot h hk hj; B8.rdb h

theorem View.isSome_dest (h : (View S g ∗ F).get m) {i : Nat} (hi : i < MAX_N) :
    (m.loadInt (Fld.mapping_destinationOf S i) 8).isSome = true :=
  let ⟨_, h⟩ := View.arr_dest h; Arr.isSome h (by simpa using hi)

section
variable {a : Addr} {r : OpR}

theorem OpM.isSome_depth (h : (OpM a r ∗ F).get m) : (m.loadInt (a + 1#64) 1).isSome = true := by
  obtain ⟨R, e⟩ : ∃ R, OpM a r ∗ F = B8 (a + 1#64) r.op.depth ∗ R := ⟨_, by unfold OpM; ecancel⟩
  exact B8.isSome (e ▸ h)
theorem OpM.isSome_skind (h : (OpM a r ∗ F).get m) : (m.loadInt (a + 8#64) 1).isSome = true := by
  obtain ⟨R, e⟩ : ∃ R, OpM a r ∗ F = B8 (a + 8#64) r.op.slot.kind ∗ R := ⟨_, by unfold OpM; ecancel⟩
  exact B8.isSome (e ▸ h)
theorem OpM.isSome_sop (h : (OpM a r ∗ F).get m) : (m.loadInt (a + 9#64) 1).isSome = true := by
  obtain ⟨R, e⟩ : ∃ R, OpM a r ∗ F = B8 (a + 9#64) r.op.slot.valueOpcode ∗ R := ⟨_, by unfold OpM; ecancel⟩
  exact B8.isSome (e ▸ h)
theorem OpM.isSome_payload (h : (OpM a r ∗ F).get m) : (m.loadInt (a + 4#64) 4).isSome = true := by
  obtain ⟨R, e⟩ : ∃ R, OpM a r ∗ F = B32 (a + 4#64) r.op.slot.payload ∗ R := ⟨_, by unfold OpM; ecancel⟩
  exact B32.isSome (e ▸ h)

end

/-- `view_load` closes a load VC from a `View` or `OpM` hypothesis. -/
macro "view_load" : tactic => `(tactic| sep_load [View.isSome_data, View.isSome_len,
  View.isSome_ops, View.isSome_nops, View.isSome_slot, View.isSome_pos, View.isSome_dest,
  OpM.isSome_kind, OpM.isSome_depth, OpM.isSome_payload, OpM.isSome_skind, OpM.isSome_sop])

end Bbu.Sep
