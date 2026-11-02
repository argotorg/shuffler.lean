module

public import FlatShuffler.Unit.Plan.ResolveTie
import all FlatShuffler.Unit.Plan.ResolveTie

@[expose] public section

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
  {w : Work} {lo lo' : List Word} {L : Lc} {i best : Word} {cls : BitVec 8}

theorem PickAt.next (h : PickAt P r F s ra w lo L i best cls t)
    (hmem : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (h12 : u.regs.r12 = t.regs.r12) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (hbx : u.regs.rbx = t.regs.rbx)
    (h15 : u.regs.r15 = t.regs.r15) :
    PickAt P r F s ra w lo L i best cls u :=
  ⟨h.toCore.next hmem hsp h12 h14 h13, h.index,
    by rw [hbx, hsp]; exact h.rbx, h15 ▸ h.r15, h.bestClass, h.bestValid⟩

theorem pending_take (h : PickAt P r F s ra w lo L i best cls t)
    {c : BitVec 8} (hm : w.Model r s)
    (hv : BestValid r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i) c)
    (he : PickEq r w (i + 1) (Flat.get w.candidates i) c)
    (hp : L.pending = Flat.get w.candidates i)
    (hmem : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (h12 : u.regs.r12 = t.regs.r12) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (hbx : u.regs.rbx = t.regs.rbx)
    (ha : al u = c) : Pending P r F s ra u := by
  exact ⟨w, lo, L, i, Flat.get w.candidates i, c,
    h.toCore.next hmem hsp h12 h14 h13, h.index,
    by rw [hbx, hsp]; exact h.rbx, hp, ha, hv, hm, he⟩

theorem pending_keep (h : PickAt P r F s ra w lo L i best cls t)
    (hm : w.Model r s) (he : PickEq r w (i + 1) best cls)
    (hmem : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8 t.regs.r15.toBitVec.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (h12 : u.regs.r12 = t.regs.r12) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (hbx : u.regs.rbx = t.regs.rbx)
    (ha : al u = cls) : Pending P r F s ra u := by
  rw [h.r15] at hmem
  have hb := h.bd.storeLocal (i := 1) (by simp) best hmem hsp
  rw [Lc.set_pending] at hb
  exact ⟨w, lo, { L with pending := best }, i, best, cls,
    h.toCore.withPending hb hsp h12 h14 h13, h.index,
    by rw [hbx, hsp]; exact h.rbx, rfl, ha, h.bestValid, hm, he⟩

theorem rd_pass_store_pending (m : Mem 64) (sp : Addr) (x : Word) :
    rd (m.storeInt (sp + 8#64) 8 x.toInt) (sp + 32#64) = rd m (sp + 32#64) := by
  rw [rd_store_other _ (by bv_omega)]

theorem rdb_class_store_pending (m : Mem 64) (sp : Addr) (x : Word) :
    rdb (m.storeInt (sp + 8#64) 8 x.toInt) (sp + 23#64) =
      rdb m (sp + 23#64) := by
  rw [rdb, rdb, Mem.loadInt_congr (m' := m)]
  intro i hi
  apply Mem.get?_storeInt_of_ne
  intro j hj
  bv_omega

theorem class_some_store_pending (m : Mem 64) (sp : Addr) (x : Word) :
    ((m.storeInt (sp + 8#64) 8 x.toInt).loadInt (sp + 23#64) 1).isSome =
      (m.loadInt (sp + 23#64) 1).isSome := by
  congr 1
  apply Mem.loadInt_congr
  intro i hi
  apply Mem.get?_storeInt_of_ne
  intro j hj
  bv_omega

theorem PickAt.withPending (h : PickAt P r F s ra w lo L i best cls t)
    {off : Word}
    (hb : Bd P (w.ghost r) F s ra lo { L with pending := off }.toList u)
    (hsp : u.regs.rsp = t.regs.rsp) (h12 : u.regs.r12 = t.regs.r12)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13)
    (hbx : u.regs.rbx = t.regs.rbx) (h15 : u.regs.r15 = t.regs.r15) :
    PickAt P r F s ra w lo { L with pending := off } i best cls u :=
  ⟨h.toCore.withPending hb hsp h12 h14 h13, h.index,
    by rw [hbx, hsp]; exact h.rbx, h15 ▸ h.r15, h.bestClass, h.bestValid⟩

theorem Bd.candidateRead (h : Bd P r F s ra lo L.toList t) {j : Word}
    (hj : j.toNat < MAX_N) :
    rd t.dmem (t.regs.rsp.toBitVec + 48#64 + 8#64 * j) = Flat.get L.candidates j := by
  have hjN : j.toNat < 1024 := hj
  have hi : 6 + j.toNat < 1159 := by omega
  obtain ⟨R, hm⟩ := h.typedWord (6 + j.toNat) hi
  have hr := Wd.rd hm
  have ha : t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (6 + j.toNat)) =
      t.regs.rsp.toBitVec + 48#64 + 8#64 * j := by
    simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_toNat]
    bv_omega
  rw [ha] at hr
  have hv : L.toList[6 + j.toNat]? = some (Flat.get L.candidates j) := by
    rw [Nat.add_comm 6]
    simp [Lc.toList, List.getElem?_append, hj, Flat.get]
  have hv' : L.toList.get ⟨6 + j.toNat, by simpa using hi⟩ =
      Flat.get L.candidates j := by
    rw [List.getElem?_eq_getElem (by simpa using hi)] at hv
    exact Option.some.inj hv
  exact hr.trans hv'

theorem PickAt.pendingBd (h : PickAt P r F s ra w lo L i best cls t) :
    Bd P (w.ghost r) F s ra lo
      { L with pending := Flat.get w.candidates i }.toList
      { t with dmem := (t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8
        (Flat.get w.candidates i).toInt) } := by
  have hb := h.bd.storeLocal
    (u := { t with dmem := (t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8
      (Flat.get w.candidates i).toInt) })
    (i := 1) (by simp) (Flat.get w.candidates i) rfl rfl
  rwa [Lc.set_pending] at hb

theorem PickAt.afterCall (h : PickAt P r F s ra w lo L i best cls t)
    (hb : Bd P (w.ghost r) F s ra lo' L.toList u) (hag : Sep.mod.Agree t u) :
    PickAt P r F s ra w lo' L i best cls u := by
  have hsp := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp
  have h12 := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12
  have h14 := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14
  have h13 := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13
  have hbx := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx
  have h15 := mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15
  refine ⟨⟨hb, h.candidates, h.droppedNow, h.count, h.pass, h.excess, h.ok,
    h12 ▸ h.r12, h14 ▸ h.r14, ?_⟩, h.index, ?_, h15 ▸ h.r15,
    h.bestClass, h.bestValid⟩
  · rw [h13, hsp]; exact h.r13
  · rw [hbx, hsp]; exact h.rbx

theorem dropped_eq {dv : Vector (BitVec 8) MAX_N}
    (hb : Bd P (w.ghost r) F s ra lo L.toList t)
    (hd : L.droppedNow = w.droppedNow)
    (hv : ∀ o : Word, o.toNat < MAX_N →
      Flat.get dv o = rdb t.dmem (t.regs.rsp.toBitVec + 8240#64 + o)) :
    dv = w.droppedNow := by
  apply Vector.ext
  intro j hj
  have ho : (BitVec.ofNat 64 j).toNat = j := by
    change j < 1024 at hj
    simp only [BitVec.toNat_ofNat]
    omega
  have hj' : (BitVec.ofNat 64 j).toNat < MAX_N := by rw [ho]; exact hj
  have he := (hv (BitVec.ofNat 64 j) hj').trans
    (hb.droppedRead (o := BitVec.ofNat 64 j) hj').symm
  rw [hd] at he
  simpa only [Flat.get, ho, dite_eq_left hj] using he

theorem pick_select (h : PickAt P r F s ra w lo L i best cls t)
    (heq : PickEq r w i best cls)
    (hd : Flat.get w.droppedNow (Flat.get w.candidates i) = 0#8)
    (hn : Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i) ≠ Flat.NOCLASS)
    (hb : better r.M (Flat.get w.candidates i) best
      (Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i)) cls = true) :
    BestValid r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i)
      (Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i)) ∧
      PickEq r w (i + 1) (Flat.get w.candidates i)
        (Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i)) :=
  ⟨Or.inr ⟨h.ok.bounded i h.index, h.ok.live i h.index, rfl, hn⟩,
    heq.trans (pick_take h.index hd hn hb)⟩

end

section
variable [Host] [FunDecls]
  {P : Addr} {r : RG} {F : MProp 64} {s t c : MachineData} {ra : Int64}
  {w : Work} {lo : List Word} {L : Lc} {i best : Word} {cls : BitVec 8}
  {K : MachineData → Prop}

omit [Host] [FunDecls] in
theorem PickAt.callClassify (h : PickAt P r F s ra w lo L i best cls t)
    (hok : r.Ok)
    (hmem : c.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8#64) 8
      (Flat.get w.candidates i).toInt)
    (hsp : c.regs.rsp = t.regs.rsp) (h12 : c.regs.r12 = t.regs.r12)
    (h14 : c.regs.r14 = t.regs.r14) (h13 : c.regs.r13 = t.regs.r13)
    (hbx : c.regs.rbx = t.regs.rbx) (h15 : c.regs.r15 = t.regs.r15)
    (hbp : c.regs.rbp.toBitVec = Flat.get w.candidates i)
    (hdi : rdi c = P) (hsi : rsi c = r.mp)
    (hdx : rdx c = c.regs.rsp.toBitVec + 8240#64)
    (hcx : rcx c = Flat.get w.candidates i)
    (hK : ∀ u lo',
      PickAt P r F s ra w lo' { L with pending := Flat.get w.candidates i } i best cls u →
      al u = Flat.classify r.p.fl w.spills r.M w.droppedNow (Flat.get w.candidates i) →
      u.regs.rbp.toBitVec = Flat.get w.candidates i → K u) :
    ∃ S a CF, VPre CView CG.Ok S a CF classifyA 16 c ∧
      ∀ u, VPost CView CG.Ok S CF 16 (fun a' u => classifyQ a a' c u) c u →
        Sep.mod.Agree c u → K u := by
  have hb := h.bd.storeLocal (i := 1) (by simp) (Flat.get w.candidates i) hmem hsp
  rw [Lc.set_pending] at hb
  have hc := h.withPending hb hsp h12 h14 h13 hbx h15
  refine hb.callClassify (update_ok hok _ _) hdi hsi hdx
    (hcx ▸ BitVec.lt_def.mp (h.ok.bounded i h.index))
    (hcx ▸ h.ok.live i h.index) ?_
  intro dv u lo' hdv hbu hal hag
  have he := dropped_eq hb hc.droppedNow hdv
  rw [he, hcx] at hal
  apply hK u lo' (hc.afterCall hbu hag) hal
  rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]
  exact hbp

end
end FlatShuffler.Unit.ResolveU
