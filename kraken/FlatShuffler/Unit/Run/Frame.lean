module

public import FlatShuffler.Unit.Run.Model
import all FlatShuffler.Unit.Run.Model
public import FlatShuffler.Unit.StackCall
import all FlatShuffler.Unit.StackCall
public import FlatShuffler.Unit.Plan.ExitCall
import all FlatShuffler.Unit.Plan.ExitCall
public import FlatShuffler.Unit.IsAvailable
import all FlatShuffler.Unit.IsAvailable
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace FlatShuffler.Unit
open FlatShuffler.Sep

def runA (planned : Vector Word MAX_N) (g : G) (_s : MachineData) : Prop :=
  RunU.Safe planned (flat g) g.xo

def runModelResult (planned : Vector Word MAX_N) (g g' : G) (_s t : MachineData) : Prop :=
  ∃ l, Res (Flat.emissionRun planned l) g g' t

def runQ (planned : Vector Word MAX_N) (g g' : G) (s t : MachineData) : Prop :=
  runModelResult planned g g' s t ∧ al t ≠ ASSERTION_FAILED

def runX (planned : Vector Word MAX_N) (g g' : G) (_s _t : MachineData) : Prop :=
  ∃ l, ExitRes (Flat.emissionRun planned l) g g'

theorem runX_to_modelResult {planned : Vector Word MAX_N} {g g' : G} {s t : MachineData}
    (hX : runX planned g g' s t) :
    runModelResult planned g g' s { t with regs := { t.regs with rax := ⟨2#64⟩ } } := by
  obtain ⟨l, hkeep, hflat, hstatus⟩ := hX
  refine ⟨l, hkeep, hflat, ?_⟩
  rw [hstatus]
  rfl

abbrev runD : Nat := lowestD + 4

def RunView (PM : Addr) (planned : Vector Word MAX_N) (S : Addr) (g : G) : MProp 64 :=
  View S g ∗ Planned S PM planned

abbrev RunThm [Host] [FunDecls] (p : Program) : Prop :=
  ∀ S PM planned g F,
    Sep.BodyWithExit p (Sep.Pre S g (Planned S PM planned ∗ F) (runA planned) runD)
      (fun s t => Sep.Post S (Planned S PM planned ∗ F) runD
        (fun g' t => runQ planned g g' s t) s t)
      (fun s t => Sep.Post S (Planned S PM planned ∗ F) runD
        (fun g' t => runX planned g g' s t) s t)

namespace RunU

theorem post_imp {V : Addr → G → MProp 64} {S : Addr} {F : MProp 64}
    {d : Nat} {s t : MachineData} {Q R : G → MachineData → Prop}
    (hp : VPost V G.Ok S F d Q s t) (h : ∀ g', Q g' t → R g' t) :
    VPost V G.Ok S F d R s t := by
  obtain ⟨g', hq, hok, fr, v, hl, hm⟩ := hp
  exact ⟨g', h g' hq, hok, fr, v, hl, hm⟩

theorem pre_iff {S PM : Addr} {planned : Vector Word MAX_N} {g : G} {F : MProp 64}
    {A : G → MachineData → Prop} {d : Nat} {s : MachineData} :
    VPre (RunView PM planned) G.Ok S g F A d s ↔
      Sep.Pre S g (Planned S PM planned ∗ F) A d s := by
  constructor
  · rintro ⟨hdi, hok, hA, fr, v, hl, hm⟩
    exact ⟨hdi, hok, ⟨fr, v, hl, (by unfold RunView; ecancel :
      Stk (rsp s) fr v ∗ RunView PM planned S g ∗ F =
        View S g ∗ Stk (rsp s) fr v ∗ (Planned S PM planned ∗ F)) ▸ hm⟩, hA⟩
  · rintro ⟨hdi, hok, ⟨fr, v, hl, hm⟩, hA⟩
    exact ⟨hdi, hok, hA, fr, v, hl, (by unfold RunView; ecancel :
      View S g ∗ Stk (rsp s) fr v ∗ (Planned S PM planned ∗ F) =
        Stk (rsp s) fr v ∗ RunView PM planned S g ∗ F) ▸ hm⟩

theorem post_iff {S PM : Addr} {planned : Vector Word MAX_N} {F : MProp 64} {d : Nat}
    {Q : G → MachineData → Prop} {s t : MachineData} :
    VPost (RunView PM planned) G.Ok S F d Q s t ↔
      Sep.Post S (Planned S PM planned ∗ F) d Q s t := by
  constructor
  · rintro ⟨g, hQ, hok, fr, v, hl, hm⟩
    exact ⟨g, fr, v, hQ, hok, hl, (by unfold RunView; ecancel :
      Stk (rsp s) fr v ∗ RunView PM planned S g ∗ F =
        View S g ∗ Stk (rsp s) fr v ∗ (Planned S PM planned ∗ F)) ▸ hm⟩
  · rintro ⟨g, fr, v, hQ, hok, hl, hm⟩
    exact ⟨g, hQ, hok, fr, v, hl, (by unfold RunView; ecancel :
      View S g ∗ Stk (rsp s) fr v ∗ (Planned S PM planned ∗ F) =
        Stk (rsp s) fr v ∗ RunView PM planned S g ∗ F) ▸ hm⟩

-- A callee that uses `View` keeps `Planned` as part of its frame.
theorem frame_spec [Host] [FunDecls] {PM : Addr} {planned : Vector Word MAX_N}
    {f : Label} {A : G → MachineData → Prop} {d : Nat}
    {Q : G → G → MachineData → MachineData → Prop} (h : Sep.Spec f A d Q) :
    VSpec (RunView PM planned) G.Ok f A d Q := by
  intro asz osz K E
  refine ⟨fun s ⟨S, g, F, hp, hk⟩ => ?_⟩
  exact (h asz osz K E).1 s ⟨S, g, Planned S PM planned ∗ F, pre_iff.mp hp,
    fun t ht ha => hk t (post_iff.mpr ht) ha⟩

theorem frame_specWithExit [Host] [FunDecls] {PM : Addr} {planned : Vector Word MAX_N}
    {f : Label} {A : G → MachineData → Prop} {d : Nat}
    {Q X : G → G → MachineData → MachineData → Prop} (h : Sep.SpecWithExit f A d Q X) :
    VSpecWithExit (RunView PM planned) G.Ok f A d Q X := by
  intro asz osz K E
  refine ⟨fun s ⟨S, g, F, hp, hn, hx⟩ => ?_⟩
  exact (h asz osz K E).1 s ⟨S, g, Planned S PM planned ∗ F, pre_iff.mp hp,
    (fun t ht ha => hn t (post_iff.mpr ht) ha), fun t ht ha => hx t (post_iff.mpr ht) ha⟩

theorem lowest_vthm [Host] [FunDecls] {p : Program} (h : LowestThm p)
    (PM : Addr) (planned : Vector Word MAX_N) :
    VThmWithExit (RunView PM planned) G.Ok p (lowestA planned) lowestD
      (lowestQ planned) (lowestX planned) := by
  intro S g F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  apply Program.wp_mono (fun _ h => h) ?_
    ((h S PM planned g F s ra).1 t ⟨ht, pre_iff.mp hp⟩)
  rintro u (⟨ha, hq, hag⟩ | ⟨ha, harg, hx⟩)
  · exact Or.inl ⟨ha, post_iff.mpr hq, hag⟩
  · exact Or.inr ⟨ha, harg, post_iff.mpr hx⟩

def saved (s : MachineData) : List Word :=
  [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec]

def fr (s : MachineData) (lo : List Word) (w : Word) : List Word := lo ++ w :: saved s

theorem split_frame {xs : List Word} (hl : xs.length = runD) :
    ∃ lo w x y z, xs = lo ++ [w, x, y, z] ∧ lo.length = lowestD := by
  have hd : (xs.drop lowestD).length = 4 := by simp [hl, runD]
  match e : xs.drop lowestD, hd with
  | [w, x, y, z], _ =>
    exact ⟨xs.take lowestD, w, x, y, z, by rw [← e, List.take_append_drop],
      by simp [hl, runD]⟩

theorem fr_length {s : MachineData} {lo : List Word} {w : Word}
    (h : lo.length = lowestD) : (fr s lo w).length = runD := by
  simp [fr, saved, h, runD]

structure Bd (S PM : Addr) (planned : Vector Word MAX_N) (g : G) (F : MProp 64)
    (s : MachineData) (ra : Int64) (lo : List Word) (w : Word) (t : MachineData) : Prop where
  kb : Kb (RunView PM planned S g ∗ F) s ra (fr s lo w) 24#64 t
  len : lo.length = lowestD
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

section
variable {S PM : Addr} {planned : Vector Word MAX_N} {g : G} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo : List Word} {w : Word}

theorem Bd.next (h : Bd S PM planned g F s ra lo w t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) (h13 : u.regs.r13 = t.regs.r13)
    (h14 : u.regs.r14 = t.regs.r14) (h15 : u.regs.r15 = t.regs.r15) :
    Bd S PM planned g F s ra lo w u :=
  ⟨h.kb.next hm hsp, h.len, h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩

theorem Bd.mem (h : Bd S PM planned g F s ra lo w t) :
    (View S g ∗ (Planned S PM planned ∗ Stk (rsp s) (fr s lo w) ra.toBitVec ∗ F)).get
      t.dmem := by
  have hm := h.kb.mem
  exact (by unfold RunView; ecancel :
    Stk (rsp s) (fr s lo w) ra.toBitVec ∗ RunView PM planned S g ∗ F =
      View S g ∗ (Planned S PM planned ∗ Stk (rsp s) (fr s lo w) ra.toBitVec ∗ F)) ▸ hm

theorem Bd.rd_pos (h : Bd S PM planned g F s ra lo w t) {i : Word}
    (hok : g.Ok) (hi : i < g.h.n) :
    rd t.dmem (Fld.mapping_positionOf S i.toNat) = Flat.get (flat g).pos i := by
  have hiM : i.toNat < MAX_N := Nat.lt_of_lt_of_le hi hok.n
  rw [View.rd_pos h.mem hiM]
  simp only [flat, Flat.get, dite_eq_left hiM]

theorem Bd.kind (h : Bd S PM planned g F s ra lo w t) {i : Word}
    (hok : g.Ok) (hi : i < g.h.n) :
    rdb t.dmem (slotAt g.h.tgt i.toNat + 4#64) = (Flat.get (flat g).target i).kind := by
  rw [View.rdb_tgt_byte h.mem hi (j := 4) (by decide), AvailableU.get_target hok hi]
  rfl

theorem Bd.after {g' : G} {lo' : List Word} {w' : Word}
    (h : Bd S PM planned g F s ra lo w t)
    (hk : Kb (RunView PM planned S g' ∗ F) s ra (fr s lo' w') 24#64 u)
    (hl : lo'.length = lowestD) (hag : Sep.mod.Agree t u) :
    Bd S PM planned g' F s ra lo' w' u :=
  ⟨hk, hl,
    (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13).trans h.r13,
    (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14).trans h.r14,
    (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15).trans h.r15⟩

-- A smaller callee uses the highest free words. The lower words stay in its frame.
theorem Bd.call {k : Nat} {A : G → MachineData → Prop}
    {Q : G → G → MachineData → MachineData → Prop} {K : MachineData → Prop}
    (h : Bd S PM planned g F s ra lo w t) (hk : k ≤ lowestD)
    (hdi : rdi t = S) (hok : g.Ok) (hA : A g t)
    (hK : ∀ u g' lo' w', Bd S PM planned g' F s ra lo' w' u →
      Q g g' t u → g'.Ok → Sep.mod.Agree t u → K u) :
    ∃ S' g' F', VPre (RunView PM planned) G.Ok S' g' F' A k t ∧
      ∀ u, VPost (RunView PM planned) G.Ok S' F' k (fun g'' u => Q g' g'' t u) t u →
        Sep.mod.Agree t u → K u := by
  let xs := lo.take (lowestD - k)
  let ys := lo.drop (lowestD - k)
  have he : xs ++ ys = lo := List.take_append_drop _ _
  have hx : xs.length = lowestD - k := by simp only [xs, List.length_take, h.len]; omega
  have hy : ys.length = k := by simp only [ys, List.length_drop, h.len]; omega
  have hkb : Kb (RunView PM planned S g ∗ F) s ra
      (xs ++ ys ++ w :: saved s) 24#64 t := by rw [he]; exact h.kb
  refine Kb.vcall_above hkb (by rfl) hy hdi hok hA ?_
  intro u g' lo' w' hkb hl hq hok' hag
  have hlen : (xs ++ lo').length = lowestD := by
    rw [List.length_append, hx, hl]; omega
  exact hK u g' (xs ++ lo') w' (h.after hkb hlen hag) hq hok' hag

theorem Bd.callWithExit {k : Nat} {A : G → MachineData → Prop}
    {Q X : G → G → MachineData → MachineData → Prop} {K E : MachineData → Prop}
    (h : Bd S PM planned g F s ra lo w t) (hk : k ≤ lowestD)
    (hdi : rdi t = S) (hok : g.Ok) (hA : A g t)
    (hK : ∀ u g' lo' w', Bd S PM planned g' F s ra lo' w' u →
      Q g g' t u → g'.Ok → Sep.mod.Agree t u → K u)
    (hX : ∀ u, VPost (RunView PM planned) G.Ok S F runD
      (fun g' u => X g g' t u) s u → u.regs.get64 .rdi = 1#64 → E u) :
    ∃ S' g' F', VPre (RunView PM planned) G.Ok S' g' F' A k t ∧
      (∀ u, VPost (RunView PM planned) G.Ok S' F' k (fun g'' u => Q g' g'' t u) t u →
        Sep.mod.Agree t u → K u) ∧
      (∀ u, VPost (RunView PM planned) G.Ok S' F' k (fun g'' u => X g' g'' t u) t u →
        u.regs.get64 .rdi = 1#64 → E u) := by
  let xs := lo.take (lowestD - k)
  let ys := lo.drop (lowestD - k)
  have he : xs ++ ys = lo := List.take_append_drop _ _
  have hx : xs.length = lowestD - k := by simp only [xs, List.length_take, h.len]; omega
  have hy : ys.length = k := by simp only [ys, List.length_drop, h.len]; omega
  have hkb : Kb (RunView PM planned S g ∗ F) s ra
      (xs ++ ys ++ w :: saved s) 24#64 t := by rw [he]; exact h.kb
  refine Kb.vcallWithExit_above hkb (by rfl) hy hdi hok hA ?_ ?_
  · intro u g' lo' w' hkb hl hq hok' hag
    have hlen : (xs ++ lo').length = lowestD := by
      rw [List.length_append, hx, hl]; omega
    exact hK u g' (xs ++ lo') w' (h.after hkb hlen hag) hq hok' hag
  · intro u g' lo' w' hm hl hq hok' harg
    have hlen : (xs ++ lo').length = lowestD := by
      rw [List.length_append, hx, hl]; omega
    apply hX u ⟨g', hq, hok', fr s (xs ++ lo') w', ra.toBitVec, fr_length hlen, ?_⟩ harg
    simpa only [fr, List.append_assoc] using hm

theorem Bd.callee_mem (h : Bd S PM planned g F s ra lo w t) :
    (RunView PM planned S g ∗ Stk (rsp t) lo w ∗
      (Arr (rsp t) (saved s) ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)).get t.dmem := by
  have hm := h.kb.mem
  change (Stk (rsp s) (lo ++ w :: saved s) ra.toBitVec ∗ (RunView PM planned S g ∗ F)).get
    t.dmem at hm
  rw [Stk.callee] at hm
  have hsp : rsp s - 8#64 - BitVec.ofNat 64 (8 * (saved s).length) = rsp t := by
    simp only [saved, List.length_cons, List.length_nil]
    exact h.kb.sp.symm
  rw [hsp] at hm
  have he : Stk (rsp t) lo w ∗ (RunView PM planned S g ∗
      (Arr (rsp t) (saved s) ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)) =
      RunView PM planned S g ∗ Stk (rsp t) lo w ∗
        (Arr (rsp t) (saved s) ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F) := by ac_rfl
  exact he ▸ hm

theorem Bd.isSome_exit (h : Bd S PM planned g F s ra lo w t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec - 8#64) 8).isSome = true := by
  apply isSome_of_eq (R := RunView PM planned S g ∗
    Arr (rsp t - 8#64 - BitVec.ofNat 64 (8 * lo.length)) lo ∗
    Arr (rsp t) (saved s) ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F) w h.callee_mem
  unfold Stk
  ac_rfl

theorem Bd.exitPost (h : Bd S PM planned g F s ra lo w t) (hok : g.Ok)
    (exitra : Int64) {X : G → MachineData → Prop}
    (hm : u.dmem = t.dmem.storeInt (rsp t - 8#64) 8 exitra.toBitVec.toInt)
    (hx : X g u) : VPost (RunView PM planned) G.Ok S F runD X s u := by
  refine ⟨g, hx, hok, fr s lo exitra.toBitVec, ra.toBitVec, fr_length h.len, ?_⟩
  rw [hm, fr, Stk.callee]
  have hsp : rsp s - 8#64 - BitVec.ofNat 64 (8 * (saved s).length) = rsp t := by
    simp only [saved, List.length_cons, List.length_nil]
    exact h.kb.sp.symm
  rw [hsp]
  have hs := Generate.stk_store h.callee_mem exitra.toBitVec
  have he : RunView PM planned S g ∗ Stk (rsp t) lo exitra.toBitVec ∗
      (Arr (rsp t) (saved s) ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F) =
      Stk (rsp t) lo exitra.toBitVec ∗ (RunView PM planned S g ∗
        (Arr (rsp t) (saved s) ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)) := by ac_rfl
  exact he ▸ hs

theorem Bd.pop (h : Bd S PM planned g F s ra lo w t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64)
    (hbx : u.regs.rbx.toBitVec = rd t.dmem t.regs.rsp.toBitVec)
    (hbp : u.regs.rbp.toBitVec = rd t.dmem (t.regs.rsp.toBitVec + 8#64))
    (h12 : u.regs.r12.toBitVec = rd t.dmem (t.regs.rsp.toBitVec + 8#64 + 8#64))
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) :
    Kg (RunView PM planned S g ∗ F) s ra (fr s lo w) u := by
  have hkb : Kb (RunView PM planned S g ∗ F) s ra ((lo ++ [w]) ++ saved s) 24#64 t := by
    simpa only [fr, List.append_assoc, List.singleton_append] using h.kb
  have hd := fun i (hi : i < 3) => hkb.rd_hi (lo := lo ++ [w]) (hi := saved s) rfl
    (i := i) (by simpa [saved] using hi)
  have hd0 := hd 0 (by decide)
  have hd1 := hd 1 (by decide)
  have hd2 := hd 2 (by decide)
  simp only [saved, List.getElem_cons_zero, List.getElem_cons_succ, Nat.reduceMul,
    BitVec.add_zero] at hd0 hd1 hd2
  refine h.kb.kg hm (by rw [hsp, h.kb.sp]; bv_omega)
    (UInt64.toBitVec_inj.mp (hbx.trans hd0))
    (UInt64.toBitVec_inj.mp (hbp.trans hd1))
    (UInt64.toBitVec_inj.mp (h12.trans ?_))
    (h13.trans h.r13) (h14.trans h.r14) (h15.trans h.r15)
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hd2

end
end RunU
end FlatShuffler.Unit
