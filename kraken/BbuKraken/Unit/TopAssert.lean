module

public import BbuKraken.Unit.TopInv
import all BbuKraken.Unit.TopInv
public import BbuKraken.Unit.ExitDefs
import all BbuKraken.Unit.ExitDefs
public import BbuKraken.Unit.StackCall
import all BbuKraken.Unit.StackCall

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit.Top
open Bbu.Sep

-- These registers serve only to reuse the memory correspondence of `topPost`.
-- The actual exit state keeps its own registers.
def memoryReturn (c t : MachineData) : MachineData :=
  {t with regs := {c.regs with rax := 2}}

theorem memoryReturn_agree (c t : MachineData) : Sep.mod.Agree c (memoryReturn c t) := by
  refine ⟨fun q hq => ?_, Sep.mod_mem _ _⟩
  cases q <;> first | rfl | exact False.elim (hq (by simp [Sep.mod]))

theorem topAssert {s : MachineData} {ra : Int64} {L : Loc} {t c x : MachineData}
    (hs : TS s ra (hdr s ra (Dm s ra) (Pm s ra)
      (Flat.countNone (Pm s ra) (nArg s) 0)) L t)
    (hp : TopPre s) (hsp : c.regs.rsp = t.regs.rsp)
    (e1 : c.regs.rbx = t.regs.rbx) (e2 : c.regs.rbp = t.regs.rbp)
    (e3 : c.regs.r12 = t.regs.r12) (e4 : c.regs.r13 = t.regs.r13)
    (e5 : c.regs.r14 = t.regs.r14) (e6 : c.regs.r15 = t.regs.r15)
    (hx : Sep.Post (topS s) (FL s ra L) 2068
      (fun g' t' => loopX (topG s ra) g' c t') c x) : TopFlatExit s x := by
  obtain ⟨g', fr, v, hX, hok, hlen, hmem⟩ := hx
  have hpost : Sep.Post (topS s) (FL s ra L) 2068
      (fun g' t' => loopQ (topG s ra) g' c t') c (memoryReturn c x) := by
    refine ⟨g', fr, v, ⟨hX.1, hX.2.1, ?_⟩, hok, hlen, hmem⟩
    change 2#8 = code (Flat.buildBottomUp (flat (topG s ra))).1
    rw [hX.2.2]
    rfl
  obtain ⟨hq, _⟩ := topPost hs hp hsp e1 e2 e3 e4 e5 e6 hpost (memoryReturn_agree c x)
  have hres : Flat.buildBottomUp (topCtor s (u0 s ra)) =
      (.assertionFailed, (Flat.buildBottomUp (flat (topG s ra))).2) := by
    simpa only [hX.2.2] using hq.res
  exact ⟨hs.g, hq.mapped, hq.out, u0 s ra, _, topRes_fail hs.g hres,
    hq.len, hq.ops, hq.data⟩

def EWithExit [Host] (s : MachineData) (ra : Int64) (a : Int64) (t : MachineData) : Prop :=
  E s ra a t ∨ (a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧ TopFlatExit s t)

def OblWithExit [Host] [FunDecls] (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, LInv s ra blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      LInv s ra b u ∧ Program.Decreases V blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels buildBottomUpAsm) (s.pushRa ra) I' (EWithExit s ra)) t

theorem Obl.withExit [Host] [FunDecls] {s : MachineData} {ra : Int64}
    {blk : Program.Block} (h : Obl s ra blk) : OblWithExit s ra blk := by
  intro t ht
  exact WP.wp_monotone_epost (x := blk.body)
    (fun _ _ hi => ProofKit.intercept_mono_exit hi Or.inl) t (h t ht)

private theorem blocksFromWithExit [Host] [FunDecls] {s : MachineData} {ra : Int64}
    {l : CfgLabel} : ∀ {bs : List (Label × Program)} {b : CfgLabel} {j : Nat} {body : Program},
    Program.forallBlocksFrom (fun blk => blk.label = l → Obl s ra blk) b j body bs →
    Program.forallBlocksFrom (fun blk => blk.label = l → OblWithExit s ra blk) b j body bs
  | [], _, _, _, h => fun hl => (h hl).withExit
  | _ :: _, _, _, _, h => ⟨fun hl => (h.1 hl).withExit, blocksFromWithExit h.2⟩

theorem blocksWithExit [Host] [FunDecls] {s : MachineData} {ra : Int64}
    {p : Program} {l : CfgLabel}
    (h : p.ForallBlocks fun blk => blk.label = l → Obl s ra blk) :
    p.ForallBlocks fun blk => blk.label = l → OblWithExit s ra blk :=
  blocksFromWithExit h

end Bbu.Unit.Top
