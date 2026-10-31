import BbuKraken.Unit.Run.Frame

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit.RunU
open Bbu.Sep ProofKit

structure Phase (S PM : Addr) (planned : Vector Word MAX_N) (g a : G) (F : MProp 64)
    (s : MachineData) (ra : Int64) (l : Flat.Locals) (lo : List Word) (w : Word)
    (t : MachineData) : Prop where
  bd : Bd S PM planned a F s ra lo w t
  bx : t.regs.rbx.toBitVec = S
  ok : a.Ok
  keep : Keep g a
  model : afterLowest planned l (flat g) (flat a)

section
variable {S PM : Addr} {planned : Vector Word MAX_N} {g a : G} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {l : Flat.Locals} {lo : List Word} {w : Word}

theorem Phase.next (h : Phase S PM planned g a F s ra l lo w t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) (hbx : u.regs.rbx = t.regs.rbx)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) : Phase S PM planned g a F s ra l lo w u :=
  ⟨h.bd.next hm hsp h13 h14 h15, by rw [hbx]; exact h.bx, h.ok, h.keep, h.model⟩

theorem Phase.result (h : Phase S PM planned g a F s ra l lo w t)
    (hf : finish (flat a) = (.assertionFailed, flat a))
    (hal : al u = ASSERTION_FAILED) : runQ planned g a s u := by
  refine ⟨l, h.keep, ?_, ?_⟩
  · rw [emission_finish h.model, hf]
  · rw [emission_finish h.model, hf]; exact hal

theorem Phase.loopA (h : Phase S PM planned g a F s ra l lo w t)
    (hs : Safe planned (flat g) g.xo) (hc : checks (flat a)) : loopA a u := by
  have ha := hs.loop l h.model.1
  rw [h.model.2] at ha
  have hi := ha rfl hc
  change Flat.HInv (flat a) 0 a.xo
  rw [h.keep.xo]
  exact hi

end

def Inv (S PM : Addr) (planned : Vector Word MAX_N) (g : G) (F : MProp 64)
    (s : MachineData) (ra : Int64) : CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .label q, t =>
    if q = Names.run then t = s.pushRa ra
    else if q = ".LB.Emission.run.0" then
      ∃ a lo w, Bd S PM planned a F s ra lo w t ∧ a.Ok ∧ runQ planned g a s t
    else if q = ".LB.Emission.run.1" then
      ∃ a lo w, Bd S PM planned a F s ra lo w t ∧ t.regs.rbx.toBitVec = S ∧ a.Ok ∧
        Keep g a ∧ Flat.removeSurplus (flat g) = (.done, flat a)
    else if q = ".LB.Emission.run.2" then
      ∃ a l lo w, Phase S PM planned g a F s ra l lo w t ∧
        t.regs.r12.toBitVec = a.h.n ∧ t.regs.rcx.toBitVec = a.h.pend ∧
        t.regs.rax.toBitVec < a.h.n ∧ a.h.len + a.h.pend = a.h.n ∧
        Flat.unmappedFrom (flat a) (t.regs.rax.toBitVec + 1#64) t.regs.rdx.toBitVec =
          Flat.unmappedFrom (flat a) 0#64 0#64
    else if q = ".LB.Emission.run.3" then
      ∃ a l lo w, Phase S PM planned g a F s ra l lo w t ∧
        t.regs.r12.toBitVec = a.h.n ∧ t.regs.rcx.toBitVec = a.h.pend ∧
        t.regs.rax.toBitVec < a.h.n ∧ a.h.len + a.h.pend = a.h.n ∧
        Flat.unmappedFrom (flat a) t.regs.rax.toBitVec t.regs.rdx.toBitVec =
          Flat.unmappedFrom (flat a) 0#64 0#64
    else if q = ".LB.Emission.run.4" then
      ∃ a l lo w, Phase S PM planned g a F s ra l lo w t ∧
        t.regs.r12.toBitVec = a.h.n ∧ t.regs.rdx.toBitVec = a.h.tgt ∧
        t.regs.rax.toBitVec < a.h.n ∧ a.h.len + a.h.pend = a.h.n ∧
        Flat.unmappedFrom (flat a) 0#64 0#64 = a.h.pend ∧ Flat.availableFrom (flat a) 0#64 = true ∧
        Flat.labelsFrom (flat a) (t.regs.rax.toBitVec + 1#64) = Flat.labelsFrom (flat a) 0#64
    else if q = ".LB.Emission.run.5" then
      ∃ a l lo w, Phase S PM planned g a F s ra l lo w t ∧
        t.regs.r12.toBitVec = a.h.n ∧ t.regs.rdx.toBitVec = a.h.tgt ∧
        t.regs.rax.toBitVec < a.h.n ∧ a.h.len + a.h.pend = a.h.n ∧
        Flat.unmappedFrom (flat a) 0#64 0#64 = a.h.pend ∧ Flat.availableFrom (flat a) 0#64 = true ∧
        Flat.labelsFrom (flat a) t.regs.rax.toBitVec = Flat.labelsFrom (flat a) 0#64
    else if q = ".LB.Emission.run.6" then
      ∃ a l lo w, Phase S PM planned g a F s ra l lo w t ∧
        Flat.availableFrom (flat a) 0#64 = false
    else if q = ".LB.Emission.run.7" then
      ∃ a l lo w, Phase S PM planned g a F s ra l lo w t ∧
        t.regs.rcx.toBitVec = a.h.pend ∧ a.h.n = 0#64 ∧ a.h.len + a.h.pend = a.h.n
    else if q = ".LB.Emission.run.8" then
      ∃ a l lo w, Phase S PM planned g a F s ra l lo w t ∧ checks (flat a)
    else if q = ".LB.Emission.run.9" then
      ∃ a l lo w, Phase S PM planned g a F s ra l lo w t ∧
        t.regs.r12.toBitVec = a.h.n ∧ t.regs.rcx.toBitVec = a.h.pend ∧
        a.h.n ≠ 0#64 ∧ a.h.len + a.h.pend = a.h.n ∧
        t.regs.rdx.toBitVec = Flat.unmappedFrom (flat a) 0#64 0#64
    else if q = ".LB.Emission.run.10" then
      ∃ a l lo w, Phase S PM planned g a F s ra l lo w t ∧
        t.regs.r12.toBitVec = a.h.n ∧ t.regs.rbp.toBitVec < a.h.n ∧
        a.h.len + a.h.pend = a.h.n ∧ Flat.unmappedFrom (flat a) 0#64 0#64 = a.h.pend ∧
        Flat.availableFrom (flat a) t.regs.rbp.toBitVec = Flat.availableFrom (flat a) 0#64
    else False
  | .exit, _ => False

def V (q : Label) (t : MachineData) : Nat :=
  if q = Names.run then 15000
  else if q = ".LB.Emission.run.1" then 14000
  else if q = ".LB.Emission.run.3" then 10001 + 2 * (MAX_N - t.regs.rax.toBitVec.toNat)
  else if q = ".LB.Emission.run.2" then 10000 + 2 * (MAX_N - t.regs.rax.toBitVec.toNat)
  else if q = ".LB.Emission.run.9" then 9000
  else if q = ".LB.Emission.run.10" then 6000 + (MAX_N - t.regs.rbp.toBitVec.toNat)
  else if q = ".LB.Emission.run.7" then 5000
  else if q = ".LB.Emission.run.5" then 2001 + 2 * (MAX_N - t.regs.rax.toBitVec.toNat)
  else if q = ".LB.Emission.run.4" then 2000 + 2 * (MAX_N - t.regs.rax.toBitVec.toNat)
  else if q = ".LB.Emission.run.6" ∨ q = ".LB.Emission.run.8" then 1
  else 0

def E (S PM : Addr) (planned : Vector Word MAX_N) (g : G) (F : MProp 64)
    (s : MachineData) (ra : Int64) : Int64 → MachineData → Prop :=
  fun a t => a = ra ∧
    VPost (RunView PM planned) G.Ok S F runD (fun g' t => runQ planned g g' s t) s t ∧
      Sep.mod.Agree s t

def Obl [Host] [FunDecls] (S PM : Addr) (planned : Vector Word MAX_N) (g : G) (F : MProp 64)
    (s : MachineData) (ra : Int64) (blk : Program.Block) : Prop :=
  ∀ t, Inv S PM planned g F s ra blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv S PM planned g F s ra c u ∧ Program.Decreases V blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels runAsm) (s.pushRa ra) I' (E S PM planned g F s ra)) t

end Bbu.Unit.RunU
