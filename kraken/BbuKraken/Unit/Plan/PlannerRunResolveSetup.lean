import BbuKraken.Unit.Plan.PlannerRunResolveDefs

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

def resolveLocals (locals : List Word) (hl : locals.length = 4121) : List Word :=
  ((locals.set 0 (resolveOffset locals hl)).set 0 (resolveOffset locals hl)).set 1
    (resolveExcess locals hl)

section
variable {P : Addr} {g : PlannerRunG} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}

theorem PostEmitLI.resolveSetup (h : PostEmitLI P g M F s ra lo locals t)
    (hl : locals.length = 4121)
    (hm : u.dmem = ((t.dmem.storeInt t.regs.rsp.toBitVec 8
      (resolveOffset locals hl).toInt).storeInt t.regs.rsp.toBitVec 8
        (resolveOffset locals hl).toInt).storeInt (t.regs.rsp.toBitVec + 8#64) 8
          (resolveExcess locals hl).toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) :
    PostEmitLI P g M F s ra lo (resolveLocals locals hl) u := by
  let v : MachineData := {t with dmem := (t.dmem.storeInt t.regs.rsp.toBitVec 8
    (resolveOffset locals hl).toInt)}
  have h1 : PostEmitLI P g M F s ra lo (locals.set 0 (resolveOffset locals hl)) v :=
    h.storeFront (by decide) (resolveOffset locals hl) (by simp [v])
      rfl rfl rfl rfl rfl rfl
  let w : MachineData := {v with dmem := (v.dmem.storeInt t.regs.rsp.toBitVec 8
    (resolveOffset locals hl).toInt)}
  have h2 : PostEmitLI P g M F s ra lo
      ((locals.set 0 (resolveOffset locals hl)).set 0 (resolveOffset locals hl)) w :=
    h1.storeFront (by decide) (resolveOffset locals hl) (by simp [w, v])
      rfl rfl rfl rfl rfl rfl
  exact h2.storeFront (by decide) (resolveExcess locals hl) hm hsp hbx h12 h15 h14 h13

theorem ResolveInputs.resolveLocals {hl : locals.length = 4121} (h : ResolveInputs g M locals hl)
    (hl' : (resolveLocals locals hl).length = 4121) :
    ResolveInputs g M (resolveLocals locals hl) hl' :=
  ((h.set_front (by decide) _ (by simpa using hl)).set_front (by decide) _
    (by simpa using hl)).set_front (by decide) _ hl'

theorem resolveLocals_current (hl : locals.length = 4121)
    (hl' : (resolveLocals locals hl).length = 4121) :
    localCurrentMapping (resolveLocals locals hl) hl' = localCurrentMapping locals hl := by
  simp only [resolveLocals]
  rw [localCurrentMapping_set_front (by simp [hl]) (by decide),
    localCurrentMapping_set_front (by simp [hl]) (by decide),
    localCurrentMapping_set_front hl (by decide)]

theorem resolveLocals_size (hl : locals.length = 4121)
    (hl' : (resolveLocals locals hl).length = 4121) :
    resolveSize (resolveLocals locals hl) hl' = resolveSize locals hl := by
  simp [resolveSize, resolveLocals]

end
end Bbu.Unit.PlannerRunU
