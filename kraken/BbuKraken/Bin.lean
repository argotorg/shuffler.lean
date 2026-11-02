module

public import BbuKraken.Final
import all BbuKraken.Final
public import BbuKraken.BinHost
import all BbuKraken.BinHost

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

theorem bbu_harness_correct :
    letI := binLinked.decls
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ TopPre s ⦄ buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t =>
        (a = ra ∧ TopPost s t ∧ (topMod s).Agree s t) ∨
        (a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧ TopModelExit s t) ⦄ :=
  buildBottomUp_correct binLinked binBoundary

end Bbu
