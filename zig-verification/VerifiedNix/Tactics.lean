module

public import Kraken.StateCfg

/-! Kraken's `kfinish` in an ordinary tactic proof. -/

public section

syntax (name := kfinishTactic) "kfinish" (ppSpace Lean.Parser.Tactic.configItem)*
    (ppSpace &"only")? (" [" withoutPosition(Lean.Parser.Tactic.grindParam,*) "]")? : tactic

macro_rules
  | `(tactic| kfinish $cfg* $[only%$o]? $[[$ps,*]]?) =>
    `(tactic| sym => kfinish $cfg* $[only%$o]? $[[$ps,*]]?)
