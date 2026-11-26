module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

@[expose] public section

/-! The simp sets of `lift_block` (`Lift/Tactic/Block.lean`).

- `lift_site`: the normal form of a site body (address arithmetic of the exact L1, the register
  slices). `lift_block` uses it with the default simp set, as the site scripts of
  `Lift/Spike/Sites/*.lean` do.
- `lift_flag`: the value of a flag condition after a compare (`je`, `jbe`).
- `lift_addr`: the normal form of an address, for the match of an access with its hypothesis. -/

register_simp_attr lift_site
register_simp_attr lift_flag
register_simp_attr lift_addr
