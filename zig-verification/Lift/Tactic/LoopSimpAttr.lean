module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

@[expose] public section

/-- The normal form of `UInt64` sums in `Nat`, for the goals of a loop (`Lift/Tactic/LoopSimp.lean`). -/
register_simp_attr uint_norm

/-- A typed heap load at an index inside the bounds of an array of words. -/
register_simp_attr heap_load

/-- One step of a list: `drop`, `sum` and `getElem` at the present index. -/
register_simp_attr list_step

/-- The heap of a statement as a list of `Obj.words` and the frame: `toObj` of the encoding of a list of words, and the
`map` and `++` of the list of objects. -/
register_simp_attr heap_norm

/-- The equations of `UInt64` as equations of `BitVec 64`, for `bv_omega`: `a = b` becomes `a.toBitVec = b.toBitVec`, and
`toBitVec` goes inside `+`, `-`, `*`, the numbers and `ofBitVec`; with the list rules that the hypotheses need for that
form: `sum` of `++`, a fold that adds each word, `range` and `set` at the index. -/
register_simp_attr bv_norm

/-- The cells of the typed objects of a statement by byte offset (`Lift/Sem/HeapFields.lean`): `cellGet` and `cellSet` on
`::`, `++` and `flatMap`, the sizes, and `toObj` and `Encode.encode` of the objects. -/
register_simp_attr heap_field

/-- The flag normal form (`Lift/Tactic/FlagNorm.lean`): `(if c then 1 else 0)` terms that `|||`, `&&&` or `^^^` combine,
with casts, and a comparison of them, as a Boolean combination of the conditions `c`; each order of `UInt` or `BitVec` as
an order of `toNat`. -/
register_simp_attr flag_norm
