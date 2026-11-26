module

/-
Layouts as data: the description of a struct type for the typed heap (`Lift.Heap.Typed`).

A `StructTy` has a size, an alignment and fields. A field has a name, an offset, a width in bytes
and a kind: a scalar, a pointer to a type, a pointer to a type that may be null, or the address of a
field of an object of a type (`fieldPtr`: a C++ reference into a struct). `Ty` is the type of the type
names; a pointer kind names its target in `Ty`.

A layout is a hint. The proofs about a function use the layout only through lemmas that need
`StructTy.WF` (fields inside the struct, aligned to their width, pairwise disjoint, pointers of 8
bytes), and `Schema` carries that proof for each type. A wrong offset gives a layout that is not
`WF`, or a lifted function whose guards do not hold; it does not give a false theorem.

Where the layouts come from: the first instance (`Node`) is written by hand. Later the layouts come
from DWARF (`DW_TAG_structure_type`, `DW_TAG_member` with `DW_AT_data_member_location` and the
byte size of the member type; a pointer member gets the kind `ptr`/`nullPtr` from the pointee type
and a nullability hint) or from the JSON that the GCC plugin writes. The reader emits a `Schema`
and `decide` checks `WF` for each type.
-/

@[expose] public section

namespace Lift.Heap

inductive Kind (Ty : Type) where
  | scalar
  | ptr (target : Ty)
  | nullPtr (target : Ty)
  /-- The address of the field at byte offset `off` of an object of type `target`. -/
  | fieldPtr (target : Ty) (off : Nat)
  deriving DecidableEq, Repr

def Kind.isPtr {Ty : Type} : Kind Ty → Bool
  | .scalar => false
  | _ => true

structure Field (Ty : Type) where
  name : String
  off : Nat
  width : Nat
  kind : Kind Ty
  deriving DecidableEq, Repr

structure StructTy (Ty : Type) where
  size : Nat
  align : Nat
  fields : List (Field Ty)
  deriving DecidableEq, Repr

/-- The field fits in the struct, is aligned to its width, and a pointer has 8 bytes. -/
def Field.WF {Ty : Type} (size : Nat) (f : Field Ty) : Prop :=
  0 < f.width ∧ f.width ≤ 8 ∧ f.off + f.width ≤ size ∧ f.off % f.width = 0 ∧
    (f.kind.isPtr = true → f.width = 8)

/-- The bytes of the two fields do not overlap. -/
def Field.Apart {Ty : Type} (f g : Field Ty) : Prop :=
  f.off + f.width ≤ g.off ∨ g.off + g.width ≤ f.off

def StructTy.WF {Ty : Type} (T : StructTy Ty) : Prop :=
  0 < T.size ∧ T.size < 2 ^ 64 ∧ 0 < T.align ∧ (∀ f ∈ T.fields, f.WF T.size) ∧
    T.fields.Pairwise Field.Apart

theorem StructTy.WF.size_pos {Ty : Type} {T : StructTy Ty} (h : T.WF) : 0 < T.size := h.1
theorem StructTy.WF.size_lt {Ty : Type} {T : StructTy Ty} (h : T.WF) : T.size < 2 ^ 64 := h.2.1
theorem StructTy.WF.field {Ty : Type} {T : StructTy Ty} (h : T.WF) :
    ∀ f ∈ T.fields, f.WF T.size := h.2.2.2.1
theorem StructTy.WF.apart {Ty : Type} {T : StructTy Ty} (h : T.WF) :
    T.fields.Pairwise Field.Apart := h.2.2.2.2

instance {Ty : Type} (size : Nat) (f : Field Ty) : Decidable (f.WF size) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance {Ty : Type} (f g : Field Ty) : Decidable (f.Apart g) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance {Ty : Type} (T : StructTy Ty) : Decidable T.WF :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (∀ f ∈ T.fields, f.WF T.size) ∧ T.fields.Pairwise Field.Apart))

/-- The layouts of the types of a program; each layout is `WF`. -/
structure Schema (Ty : Type) where
  layout : Ty → StructTy Ty
  wf : ∀ t, (layout t).WF

/-! ### The tree node: `std::_Rb_tree_node_base` (see `Rb.Pred.Layout`) -/

/-- The types of the tree heap: the node and the header have one layout, so one type. -/
inductive NodeTy where
  | node
  deriving DecidableEq, Repr

namespace Node

def color : Field NodeTy := ⟨"_M_color", 0, 4, .scalar⟩
def parent : Field NodeTy := ⟨"_M_parent", 8, 8, .nullPtr .node⟩
def left : Field NodeTy := ⟨"_M_left", 16, 8, .nullPtr .node⟩
def right : Field NodeTy := ⟨"_M_right", 24, 8, .nullPtr .node⟩

/-- 32 bytes, 8-byte aligned; the 4 bytes at offset 4 are padding. -/
def ty : StructTy NodeTy := ⟨32, 8, [color, parent, left, right]⟩

theorem ty_wf : ty.WF := by decide

def schema : Schema NodeTy := ⟨fun _ => ty, fun _ => ty_wf⟩

end Node

end Lift.Heap
