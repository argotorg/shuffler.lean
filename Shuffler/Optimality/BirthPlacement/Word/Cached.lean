import Shuffler.Optimality.BirthPlacement.Word.Theorems
import Mathlib.Data.List.Sigma
import Init.Data.Vector.OfFn

namespace Shuffler.Optimality.BirthPlacement.Word

namespace Cache

variable {α : Type*} [DecidableEq α] {β : α → Type*}

def entries (keys : List α) (value : (key : α) → β key) : List (Sigma β) :=
  keys.map fun key => ⟨key, value key⟩

-- The caller builds and stores the table. Keeping it as explicit data avoids
-- Lean adding the lookup key to a table-building function's runtime arity.
def lookup (table : List (Sigma β)) (value : (key : α) → β key) (key : α) : β key :=
  match table.dlookup key with
    | some result => result
    | none => value key

theorem lookup_entries (keys : List α) (value : (key : α) → β key) (key : α) :
    (entries keys value).dlookup key = if key ∈ keys then some (value key) else none := by
  induction keys with
  | nil => simp [entries]
  | cons first rest ih =>
      by_cases he : first = key
      · subst first
        simp [entries]
      · simp only [entries, List.map_cons, List.dlookup, he, dite_false]
        rw [show (rest.map fun item => (⟨item, value item⟩ : Sigma β)).dlookup key =
          if key ∈ rest then some (value key) else none from ih]
        simp [Ne.symm he]

theorem lookup_entries_eq (keys : List α) (value : (key : α) → β key) (key : α) :
    lookup (entries keys value) value key = value key := by
  unfold lookup
  rw [lookup_entries]
  split_ifs <;> rfl

end Cache

variable {α : Type*} [DecidableEq α] {size : Nat}

def cachedByValue (reach : Nat) (births target : Fin size → α) (hcount : Balanced births target) :
    Equiv.Perm (Fin size) :=
  let valueMap := fun value =>
    (fiber births value).trans
      ((Endpoint.optimal reach (positions births value) (positions target value) (hcount value)).trans
        (fiber target value).symm)
  let table := Cache.entries (List.ofFn births).dedup valueMap
  Equiv.ofFiberEquiv fun value => Cache.lookup table valueMap value

theorem cachedByValue_eq (reach : Nat) (births target : Fin size → α)
    (hcount : Balanced births target) :
    cachedByValue reach births target hcount = optimal reach births target hcount := by
  dsimp only [cachedByValue, optimal]
  congr 1
  funext value
  exact Cache.lookup_entries_eq _ _ _

-- Read each input position once. In the production callers the input
-- functions can index lists, so retaining these values also avoids repeated
-- list scans while the per-value position sets are built.
def cachedOptimal (reach : Nat) (births target : Fin size → α) (hcount : Balanced births target) :
    Equiv.Perm (Fin size) :=
  let birthValues := Vector.ofFn births
  let targetValues := Vector.ofFn target
  cachedByValue reach (fun index : Fin size => birthValues[index.val])
    (fun index : Fin size => targetValues[index.val])
    (by simpa only [birthValues, targetValues, Vector.getElem_ofFn] using hcount)

theorem cachedOptimal_eq (reach : Nat) (births target : Fin size → α)
    (hcount : Balanced births target) :
    cachedOptimal reach births target hcount = optimal reach births target hcount := by
  dsimp only [cachedOptimal]
  simp only [cachedByValue_eq, Vector.getElem_ofFn]

end Shuffler.Optimality.BirthPlacement.Word
