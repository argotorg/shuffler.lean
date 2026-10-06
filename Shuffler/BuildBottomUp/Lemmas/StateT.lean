import Std.Internal.Do

namespace Shuffler.BuildBottomUp

-- Keep successful action equations available to the termination proof.
-- These rewrites apply only during well-founded recursion preprocessing.
def bindWithEquation (x : Except ε α)
    (f : (a : α) → x = .ok a → Except ε β) : Except ε β :=
  match x with
  | .ok a => f a rfl
  | .error err => .error err

theorem bind_eq (x : Except ε α) (f : α → Except ε β) :
    (x >>= f) = bindWithEquation x (fun a _ => f a) := by
  cases x <;> rfl

theorem state_bind_apply (x : StateT σ (Except ε) α) (f : α → StateT σ (Except ε) β) (s : σ) :
    (x >>= f) s = bindWithEquation (x s) (fun p _ => f p.1 p.2) := by
  change (x s >>= fun p => f p.1 p.2) = _
  exact bind_eq _ _

theorem state_get_apply (s : σ) : (get : StateT σ (Except ε) σ) s = .ok (s, s) := rfl

theorem state_dite_apply (p : Prop) [Decidable p]
    (yes : p → StateT σ (Except ε) α) (no : ¬p → StateT σ (Except ε) α) (s : σ) :
    (if h : p then yes h else no h) s = if h : p then yes h s else no h s := by
  split <;> rfl

theorem bindWithEquation_ok (a : α)
    (f : (b : α) → (Except.ok a : Except ε α) = .ok b → Except ε β) :
    bindWithEquation (.ok a) f = f a rfl := rfl


open Std.Internal.Do in
theorem preserves_state_of_run (action : StateT σ (Except ε) α)
    (before : σ) (result : α × σ)
    (h : action before = .ok result)
    (hs : ⦃fun s => s = before⦄ action ⦃fun _ s => s = before; epost⟨fun _ => True⟩⦄) :
    result.2 = before := by
  have hp := hs.le_wp before rfl
  rw [StateT.wp_apply_eq] at hp
  change wp (action before) _ _ at hp
  rw [h] at hp
  exact hp

end Shuffler.BuildBottomUp
