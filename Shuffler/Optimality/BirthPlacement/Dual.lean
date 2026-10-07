import Shuffler.Optimality.BirthPlacement.Global
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {target : Stack}

structure Gap where
  value : Value
  cut : Nat
  required : Nat
  reward : Nat
  deriving DecidableEq

def covers (target : Stack) (gap : Gap) (birth output : Fin target.length) : Prop :=
  birth.val ≤ gap.cut ∧ target[output] = gap.value

instance (target : Stack) (gap : Gap) (birth output : Fin target.length) :
    Decidable (covers target gap birth output) := by unfold covers; infer_instance

def prefixCount (target : Stack) (gap : Gap)
    (assignment : Equiv.Perm (Fin target.length)) : Nat :=
  (Finset.univ.filter fun birth => covers target gap birth (assignment birth)).card

structure Certificate (size gapCount : Nat) where
  scale : Nat
  row : Fin size → Int
  column : Fin size → Int
  quotaWeight : Fin gapCount → Nat
  capWeight : Fin gapCount → Nat

def Certificate.ValidOn (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap) (swap : Nat)
    (allowed : Fin target.length → Fin target.length → Prop) : Prop :=
  0 < cert.scale ∧
  (∀ birth output : Fin target.length, allowed birth output →
    (if birth = output then (↑(cert.scale * swap) : Int) else 0) +
      (∑ gap, if covers target (gaps gap) birth output then (cert.quotaWeight gap : Int) else 0)
      ≤ cert.row birth + cert.column output) ∧
  (∀ gap, cert.scale * (gaps gap).reward ≤ cert.quotaWeight gap + cert.capWeight gap)

instance (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap) (swap : Nat)
    (allowed : Fin target.length → Fin target.length → Prop) [DecidableRel allowed] :
    Decidable (cert.ValidOn gaps swap allowed) := by unfold Certificate.ValidOn; infer_instance

def Certificate.Valid (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap) (swap : Nat) : Prop :=
  cert.ValidOn gaps swap (fun birth output => birth.val ≤ output.val + 16)

instance (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap) (swap : Nat) :
    Decidable (cert.Valid gaps swap) := by unfold Certificate.Valid; infer_instance

def Certificate.rewardUpper (cert : Certificate size gapCount) (gaps : Fin gapCount → Gap) : Int :=
  (∑ index, cert.row index) + (∑ index, cert.column index) -
    (∑ gap, (gaps gap).required * (cert.quotaWeight gap : Int)) +
    ∑ gap, (cert.capWeight gap : Int)

def Certificate.lowerNumerator (cert : Certificate size gapCount)
    (gaps : Fin gapCount → Gap) (direct swap : Nat) : Int :=
  cert.scale * (2 * direct + swap * size : Nat) - cert.rewardUpper gaps

end Shuffler.Optimality.BirthPlacement.Dual
