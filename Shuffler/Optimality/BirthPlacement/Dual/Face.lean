import Shuffler.Optimality.BirthPlacement.Dual

namespace Shuffler.Optimality.BirthPlacement.Dual

variable {target : Stack} {gapCount reach swap : Nat}

def Certificate.birthPrice (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap) (birth : Fin target.length) (value : Value) : Int :=
  ∑ gap, if birth.val ≤ (gaps gap).cut ∧ value = (gaps gap).value
    then (cert.quotaWeight gap : Int) else 0

def Certificate.EdgeTight (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap) (swap : Nat) (birth output : Fin target.length) : Prop :=
  (if birth = output then (↑(cert.scale * swap) : Int) else 0) +
    cert.birthPrice gaps birth target[output] = cert.row birth + cert.column output

instance (cert : Certificate target.length gapCount) (gaps : Fin gapCount → Gap)
    (swap : Nat) (birth output : Fin target.length) : Decidable (cert.EdgeTight gaps swap birth output) := by
  unfold Certificate.EdgeTight
  infer_instance

-- A nonidentity tight edge reaches a column with minimum price among
-- all eligible columns of the same value.
theorem Certificate.generic_column_min (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap)
    (hvalid : cert.ValidOn gaps swap (fun birth output => birth.val ≤ output.val + reach))
    (birth output other : Fin target.length) (hne : birth ≠ output)
    (htight : cert.EdgeTight gaps swap birth output)
    (hvalue : target[output] = target[other]) (hother : birth.val ≤ other.val + reach) :
    cert.column output ≤ cert.column other := by
  have he : cert.birthPrice gaps birth target[output] = cert.row birth + cert.column output := by
    simpa only [EdgeTight, hne, ite_false, zero_add] using htight
  have hb := hvalid.2.1 birth other hother
  change (if birth = other then (↑(cert.scale * swap) : Int) else 0) +
    cert.birthPrice gaps birth target[other] ≤ cert.row birth + cert.column other at hb
  rw [← hvalue, he] at hb
  split_ifs at hb <;> omega

theorem Certificate.generic_identity_gap (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap)
    (hvalid : cert.ValidOn gaps swap (fun birth output => birth.val ≤ output.val + reach))
    (birth output : Fin target.length) (hne : birth ≠ output)
    (htight : cert.EdgeTight gaps swap birth output) (hvalue : target[output] = target[birth]) :
    cert.column output + (cert.scale * swap : Nat) ≤ cert.column birth := by
  have he : cert.birthPrice gaps birth target[output] = cert.row birth + cert.column output := by
    simpa only [EdgeTight, hne, ite_false, zero_add] using htight
  have hb := hvalid.2.1 birth birth (Nat.le_add_right _ _)
  change (if birth = birth then (↑(cert.scale * swap) : Int) else 0) +
    cert.birthPrice gaps birth target[birth] ≤ cert.row birth + cert.column birth at hb
  rw [ite_eq_left rfl, ← hvalue, he] at hb
  omega

-- A row with both a tight identity and a tight same-value nonidentity
-- edge connects two column levels separated by exactly the identity reward.
theorem Certificate.pin_bridge (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap) (birth output : Fin target.length) (hne : birth ≠ output)
    (hpin : cert.EdgeTight gaps swap birth birth)
    (hgeneric : cert.EdgeTight gaps swap birth output)
    (hvalue : target[output] = target[birth]) :
    cert.column birth = cert.column output + (cert.scale * swap : Nat) := by
  change (if birth = birth then (↑(cert.scale * swap) : Int) else 0) +
    cert.birthPrice gaps birth target[birth] = cert.row birth + cert.column birth at hpin
  rw [ite_eq_left rfl] at hpin
  simp only [EdgeTight, ite_eq_right hne, zero_add, hvalue] at hgeneric
  omega

-- Eligibility sets shrink with the birth row, so their minimum levels increase.
theorem Certificate.generic_levels_mono (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap)
    (hvalid : cert.ValidOn gaps swap (fun birth output => birth.val ≤ output.val + reach))
    (first second left right : Fin target.length) (hrows : first.val ≤ second.val)
    (hfirst : first ≠ left) (htight : cert.EdgeTight gaps swap first left)
    (hvalue : target[left] = target[right]) (hright : second.val ≤ right.val + reach) :
    cert.column left ≤ cert.column right :=
  cert.generic_column_min gaps hvalid first left right hfirst htight hvalue (by omega)

-- A downward column-price step makes the earlier column an identity in
-- every tight assignment, rather than a variable endpoint choice.
theorem Certificate.column_drop_fixed (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap)
    (hvalid : cert.ValidOn gaps swap (fun birth output => birth.val ≤ output.val + reach))
    (assignment : Equiv.Perm (Fin target.length))
    (hlegal : ∀ birth, birth.val ≤ (assignment birth).val + reach)
    (htight : ∀ birth, cert.EdgeTight gaps swap birth (assignment birth))
    (left right : Fin target.length) (horder : left.val ≤ right.val)
    (hvalue : target[left] = target[right]) (hdrop : cert.column right < cert.column left) :
    assignment left = left := by
  let birth := assignment⁻¹ left
  have he : assignment birth = left := assignment.apply_symm_apply left
  by_cases hfixed : birth = left
  · simpa only [hfixed] using he
  · have ht : cert.EdgeTight gaps swap birth left := by simpa only [he] using htight birth
    have hl := hlegal birth
    rw [he] at hl
    have hb := cert.generic_column_min gaps hvalid birth left right hfixed ht hvalue (by omega)
    omega

-- Crossing same-value generic edges have one column level. Their
-- uncrossing stays tight and cannot introduce an identity at positive price.
theorem Certificate.generic_uncross (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap)
    (hvalid : cert.ValidOn gaps swap (fun birth output => birth.val ≤ output.val + reach))
    (hpositive : 0 < swap)
    (first second left right : Fin target.length) (hrows : first.val ≤ second.val)
    (hcolumns : right.val ≤ left.val)
    (hfirst : first ≠ left) (hsecond : second ≠ right)
    (htightFirst : cert.EdgeTight gaps swap first left)
    (htightSecond : cert.EdgeTight gaps swap second right)
    (hvalue : target[left] = target[right]) (hlegal : second.val ≤ right.val + reach) :
    cert.column left = cert.column right ∧ first ≠ right ∧ second ≠ left ∧
      cert.EdgeTight gaps swap first right ∧ cert.EdgeTight gaps swap second left := by
  have hbonus : (0 : Int) < (cert.scale * swap : Nat) := by
    exact_mod_cast Nat.mul_pos hvalid.1 hpositive
  have hle := cert.generic_column_min gaps hvalid first left right hfirst htightFirst hvalue (by omega)
  have hge := cert.generic_column_min gaps hvalid second right left hsecond htightSecond hvalue.symm (by omega)
  have he : cert.column left = cert.column right := by omega
  have hnFirst : first ≠ right := by
    intro hn
    subst right
    have hg := cert.generic_identity_gap gaps hvalid first left hfirst htightFirst hvalue
    omega
  have hnSecond : second ≠ left := by
    intro hn
    subst left
    have hg := cert.generic_identity_gap gaps hvalid second right hsecond htightSecond hvalue.symm
    omega
  refine ⟨he, hnFirst, hnSecond, ?_, ?_⟩
  · simp only [EdgeTight, ite_eq_right hnFirst, zero_add, ← hvalue, ← he]
    simpa only [EdgeTight, ite_eq_right hfirst, zero_add] using htightFirst
  · simp only [EdgeTight, ite_eq_right hnSecond, zero_add, hvalue, he]
    simpa only [EdgeTight, ite_eq_right hsecond, zero_add] using htightSecond

theorem Certificate.value_correct_backward (cert : Certificate target.length gapCount)
    (gaps : Fin gapCount → Gap)
    (hvalid : cert.ValidOn gaps swap (fun birth output => birth.val ≤ output.val + reach))
    (hpositive : 0 < swap) (assignment : Equiv.Perm (Fin target.length))
    (hlegal : ∀ birth, birth.val ≤ (assignment birth).val + reach)
    (htight : ∀ birth, cert.EdgeTight gaps swap birth (assignment birth))
    (birth : Fin target.length) (hmoved : assignment birth ≠ birth)
    (hvalue : target[assignment birth] = target[birth]) :
    (assignment birth).val < birth.val ∧ birth.val < (assignment⁻¹ birth).val := by
  have hbonus : (0 : Int) < (cert.scale * swap : Nat) := by
    exact_mod_cast Nat.mul_pos hvalid.1 hpositive
  have hgap := cert.generic_identity_gap gaps hvalid birth (assignment birth)
    (Ne.symm hmoved) (htight birth) hvalue
  have hdrop : cert.column (assignment birth) < cert.column birth := by omega
  constructor
  · by_contra hn
    exact hmoved (cert.column_drop_fixed gaps hvalid assignment hlegal htight birth
      (assignment birth) (by omega) hvalue.symm hdrop)
  · let before := assignment⁻¹ birth
    have he : assignment before = birth := assignment.apply_symm_apply birth
    have hne : before ≠ birth := by intro hh; exact hmoved (hh ▸ he)
    have ht : cert.EdgeTight gaps swap before birth := by simpa only [he] using htight before
    by_contra hn
    have hle := cert.generic_levels_mono gaps hvalid before birth birth (assignment birth)
      (by omega) hne ht hvalue.symm (hlegal birth)
    omega

end Shuffler.Optimality.BirthPlacement.Dual
