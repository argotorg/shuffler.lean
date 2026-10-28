import BbuKraken.Final
import BbuKraken.BinLayout

/-!
A concrete `Host` for the binary `c/bbu_harness` (linked with `-no-pie`). The program
is `c/build_bottom_up.S` then `c/permute.S`. The layout comes from
`BbuKraken/BinLayout.lean`, which `test/bin_layout.sh` makes from the binary. Each
axiom of `Host` is proved by computation. `test/bin_check.sh` compares the directives
with the bytes of the binary.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

def binProg : Program := bbuAsm ++ State.permuteAsm

@[instance_reducible] def binLayout : Layout where
  start := .ofNat BinLayout.start
  size i := BinLayout.sizes.getD i 0

/-! ## The checks -/

-- A label has size 0 and an instruction has a size above 0. There is no data.
def sizeOk : Directive → Nat → Bool
  | .label _, n => n == 0
  | .instr _, n => n != 0
  | .byteArray _, _ => false

def sizesOk : List Directive → List Nat → Bool
  | [], [] => true
  | d :: ds, n :: ns => sizeOk d n && sizesOk ds ns
  | _, _ => false

theorem sizesOk_sound : ∀ {ds : List Directive} {ns : List Nat}, sizesOk ds ns = true →
    ds.length = ns.length ∧ ∀ i d, ds[i]? = some d → sizeOk d (ns.getD i 0) = true
  | [], [], _ => ⟨rfl, by simp⟩
  | d :: ds, n :: ns, h => by
    simp only [sizesOk, Bool.and_eq_true] at h
    obtain ⟨hl, hi⟩ := sizesOk_sound h.2
    refine ⟨by simp [hl], fun i e he => ?_⟩
    cases i with
    | zero => cases he; exact h.1
    | succ i => exact hi i e he
  | [], _ :: _, h | _ :: _, [], h => by simp [sizesOk] at h

theorem binProg_sizesOk : sizesOk binProg BinLayout.sizes = true := by decide +kernel

-- The code ends below the address -1, so addresses do not wrap around.
theorem binProg_fits : BinLayout.start + BinLayout.sizes.sum < 2 ^ 64 - 1 := by decide +kernel

theorem binProg_labels_nodup : (Program.labels binProg).Nodup := by decide +kernel

/-! ## From the checks to the axioms -/

theorem sizeOk_label {l : Label} {n : Nat} (h : sizeOk (.label l) n = true) : n = 0 := by
  simpa [sizeOk] using h

theorem sizeOk_instr {i : Instr} {n : Nat} (h : sizeOk (.instr i) n = true) : 0 < n := by
  simp [sizeOk] at h; omega

theorem sizeOk_zero {d : Directive} (h : sizeOk d 0 = true) : d.Inert := by
  cases d with
  | label => intro _ _ _ _ _ _; exact Iff.rfl
  | instr => simp [sizeOk] at h
  | byteArray => simp [sizeOk] at h

theorem binProg_size {i : Nat} {d : Directive} (h : binProg[i]? = some d) :
    sizeOk d (@Kraken.Layout.size _ binLayout i) = true :=
  (sizesOk_sound binProg_sizesOk).2 i d h

-- The sizes of the directives, in order, are `BinLayout.sizes`.
theorem binExe_sizes : (binLayout.apply binProg).program.map (·.size) = BinLayout.sizes := by
  have hl := (sizesOk_sound binProg_sizesOk).1
  apply List.ext_getElem (by simp [Kraken.Layout.apply, hl])
  intro i h1 h2
  simp only [Kraken.Layout.apply, List.getElem_map, List.getElem_mapIdx]
  show BinLayout.sizes.getD i 0 = _
  simp [List.getD_eq_getElem?_getD, h2]

theorem sum_take_le (l : List Nat) (i : Nat) : (l.take i).sum ≤ l.sum := by
  have := congrArg List.sum (List.take_append_drop i l)
  rw [List.sum_append] at this
  omega

theorem binExe_sizeBefore_le (i : Nat) :
    (binLayout.apply binProg).sizeBefore i ≤ BinLayout.sizes.sum := by
  rw [Kraken.Executable.sizeBefore, List.map_take, binExe_sizes]
  exact sum_take_le _ _

theorem addr_ne {a s : Nat} (h : a + s < 2 ^ 64 - 1) : Int64.ofNat a + Int64.ofNat s ≠ -1 := by
  intro he
  have := congrArg (fun x : Int64 => x.toBitVec.toNat) he
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a + s < 2 ^ 64 by omega)]
    at this
  omega

theorem ofNat_cancel {a s t : Nat} (hs : a + s < 2 ^ 64) (ht : a + t < 2 ^ 64)
    (h : Int64.ofNat a + Int64.ofNat s = Int64.ofNat a + Int64.ofNat t) : s = t := by
  have := congrArg (fun x : Int64 => x.toBitVec.toNat) ((Int64.add_right_inj _).mp h)
  simpa [Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega)]
    using this

/-! ## The host -/

instance binHost : Host where
  prog := binProg
  layout := binLayout
  labels_nodup := binProg_labels_nodup
  label_size _ _ h := sizeOk_label (binProg_size h)
  instr_size_pos _ _ h _ := sizeOk_instr (binProg_size h)
  instr_addr_ne i _ _ := addr_ne (by have := binExe_sizeBefore_le i; have := binProg_fits; omega)
  zero_inert _ _ h hz := sizeOk_zero (hz ▸ binProg_size h)
  addr_determines_offset j k h := by
    have := binExe_sizeBefore_le j
    have := binExe_sizeBefore_le k
    have := binProg_fits
    exact ofNat_cancel (by omega) (by omega) h

/-- `c/build_bottom_up.S` at position 0 and `c/permute.S` right after it. -/
def binLinked : Linked where
  k := 0
  j := bbuAsm.length
  hb := List.prefix_append _ _
  hp := by
    show State.permuteAsm.IsPrefix (binProg.drop bbuAsm.length)
    simp [binProg]

theorem bbu_harness_correct :
    letI := binLinked.decls
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ TopPre s ⦄ buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ TopPost s t ∧ (topMod s).Agree s t ⦄ :=
  buildBottomUp_correct binLinked

-- The checker rejects wrong sizes.
example : sizesOk [.label "a"] [1] = false := rfl
example : sizesOk [.instr (.regular .W64 .W64 .ret)] [0] = false := rfl
example : sizesOk [.byteArray .empty] [1] = false := rfl
example : sizesOk [.label "a"] [] = false := rfl
example : sizesOk [] [0] = false := rfl

end Bbu
