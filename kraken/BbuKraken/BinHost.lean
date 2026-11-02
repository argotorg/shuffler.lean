module

public import BbuKraken.Link
import all BbuKraken.Link
public import BbuKraken.BinLayout
import all BbuKraken.BinLayout

@[expose] public section

/-!
A concrete `Host` for the binary `c/bbu_harness` (linked with `-no-pie`). The program
is `c/build_bottom_up.S`. The layout comes from
`BbuKraken/BinLayout.lean`, which `test/bin_layout.sh` makes from the binary. Each
axiom of `Host` is proved by computation. `test/bin_check.sh` compares the directives
with the bytes of the binary.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

-- The bytes before the shuffler are opaque. Only the external exit address is used.
def binProg : Program := [.label "exit", .byteArray .empty] ++ bbuAsm

def binSizes : List Nat := [0, BinLayout.start - BinLayout.exit] ++ BinLayout.sizes

@[instance_reducible] def binLayout : Layout where
  start := .ofNat BinLayout.exit
  size i := binSizes.getD i 0

/-! ## The checks -/

-- Labels have size 0. Instructions and the opaque prefix have positive size.
def sizeOk : Directive → Nat → Bool
  | .label _, n => n == 0
  | .instr _, n => n != 0
  | .byteArray _, n => n != 0

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

theorem binProg_sizesOk : sizesOk binProg binSizes = true := by decide +kernel

-- The code ends below the address -1, so addresses do not wrap around.
theorem binProg_fits : BinLayout.exit + binSizes.sum < 2 ^ 64 - 1 := by decide +kernel

-- A Boolean check avoids constructing a decidability proof for each label pair.
def labelsDistinct {α : Type} [BEq α] : List α → Bool
  | [] => true
  | l :: ls => !ls.contains l && labelsDistinct ls

theorem labelsDistinct_nodup {α : Type} [BEq α] [LawfulBEq α] {ls : List α} (h : labelsDistinct ls = true) : ls.Nodup := by
  induction ls with
  | nil => exact .nil
  | cons l ls ih =>
    simp only [labelsDistinct, Bool.and_eq_true] at h
    apply List.nodup_cons.mpr
    refine ⟨?_, ih h.2⟩
    intro hm
    have hc := List.contains_iff_mem.mpr hm
    have hn := h.1
    rw [hc] at hn
    contradiction

set_option maxRecDepth 100000 in
theorem binProg_labels_eq : Program.labels binProg = BinLayout.labels := by rfl

def labelCode (s : Label) : Nat :=
  s.toByteArray.data.toList.foldl (fun n c => (n * 257 + c.toNat) % 4294967296) 0

set_option maxRecDepth 100000 in
theorem binProg_labelCodes_eq : BinLayout.labels.map labelCode = BinLayout.labelCodes := by
  rfl

theorem binProg_labels_nodup : (Program.labels binProg).Nodup := by
  rw [binProg_labels_eq]
  have h : BinLayout.labelCodes.Nodup := labelsDistinct_nodup (by decide +kernel)
  rw [← binProg_labelCodes_eq] at h
  exact h.of_map labelCode (fun _ _ hc he => hc (congrArg labelCode he))

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

-- The sizes of the directives of a program with as many directives as `binSizes`, in order,
-- are `binSizes`. With `binProg` in place of `p`, the `simp only` reaches the maximum
-- recursion depth.
theorem apply_sizes {p : Program} (hl : p.length = binSizes.length) :
    (binLayout.apply p).program.map (·.size) = binSizes := by
  apply List.ext_getElem (by simp [Kraken.Layout.apply, hl])
  intro i h1 h2
  simp only [Kraken.Layout.apply, List.getElem_map, List.getElem_mapIdx]
  show binSizes.getD i 0 = _
  simp [List.getD_eq_getElem?_getD, h2]

-- The sizes of the directives, in order, are `binSizes`.
theorem binExe_sizes : (binLayout.apply binProg).program.map (·.size) = binSizes :=
  apply_sizes (sizesOk_sound binProg_sizesOk).1

theorem sum_take_le (l : List Nat) (i : Nat) : (l.take i).sum ≤ l.sum := by
  have := congrArg List.sum (List.take_append_drop i l)
  rw [List.sum_append] at this
  omega

theorem binExe_sizeBefore_le (i : Nat) :
    (binLayout.apply binProg).sizeBefore i ≤ binSizes.sum := by
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

set_option maxRecDepth 100000 in
/-- `c/build_bottom_up.S` after the external label and opaque bytes. -/
def binLinked : Linked where
  k := 2
  hb := List.prefix_refl bbuAsm

theorem binExit_addr : label "exit" = Host.addrOf 1 := by
  have h := Host.label_eq (p := binProg) (k := 0) (i := 0)
    (List.prefix_refl binProg) (show binProg[0]? = some (.label "exit") from rfl)
  have hs := Host.addrOf_succ (k := 0)
    (show Host.prog[0]? = some (.label "exit") from rfl)
  have hz : Kraken.Layout.size Directive 0 = 0 := rfl
  rw [hz] at hs
  simp at hs
  exact h.trans hs.symm

theorem binExit_before (j : Nat) (hj : 2 ≤ j) : label "exit" ≠ Host.addrOf j := by
  have hd : Host.prog[1]? = some (.byteArray .empty) := rfl
  have hc : Host.exe.program[1]? = some
      {directive := .byteArray .empty, size := Kraken.Layout.size Directive 1} := by
    rw [Host.exe_getElem?, hd]
    rfl
  have hz : 0 < Kraken.Layout.size Directive 1 := by decide +kernel
  have hn := Host.addrOf_succ_ne hc hz
  rw [binExit_addr]
  have he : 1 + 1 + (j - 2) = j := by omega
  simpa only [he] using Host.addrOf_ne_of_succ_ne (n := j - 2) hn

theorem binBoundary : ExitBoundary where
  labels l hl := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (Program.mem_labels.mp hl)
    have ha := Host.label_eq binLinked.hb hi
    change label l = Host.addrOf (2 + i) at ha
    rw [ha]
    exact (binExit_before (2 + i) (by omega)).symm
  returns i asz osz f hi := by
    have hi2 : 2 ≤ i := by
      by_cases h : 2 ≤ i
      · exact h
      · have hcases : i = 0 ∨ i = 1 := by omega
        rcases hcases with rfl | rfl <;> cases hi
    exact binExit_before (i + 1) (by omega)

-- The checker rejects wrong sizes.
example : sizesOk [.label "a"] [1] = false := rfl
example : sizesOk [.instr (.regular .W64 .W64 .ret)] [0] = false := rfl
example : sizesOk [.byteArray .empty] [0] = false := rfl
example : sizesOk [.label "a"] [] = false := rfl
example : sizesOk [] [0] = false := rfl

end Bbu
