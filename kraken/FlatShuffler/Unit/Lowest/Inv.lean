module

public import FlatShuffler.Unit.Lowest.Frame
import all FlatShuffler.Unit.Lowest.Frame
public import FlatShuffler.Unit.Permute.Util
import all FlatShuffler.Unit.Permute.Util
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

/-!
# `permuteAtLowestHeight`: the invariant and the variant of each block

`st` is `flat g` for the entry ghost `g`: the function does not change the struct before the
call of `permute`. `l0` is the content of the local arrays at the entry, and `scan0` is
`Flat.scan planned st 0 (Flat.Scan.init l0)`.

* `.0`: the first loop at `pos = rax < size`; `scan` from `rax` with the locals in memory gives
  `scan0`. `r8` is `holeCount` and `rsi` is `parkedCount`.
* `.1`: the scan loads after the destination assertion.
* `.2`, `.8`, `.9`: the step of the first loop at `rax`, after the assertions.
* `.3`: the end of the step: `scan` from `rax + 1` gives `scan0`.
* `.4`: the second loop at `i` with `rax = 8 * i`; `fill` from `i` gives the argument of
  `permute`.
* `.5`: the call of `permute` and the return.
* `.6`, `.7`: an assertion of the first loop fails.

The variant: `2 * (1024 - rax)` and a constant in the first loop, `1024 - i` in the second loop.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace FlatShuffler.Flat

section
variable {planned : Vector Word maxStackSize} {st : St} {pos : Word} {sc : Scan}

theorem scan_lt (h : pos < st.size) (hd : get st.dest pos ≠ NONE) (ht : pos < st.targetSize) :
    scan planned st pos sc
      = scan planned st (pos + 1) (scanStep planned st pos (get st.dest pos) sc) := by
  rw [scan, dite_eq_left h]
  simp only [hd, ht, not_true_eq_false, ite_false]

theorem scan_none_dest (h : pos < st.size) (hd : get st.dest pos = NONE) :
    scan planned st pos sc = none := by
  rw [scan, dite_eq_left h]
  simp only [hd, ite_true]

theorem scan_none_tgt (h : pos < st.size) (hd : get st.dest pos ≠ NONE)
    (ht : ¬pos < st.targetSize) : scan planned st pos sc = none := by
  rw [scan, dite_eq_left h]
  simp only [hd, ht, not_false_eq_true, ite_true, ite_false]

theorem scan_ge (h : ¬pos < st.size) : scan planned st pos sc = some sc := by
  rw [scan, dite_eq_right h]

end

theorem fill_lt {sc : Scan} {i : Word} {p : Vector Word maxStackSize} (h : i < sc.parkedCount) :
    fill sc i p = fill sc (i + 1) (put p (get sc.parked i) (get sc.holes i)) := by
  rw [fill, dite_eq_left h]

theorem fill_ge {sc : Scan} {i : Word} {p : Vector Word maxStackSize} (h : ¬i < sc.parkedCount) :
    fill sc i p = p := by
  rw [fill, dite_eq_right h]

section
variable {planned : Vector Word maxStackSize} {l : Locals} {st : St}

theorem lowest_none (h : scan planned st 0 (Scan.init l) = none) :
    permuteAtLowestHeight planned l st = (.assertionFailed, st) := by
  rw [permuteAtLowestHeight, h]

theorem lowest_ne {sc : Scan} (h : scan planned st 0 (Scan.init l) = some sc)
    (hne : sc.parkedCount ≠ sc.holeCount) :
    permuteAtLowestHeight planned l st = (.assertionFailed, st) := by
  rw [permuteAtLowestHeight, h]; exact ite_eq_left hne

theorem lowest_eq {sc : Scan} (h : scan planned st 0 (Scan.init l) = some sc)
    (heq : sc.parkedCount = sc.holeCount) :
    permuteAtLowestHeight planned l st = permute st (fill sc 0 sc.permutation) := by
  rw [permuteAtLowestHeight, h]; exact ite_eq_right (fun h => h heq)

end

end FlatShuffler.Flat

namespace FlatShuffler.Unit
open FlatShuffler.Sep
namespace Lowest

/-! ## The step of the first loop -/

-- The locals of the first loop: the arrays `L` and the counts.
def Lc.scan (L : Lc) (hc pc : Word) : Flat.Scan := ⟨L.perm, L.holes, L.parked, hc, pc⟩

section
variable {planned : Vector Word maxStackSize} {st : Flat.St} {pos d hc pc : Word} {L : Lc}

-- `.2`: a parked slot and a hole: `permutation[pos] = pos`.
theorem step_ph (hp : ¬d < st.size) (hh : Flat.get planned pos = Flat.NONE) :
    Flat.scanStep planned st pos d (L.scan hc pc)
      = Lc.scan { L with perm := Flat.put L.perm pos pos } hc pc := by
  have hp' : st.size ≤ d := by bv_omega
  simp [Flat.scanStep, Lc.scan, hp', hh]

-- `.9`: a parked slot that is not a hole: `parked[pc] = pos`.
theorem step_pn (hp : ¬d < st.size) (hh : Flat.get planned pos ≠ Flat.NONE) :
    Flat.scanStep planned st pos d (L.scan hc pc)
      = Lc.scan { L with parked := Flat.put L.parked pc pos } hc (pc + 1) := by
  have hp' : st.size ≤ d := by bv_omega
  simp [Flat.scanStep, Lc.scan, hp', hh]

-- `.8`: a slot that is not parked and a hole: `permutation[pos] = d`, `holes[hc] = pos`.
theorem step_uh (hp : d < st.size) (hh : Flat.get planned pos = Flat.NONE) :
    Flat.scanStep planned st pos d (L.scan hc pc)
      = Lc.scan { L with perm := Flat.put L.perm pos d, holes := Flat.put L.holes hc pos }
          (hc + 1) pc := by
  have hp' : ¬st.size ≤ d := by bv_omega
  simp [Flat.scanStep, Lc.scan, hp', hh]

-- `.8`: a slot that is not parked and not a hole: `permutation[pos] = d`.
theorem step_un (hp : d < st.size) (hh : Flat.get planned pos ≠ Flat.NONE) :
    Flat.scanStep planned st pos d (L.scan hc pc)
      = Lc.scan { L with perm := Flat.put L.perm pos d } hc pc := by
  have hp' : ¬st.size ≤ d := by bv_omega
  simp [Flat.scanStep, Lc.scan, hp', hh]

end

/-! ## The invariants -/

section
variable (S PM : Addr) (planned : Vector Word maxStackSize) (g : G) (F0 : MProp 64) (s : MachineData)
  (ra : Int64)

-- A body state with the locals `L`; `rdi` is the struct.
def Bs (L : Lc) (t : MachineData) : Prop :=
  ∃ lo w, Mid S g (Planned S PM planned ∗ F0) s ra L lo w t ∧ t.regs.rdi.toBitVec = S

-- The first loop up to the position `p`: `rcx = size`, the counts `r8` and `rsi` are at most
-- `p`, and the parked slots are below the size.
def Sc (L : Lc) (p : Word) (t : MachineData) : Prop :=
  t.regs.rcx.toBitVec = g.h.len ∧ t.regs.rax.toBitVec < g.h.len
    ∧ t.regs.r8.toBitVec ≤ p ∧ t.regs.rsi.toBitVec ≤ p
    ∧ ∀ j (hj : j < maxStackSize), j < t.regs.rsi.toBitVec.toNat → L.parked[j] < g.h.len

-- The result of the first loop for the locals `l0` of the entry.
abbrev scan0 (l0 : Flat.Locals) : Option Flat.Scan := Flat.scan planned (flat g) 0 (Flat.Scan.init l0)

-- `.0`: the first loop at `rax`.
def I0 (t : MachineData) : Prop :=
  ∃ L l0, Bs S PM planned g F0 s ra L t ∧ Sc g L t.regs.rax.toBitVec t
    ∧ Flat.scan planned (flat g) t.regs.rax.toBitVec (L.scan t.regs.r8.toBitVec t.regs.rsi.toBitVec)
      = scan0 planned g l0

-- `.1`: the destination assertion has passed.
def IHead (t : MachineData) : Prop :=
  ∃ L l0, Bs S PM planned g F0 s ra L t ∧ Sc g L t.regs.rax.toBitVec t
    ∧ t.regs.rdx.toBitVec = Flat.get (flat g).dest t.regs.rax.toBitVec
    ∧ Flat.get (flat g).dest t.regs.rax.toBitVec ≠ Flat.NONE
    ∧ Flat.scan planned (flat g) t.regs.rax.toBitVec
        (L.scan t.regs.r8.toBitVec t.regs.rsi.toBitVec) = scan0 planned g l0

-- `.2`, `.8`, `.9`: the step at `rax`: `rdx` is the destination and `r9` the planned position.
def IStep (c : Word → Word → Prop) (t : MachineData) : Prop :=
  ∃ L l0, Bs S PM planned g F0 s ra L t ∧ Sc g L t.regs.rax.toBitVec t
    ∧ t.regs.rdx.toBitVec = Flat.get (flat g).dest t.regs.rax.toBitVec
    ∧ t.regs.r9.toBitVec = Flat.get planned t.regs.rax.toBitVec
    ∧ c t.regs.rdx.toBitVec t.regs.r9.toBitVec
    ∧ Flat.scan planned (flat g) (t.regs.rax.toBitVec + 1#64)
        (Flat.scanStep planned (flat g) t.regs.rax.toBitVec t.regs.rdx.toBitVec
          (L.scan t.regs.r8.toBitVec t.regs.rsi.toBitVec))
      = scan0 planned g l0

-- `.3`: the end of the step at `rax`.
def I2 (t : MachineData) : Prop :=
  ∃ L l0, Bs S PM planned g F0 s ra L t ∧ Sc g L (t.regs.rax.toBitVec + 1#64) t
    ∧ Flat.scan planned (flat g) (t.regs.rax.toBitVec + 1#64)
        (L.scan t.regs.r8.toBitVec t.regs.rsi.toBitVec)
      = scan0 planned g l0

-- `.4`: the second loop at `i` with `rax = 8 * i < rsi = 8 * parkedCount`.
def I3 (t : MachineData) : Prop :=
  ∃ L l0 sc k, Bs S PM planned g F0 s ra L t ∧ scan0 planned g l0 = some sc
    ∧ sc.parkedCount = sc.holeCount ∧ L.parked = sc.parked ∧ L.holes = sc.holes
    ∧ t.regs.rax.toBitVec.toNat = 8 * k ∧ k < sc.parkedCount.toNat
    ∧ t.regs.rsi.toBitVec.toNat = 8 * sc.parkedCount.toNat ∧ sc.parkedCount.toNat ≤ 1024
    ∧ (∀ j (hj : j < maxStackSize), j < sc.parkedCount.toNat → sc.parked[j] < g.h.len)
    ∧ Flat.fill sc (BitVec.ofNat 64 k) L.perm = Flat.fill sc 0 sc.permutation

-- `.5`: the array `permutation` is the argument of `permute`.
def I4 (t : MachineData) : Prop :=
  ∃ L l0 sc, Bs S PM planned g F0 s ra L t ∧ scan0 planned g l0 = some sc
    ∧ sc.parkedCount = sc.holeCount ∧ L.perm = Flat.fill sc 0 sc.permutation

-- `.6`, `.7`: an assertion of the first loop fails.
def I5 (t : MachineData) : Prop :=
  ∃ L l0, Bs S PM planned g F0 s ra L t ∧
    Flat.permuteAtLowestHeight planned l0 (flat g) = (.assertionFailed, flat g)

-- `.6`: the result.
def I6 (t : MachineData) : Prop :=
  ∃ g' L lo w, Mid S g' (Planned S PM planned ∗ F0) s ra L lo w t ∧ g'.Ok
    ∧ lowestQ planned g g' s t

-- The invariant of each label.
def LInv : CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.permuteAtLowestHeight then t = s.pushRa ra
    else if l = ".LB.Emission.permuteAtLowestHeight.0" then I0 S PM planned g F0 s ra t
    else if l = ".LB.Emission.permuteAtLowestHeight.1" then IHead S PM planned g F0 s ra t
    else if l = ".LB.Emission.permuteAtLowestHeight.2" then
      IStep S PM planned g F0 s ra (fun d _ => ¬d < g.h.len) t
    else if l = ".LB.Emission.permuteAtLowestHeight.3" then I2 S PM planned g F0 s ra t
    else if l = ".LB.Emission.permuteAtLowestHeight.4" then I3 S PM planned g F0 s ra t
    else if l = ".LB.Emission.permuteAtLowestHeight.5" then I4 S PM planned g F0 s ra t
    else if l = ".LB.Emission.permuteAtLowestHeight.6" then I5 S PM planned g F0 s ra t
    else if l = ".LB.Emission.permuteAtLowestHeight.7" then I5 S PM planned g F0 s ra t
    else if l = ".LB.Emission.permuteAtLowestHeight.8" then
      IStep S PM planned g F0 s ra (fun d _ => d < g.h.len) t
    else if l = ".LB.Emission.permuteAtLowestHeight.9" then
      IStep S PM planned g F0 s ra (fun d p => ¬d < g.h.len ∧ p ≠ Flat.NONE) t
    else False

end

/-! ## The variant -/

def V (l : Label) (t : MachineData) : Nat :=
  if l = Names.permuteAtLowestHeight then 2 ^ 20
  else if l = ".LB.Emission.permuteAtLowestHeight.0" ∨ l = ".LB.Emission.permuteAtLowestHeight.1"
      ∨ l = ".LB.Emission.permuteAtLowestHeight.2"
      ∨ l = ".LB.Emission.permuteAtLowestHeight.8" ∨ l = ".LB.Emission.permuteAtLowestHeight.9" then
    2049 + 2 * (1024 - t.regs.rax.toBitVec.toNat)
  else if l = ".LB.Emission.permuteAtLowestHeight.3" then
    2048 + 2 * (1024 - t.regs.rax.toBitVec.toNat)
  else if l = ".LB.Emission.permuteAtLowestHeight.4" then 1024 - t.regs.rax.toBitVec.toNat / 8
  else 0

/-- The variant goal of `cfg_goto`: `V` at the two literal labels, then `omega` if it can. -/
macro "lowest_dec" : tactic => `(tactic| (
  simp only [V, Names.permuteAtLowestHeight, String.reduceEq, ↓reduceIte, or_self, or_false,
    false_or, true_or, or_true, Nat.lt_irrefl, true_and, and_true, Nat.reducePow]
  try omega))

/-! ## The obligation of a block -/

-- The exception continuation of the body triple.
def E [Host] (S PM : Addr) (planned : Vector Word maxStackSize) (g : G) (F0 : MProp 64) (s : MachineData)
    (ra : Int64) : Int64 → MachineData → Prop :=
  fun a t => (a = ra ∧ Sep.Post S (Planned S PM planned ∗ F0) lowestD
    (fun g' t => lowestQ planned g g' s t) s t ∧ Sep.mod.Agree s t) ∨
    (a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧
      Sep.Post S (Planned S PM planned ∗ F0) lowestD
        (fun g' t => lowestX planned g g' s t) s t)

theorem exit_intercept [Host]
    {S PM : Addr} {planned : Vector Word maxStackSize} {g : G} {F0 : MProp 64}
    {s t : MachineData} {ra exitRa : Int64} {L : Lc} {lo : List Word} {w : Word}
    {I : CfgLabel → Nat → Unit → MachineData → Prop}
    (hout : ∀ l ∈ Program.labels permuteAtLowestHeightAsm, label l ≠ label "exit")
    (hM : Mid S g (Planned S PM planned ∗ F0) s ra L lo w t) (hok : g.Ok)
    (l0 : Flat.Locals)
    (hfail : Flat.permuteAtLowestHeight planned l0 (flat g) = (.assertionFailed, flat g))
    (harg : t.regs.get64 .rdi = 1#64) :
    Program.Intercept (Program.labels permuteAtLowestHeightAsm) (s.pushRa ra) I
      (E S PM planned g F0 s ra) (label "exit") (t.pushRa exitRa) := by
  refine Or.inr ⟨Or.inr ⟨rfl, harg, ?_⟩, ?_⟩
  · refine frame_post (hM.pushExit exitRa) hM.len hok ⟨l0, ?_⟩
    dsimp only [ExitRes]
    rw [hfail]
    exact ⟨Permute.Keep.refl g, rfl, rfl⟩
  · intro l hl ha
    exact False.elim (hout l hl ha)

-- The obligation of `Program.WP.cfg` for the block `blk`.
def Obl [Host] [FunDecls] (S PM : Addr) (planned : Vector Word maxStackSize) (g : G) (F0 : MProp 64)
    (s : MachineData) (ra : Int64) (blk : Program.Block) : Prop :=
  ∀ t, LInv S PM planned g F0 s ra blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      LInv S PM planned g F0 s ra b u ∧ Program.Decreases V blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels permuteAtLowestHeightAsm) (s.pushRa ra) I'
        (E S PM planned g F0 s ra)) t

-- The labels of `permuteAtLowestHeightAsm`, in the order of the blocks.
def labels : List CfgLabel :=
  [.entry, .label "_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv",
    .label ".LB.Emission.permuteAtLowestHeight.0",
    .label ".LB.Emission.permuteAtLowestHeight.1",
    .label ".LB.Emission.permuteAtLowestHeight.2",
    .label ".LB.Emission.permuteAtLowestHeight.3",
    .label ".LB.Emission.permuteAtLowestHeight.4",
    .label ".LB.Emission.permuteAtLowestHeight.5",
    .label ".LB.Emission.permuteAtLowestHeight.6",
    .label ".LB.Emission.permuteAtLowestHeight.7",
    .label ".LB.Emission.permuteAtLowestHeight.8",
    .label ".LB.Emission.permuteAtLowestHeight.9"]

end Lowest
end FlatShuffler.Unit
