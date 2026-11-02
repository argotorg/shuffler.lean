module

public import FlatShuffler.Unit.Permute.Frame
import all FlatShuffler.Unit.Permute.Frame
public import FlatShuffler.Unit.Permute.Cfg
import all FlatShuffler.Unit.Permute.Cfg
public import FlatShuffler.Unit.PermuteModel
import all FlatShuffler.Unit.PermuteModel
public import FlatShuffler.Unit.PermuteSpecs
import all FlatShuffler.Unit.PermuteSpecs
public import FlatShuffler.Unit.Permute.Util
import all FlatShuffler.Unit.Permute.Util

@[expose] public section

/-!
# `permute`: the invariant and the variant of each block

`n` is the size `g.h.len` of the entry ghost `g`, `top` is `n - 1` and `st` is `flat g`.
The invariant of a block is a predicate `I…` on the state at its label (`LInv`). The name of
the predicate is the number of the label. The array `permutation` is the argument at `rsi s`;
at the entry it agrees with the ghost `p0` below `n` (`permuteA`).

* `.LB.Emission.permute.0`: `desiredBy[i] = NONE` below the index of `rax`.
* Phase C (`.LB.Emission.permute.11` to `.LB.Emission.permute.10`, and `.1` to `.10`): the
  loops of `regroup`. The model vectors `p`, `dB` and `pc` are existential; the locals `L.P`
  and `L.D` agree with them below `n` (`AgB`). `RG st p0 X`: the `regroup` of `permute` gives `X`.
* Phase D (`.LB.Emission.permute.12` to `.LB.Emission.permute.24`): the loop of `permute`, with
  the fuel `f` of `permuteLoop`.
* `.LB.Emission.permute.16`: the epilogue. `.LB.Emission.permute.25`: the `ret` if `n = 0`.

The variant `V` decreases on each back edge. Phase D uses `mu` of the array `permutation`
(`memVec`): each iteration of the loop makes it smaller (`swapP_mu`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace FlatShuffler.Unit
open FlatShuffler.Sep
namespace Permute

/-! ## The model vectors -/

-- `v` and `w` agree below `k`.
def AgB (k : Word) (v w : Vector Word MAX_N) : Prop := ∀ i < k, Flat.get v i = Flat.get w i

-- The elements below `n` are below `n`.
def LtB (n : Word) (p : Vector Word MAX_N) : Prop := ∀ i < n, Flat.get p i < n

-- The `regroup` of `permute` with the permutation `p0` gives `X`.
def RG (st : Flat.St) (p0 : Vector Word MAX_N) (X : Option (Vector Word MAX_N)) : Prop :=
  Flat.regroup st 0 p0 (Flat.clearDesired st 0 Flat.initial) = X

-- `placeGroup` from `pos`, then `regroup` from the next leader.
def pg (st : Flat.St) (l : Word) (hl : l < st.size) (σ : StackSlot) (dB : Vector Word MAX_N)
    (pos vac : Word) (pc : Vector Word MAX_N) : Option (Vector Word MAX_N) :=
  match Flat.placeGroup st l hl σ dB pos vac pc with
  | none => none
  | some p => Flat.regroup st (l + 1) p dB

-- The `vacant` loop from `x` for the slot `pos`, then the rest of `pg`.
def nv (st : Flat.St) (l : Word) (hl : l < st.size) (σ : StackSlot) (dB : Vector Word MAX_N)
    (pos x : Word) (pc : Vector Word MAX_N) : Option (Vector Word MAX_N) :=
  if Flat.nextVacant st l σ dB x < st.size then
    pg st l hl σ dB (pos + 1) (Flat.nextVacant st l σ dB x + 1)
      (Flat.put pc pos (Flat.nextVacant st l σ dB x))
  else none

-- The rest of the loop of `permute` after an iteration.
def after (f : Nat) (top : Word) : Flat.PNext → Flat.Status × Flat.St
  | .ret r => r
  | .cont X p => Flat.permuteLoop f X top p

-- The array `permutation` at the argument `rsi s`.
def memVec (s t : MachineData) : Vector Word MAX_N :=
  Vector.ofFn fun i => rd t.dmem (rsi s + BitVec.ofNat 64 (8 * i.val))

/-! ## The invariants -/

section
variable (S : Addr) (g : G) (p0 : Vector Word MAX_N) (F : MProp 64) (s : MachineData)
  (ra : Int64)

-- `.LB.Emission.permute.16`: the result.
def I6 (t : MachineData) : Prop :=
  ∃ g' L, Fm S g' F s ra L t ∧ g'.Ok ∧ permuteQ p0 g g' s t

-- `.LB.Emission.permute.25`: the size is 0; no frame.
def I25 (t : MachineData) : Prop :=
  ∃ fr, Kp S g (permW s ∗ F) s ra fr t ∧ fr.length = 1034 ∧ g.Ok ∧
    Flat.permute (flat g) p0 = (.done, flat g)

-- `.LB.Emission.permute.0`: `desiredBy[i] = NONE` below `k`; `rax` is the address of
-- `desiredBy[k]`.
def I0 (t : MachineData) : Prop :=
  ∃ L, ∃ k : Nat, Fm S g F s ra L t ∧ t.regs.r13.toBitVec = S ∧ t.regs.r15.toBitVec = rsi s
    ∧ k < g.h.len.toNat
    ∧ t.regs.rax.toBitVec = base s + 16#64 + BitVec.ofNat 64 (8 * k)
    ∧ t.regs.rdx.toBitVec = base s + 16#64 + BitVec.ofNat 64 (8 * g.h.len.toNat)
    ∧ (∀ i : Word, i.toNat < k → Flat.get L.D i = Flat.NONE) ∧ AgB g.h.len L.P p0

-- Phase C: the leader `l` in `rbx`.
structure CC (L : Lc) (l : Word) (t : MachineData) : Prop where
  fm : Fm S g F s ra L t
  lt : l < g.h.len
  bx : t.regs.rbx.toBitVec = l
  r14 : t.regs.r14.toBitVec = l + 1
  bp : t.regs.rbp.toBitVec = base s + 16#64
  r13 : t.regs.r13.toBitVec = S
  r15 : t.regs.r15.toBitVec = rsi s

-- Phase C in a group: `8(%rsp)` is the stack and `r12` is the slot of the leader.
structure GC (L : Lc) (l : Word) (t : MachineData) : Prop where
  cc : CC S g F s ra L l t
  c1 : L.c1 = g.h.data
  r12 : StackSlot.ofWord t.regs.r12.toBitVec = Flat.get (flat g).data l

-- `.LB.Emission.permute.11`: `regroup` from the leader `l`.
def I12 (t : MachineData) : Prop :=
  ∃ L l p dB, CC S g F s ra L l t ∧ RG (flat g) p0 (Flat.regroup (flat g) l p dB)
    ∧ AgB g.h.len L.P p ∧ AgB g.h.len L.D dB ∧ LtB g.h.len p

-- `.LB.Emission.permute.10`: `regroup` from the leader `l + 1`.
def I11 (t : MachineData) : Prop :=
  ∃ L l p dB, CC S g F s ra L l t ∧ RG (flat g) p0 (Flat.regroup (flat g) (l + 1) p dB)
    ∧ AgB g.h.len L.P p ∧ AgB g.h.len L.D dB ∧ LtB g.h.len p

-- `.LB.Emission.permute.2`: `markDesired` from `j`; `rax` is `8 * j`.
def I2 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ p dB j, GC S g F s ra L l t ∧ j ≤ l
    ∧ t.regs.rax.toBitVec = j * 8#64
    ∧ t.regs.rcx.toBitVec = (l + 1) * 8#64
    ∧ RG (flat g) p0 (pg (flat g) l hl (Flat.get (flat g).data l)
        (Flat.markDesired (flat g) l hl (Flat.get (flat g).data l) p j dB) 0 0 p)
    ∧ AgB g.h.len L.P p ∧ AgB g.h.len L.D dB ∧ LtB g.h.len p

-- `.LB.Emission.permute.1`: `markDesired` from `j + 1`; `rax` is `8 * j`.
def I1 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ p dB j, GC S g F s ra L l t ∧ j ≤ l
    ∧ t.regs.rax.toBitVec = j * 8#64
    ∧ t.regs.rcx.toBitVec = (l + 1) * 8#64
    ∧ RG (flat g) p0 (pg (flat g) l hl (Flat.get (flat g).data l)
        (Flat.markDesired (flat g) l hl (Flat.get (flat g).data l) p (j + 1) dB) 0 0 p)
    ∧ AgB g.h.len L.P p ∧ AgB g.h.len L.D dB ∧ LtB g.h.len p

-- `.LB.Emission.permute.3`: `placeGroup` from the start.
def I3 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ p dB, GC S g F s ra L l t
    ∧ RG (flat g) p0 (pg (flat g) l hl (Flat.get (flat g).data l) dB 0 0 p)
    ∧ AgB g.h.len L.P p ∧ AgB g.h.len L.D dB ∧ LtB g.h.len p

-- `.LB.Emission.permute.9`: `placeGroup` from `pos` (`rcx`) with `vacant` in `rax`.
def I10 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ dB pos vac pc, GC S g F s ra L l t ∧ pos ≤ l
    ∧ vac ≤ g.h.len ∧ t.regs.rcx.toBitVec = pos ∧ t.regs.rax.toBitVec = vac
    ∧ RG (flat g) p0 (pg (flat g) l hl (Flat.get (flat g).data l) dB pos vac pc)
    ∧ AgB g.h.len L.P pc ∧ AgB g.h.len L.D dB ∧ LtB g.h.len pc

-- `.LB.Emission.permute.8`: `placeGroup` from `pos + 1`.
def I9 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ dB pos vac pc, GC S g F s ra L l t ∧ pos ≤ l
    ∧ vac ≤ g.h.len ∧ t.regs.rcx.toBitVec = pos ∧ t.regs.rax.toBitVec = vac
    ∧ RG (flat g) p0 (pg (flat g) l hl (Flat.get (flat g).data l) dB (pos + 1) vac pc)
    ∧ AgB g.h.len L.P pc ∧ AgB g.h.len L.D dB ∧ LtB g.h.len pc

-- `.LB.Emission.permute.4`: the `vacant` loop from `x` (`rax`) for the slot `pos`; `rdi` is
-- the stack.
def I4 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ dB pos x pc, GC S g F s ra L l t ∧ pos ≤ l
    ∧ x ≤ g.h.len ∧ t.regs.rcx.toBitVec = pos ∧ t.regs.rax.toBitVec = x
    ∧ t.regs.rdi.toBitVec = g.h.data
    ∧ RG (flat g) p0 (nv (flat g) l hl (Flat.get (flat g).data l) dB pos x pc)
    ∧ AgB g.h.len L.P pc ∧ AgB g.h.len L.D dB ∧ LtB g.h.len pc

-- `.LB.Emission.permute.7`: and `x < n`; `rsi` is `n`.
def I8 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ dB pos x pc, GC S g F s ra L l t ∧ pos ≤ l
    ∧ x < g.h.len ∧ t.regs.rcx.toBitVec = pos ∧ t.regs.rax.toBitVec = x
    ∧ t.regs.rdi.toBitVec = g.h.data ∧ t.regs.rsi.toBitVec = g.h.len
    ∧ RG (flat g) p0 (nv (flat g) l hl (Flat.get (flat g).data l) dB pos x pc)
    ∧ AgB g.h.len L.P pc ∧ AgB g.h.len L.D dB ∧ LtB g.h.len pc

-- `.LB.Emission.permute.6`: `x` is not vacant; the loop goes on from `x + 1`.
def I7 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ dB pos x pc, GC S g F s ra L l t ∧ pos ≤ l
    ∧ x < g.h.len ∧ t.regs.rcx.toBitVec = pos ∧ t.regs.rax.toBitVec = x
    ∧ t.regs.rdi.toBitVec = g.h.data ∧ t.regs.rsi.toBitVec = g.h.len
    ∧ RG (flat g) p0 (nv (flat g) l hl (Flat.get (flat g).data l) dB pos (x + 1) pc)
    ∧ AgB g.h.len L.P pc ∧ AgB g.h.len L.D dB ∧ LtB g.h.len pc

-- `.LB.Emission.permute.5`: `regroup` fails.
def I5 (t : MachineData) : Prop :=
  ∃ L, Fm S g F s ra L t ∧ Flat.permute (flat g) p0 = (.assertionFailed, flat g)

-- `.LB.Emission.permute.12`: `regroup` gives `p`; `rcx` is `n`.
def I13 (t : MachineData) : Prop :=
  ∃ L p, Fm S g F s ra L t ∧ t.regs.r13.toBitVec = S ∧ t.regs.r15.toBitVec = rsi s
    ∧ t.regs.rcx.toBitVec = g.h.len ∧ 0 < g.h.len
    ∧ RG (flat g) p0 (some p) ∧ AgB g.h.len L.P p

-- Phase D: the struct `g'`, the locals `L` and the permutation `p`. `rcx` is `n` and `rsi`
-- is `top`.
structure DC (g' : G) (L : Lc) (p : Vector Word MAX_N) (t : MachineData) : Prop where
  fm : Fm S g' F s ra L t
  ok : g'.Ok
  keep : Keep g g'
  len : g'.h.len = g.h.len
  pos : 0 < g.h.len
  dl : DestOk (flat g')
  r13 : t.regs.r13.toBitVec = S
  r15 : t.regs.r15.toBitVec = rsi s
  cx : t.regs.rcx.toBitVec = g.h.len
  si : t.regs.rsi.toBitVec = (g.h.len - 1 : Word)
  agP : AgB g.h.len L.P p
  bij : Bij g.h.len p

-- `.LB.Emission.permute.21`: the head of the loop, with the fuel `f`.
def I21 (t : MachineData) : Prop :=
  ∃ g' L p f, DC S g F s ra g' L p t
    ∧ Flat.permute (flat g) p0 = Flat.permuteLoop f (flat g') (g.h.len - 1) p
    ∧ mu (g.h.len - 1) p ≤ f ∧ g'.h.nops.toNat + f ≤ 6 * g.h.n.toNat + g.xo

-- `.LB.Emission.permute.13`: `permutation[top] = top`.
def I14 (t : MachineData) : Prop :=
  ∃ g' L p f, DC S g F s ra g' L p t
    ∧ Flat.permute (flat g) p0 = after f (g.h.len - 1) (Flat.permuteStep (flat g') (g.h.len - 1) p)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f + 1 ≤ 6 * g.h.n.toNat + g.xo
    ∧ Flat.get p (g.h.len - 1) = g.h.len - 1

-- `.LB.Emission.permute.14`: the `candidate` loop at `c` (`rdx`).
def I15 (t : MachineData) : Prop :=
  ∃ g' L p f c, DC S g F s ra g' L p t
    ∧ Flat.permute (flat g) p0 = after f (g.h.len - 1) (Flat.permuteStep (flat g') (g.h.len - 1) p)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f + 1 ≤ 6 * g.h.n.toNat + g.xo
    ∧ Flat.get p (g.h.len - 1) = g.h.len - 1
    ∧ t.regs.rdx.toBitVec = c ∧ c ≤ g.h.len - 1
    ∧ Flat.misplacedBelow p (g.h.len - 1) (g.h.len - 1)
      = Flat.misplacedBelow p (g.h.len - 1) c

-- `.LB.Emission.permute.17`: `pos = c - 1` is misplaced.
def I17 (t : MachineData) : Prop :=
  ∃ g' L p f c, DC S g F s ra g' L p t
    ∧ Flat.permute (flat g) p0 = after f (g.h.len - 1) (Flat.permuteStep (flat g') (g.h.len - 1) p)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f + 1 ≤ 6 * g.h.n.toNat + g.xo
    ∧ Flat.get p (g.h.len - 1) = g.h.len - 1
    ∧ t.regs.rdx.toBitVec = c ∧ c ≤ g.h.len - 1 ∧ c ≠ 0
    ∧ t.regs.rax.toBitVec = (c - 1 : Word) ∧ Flat.get p (c - 1) ≠ c - 1
    ∧ Flat.misplacedBelow p (g.h.len - 1) (g.h.len - 1) = c - 1

-- The condition of `swapP_mu` for `pos`.
def Mis (n pos : Word) (p : Vector Word MAX_N) : Prop :=
  pos < n ∧ pos ≠ n - 1
    ∧ (Flat.get p (n - 1) = pos ∨ (Flat.get p (n - 1) = n - 1 ∧ Flat.get p pos ≠ pos))

-- `.LB.Emission.permute.22`: `exchange` of `pos` (`rax`).
def I22 (t : MachineData) : Prop :=
  ∃ g' L p f pos, DC S g F s ra g' L p t ∧ t.regs.rax.toBitVec = pos ∧ Mis g.h.len pos p
    ∧ Flat.permute (flat g) p0 = after f (g.h.len - 1) (Flat.exchange (flat g') (g.h.len - 1) p pos)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f + 1 ≤ 6 * g.h.n.toNat + g.xo

-- `.LB.Emission.permute.18`: equal slots: `swapDestinations` of `pos` and `top`.
def I18 (t : MachineData) : Prop :=
  ∃ g' L p f pos, DC S g F s ra g' L p t ∧ t.regs.rax.toBitVec = pos ∧ Mis g.h.len pos p
    ∧ Flat.permute (flat g) p0 = Flat.permuteLoop f
        (Flat.swapDestinations (flat g') pos (g.h.len - 1)) (g.h.len - 1)
        (swapP p (g.h.len - 1) pos)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f ≤ 6 * g.h.n.toNat + g.xo

-- `.LB.Emission.permute.19` and `.LB.Emission.permute.23`:
-- `positionOf[destinationOf[top]] = top` is left.
def I19 (t : MachineData) : Prop :=
  ∃ g' L p f pos, DC S g F s ra g' L p t ∧ t.regs.rax.toBitVec = pos ∧ Mis g.h.len pos p
    ∧ Flat.permute (flat g) p0 = Flat.permuteLoop f
        (posAt (flat g') (g.h.len - 1)) (g.h.len - 1) (swapP p (g.h.len - 1) pos)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f ≤ 6 * g.h.n.toNat + g.xo

-- `.LB.Emission.permute.20`: the swap of `permutation[pos]` and `permutation[top]` is left.
def I20 (t : MachineData) : Prop :=
  ∃ g' L p f pos, DC S g F s ra g' L p t ∧ t.regs.rax.toBitVec = pos ∧ Mis g.h.len pos p
    ∧ Flat.permute (flat g) p0 = Flat.permuteLoop f (flat g') (g.h.len - 1)
        (swapP p (g.h.len - 1) pos)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f ≤ 6 * g.h.n.toNat + g.xo

-- `.LB.Emission.permute.15`: done.
def I16 (t : MachineData) : Prop :=
  ∃ g' L, Fm S g' F s ra L t ∧ g'.Ok ∧ Keep g g' ∧ Flat.permute (flat g) p0 = (.done, flat g')

-- `.LB.Emission.permute.24`: the slot `pos` is too deep; `rdi = size - pos`.
def I24 (t : MachineData) : Prop :=
  ∃ g' L pos, Fm S g' F s ra L t ∧ g'.Ok ∧ Keep g g' ∧ t.regs.r13.toBitVec = S
    ∧ t.regs.rax.toBitVec = pos ∧ t.regs.rdx.toBitVec = (g'.h.len - pos : Word)
    ∧ ¬(g'.h.len - pos - 1 ≤ 16#64)
    ∧ Flat.permute (flat g) p0 = Flat.blockSwapUnreachable (flat g') pos

-- The invariant of each label.
def LInv : CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.permute then t = s.pushRa ra
    else if l = ".LB.Emission.permute.0" then I0 S g p0 F s ra t
    else if l = ".LB.Emission.permute.1" then I1 S g p0 F s ra t
    else if l = ".LB.Emission.permute.2" then I2 S g p0 F s ra t
    else if l = ".LB.Emission.permute.3" then I3 S g p0 F s ra t
    else if l = ".LB.Emission.permute.4" then I4 S g p0 F s ra t
    else if l = ".LB.Emission.permute.5" then I5 S g p0 F s ra t
    else if l = ".LB.Emission.permute.16" then I6 S g p0 F s ra t
    else if l = ".LB.Emission.permute.6" then I7 S g p0 F s ra t
    else if l = ".LB.Emission.permute.7" then I8 S g p0 F s ra t
    else if l = ".LB.Emission.permute.8" then I9 S g p0 F s ra t
    else if l = ".LB.Emission.permute.9" then I10 S g p0 F s ra t
    else if l = ".LB.Emission.permute.10" then I11 S g p0 F s ra t
    else if l = ".LB.Emission.permute.11" then I12 S g p0 F s ra t
    else if l = ".LB.Emission.permute.12" then I13 S g p0 F s ra t
    else if l = ".LB.Emission.permute.13" then I14 S g p0 F s ra t
    else if l = ".LB.Emission.permute.14" then I15 S g p0 F s ra t
    else if l = ".LB.Emission.permute.15" then I16 S g p0 F s ra t
    else if l = ".LB.Emission.permute.17" then I17 S g p0 F s ra t
    else if l = ".LB.Emission.permute.18" then I18 S g p0 F s ra t
    else if l = ".LB.Emission.permute.19" then I19 S g p0 F s ra t
    else if l = ".LB.Emission.permute.20" then I20 S g p0 F s ra t
    else if l = ".LB.Emission.permute.21" then I21 S g p0 F s ra t
    else if l = ".LB.Emission.permute.22" then I22 S g p0 F s ra t
    else if l = ".LB.Emission.permute.23" then I19 S g p0 F s ra t
    else if l = ".LB.Emission.permute.24" then I24 S g p0 F s ra t
    else if l = ".LB.Emission.permute.25" then I25 S g p0 F s ra t
    else False

end

/-! ## The variant -/

-- Phase C: the leader loop.
def wC (t : MachineData) : Nat := 2 ^ 23 + 2 ^ 22 * (1024 - t.regs.rbx.toBitVec.toNat)

-- Phase D: `mu` of the permutation in memory.
def mD (s : MachineData) (g : G) (t : MachineData) : Nat := mu (g.h.len - 1) (memVec s t)

def V (s : MachineData) (g : G) (l : Label) (t : MachineData) : Nat :=
  if l = Names.permute then 2 ^ 66
  else if l = ".LB.Emission.permute.0" then 2 ^ 33 + (t.regs.rdx.toBitVec - t.regs.rax.toBitVec).toNat
  else if l = ".LB.Emission.permute.11" then wC t + 2 ^ 22 - 1
  else if l = ".LB.Emission.permute.10" then wC t
  else if l = ".LB.Emission.permute.2" then wC t + 2051 * 1025 + (8192 - t.regs.rax.toBitVec.toNat) + 1
  else if l = ".LB.Emission.permute.1" then wC t + 2051 * 1025 + (8192 - t.regs.rax.toBitVec.toNat)
  else if l = ".LB.Emission.permute.3" then wC t + 2051 * 1025
  else if l = ".LB.Emission.permute.9" then wC t + 2051 * (1025 - t.regs.rcx.toBitVec.toNat)
  else if l = ".LB.Emission.permute.8" then wC t + 2051 * (1024 - t.regs.rcx.toBitVec.toNat)
  else if l = ".LB.Emission.permute.4" ∨ l = ".LB.Emission.permute.7" then
    wC t + 2051 * (1024 - t.regs.rcx.toBitVec.toNat) + 2 * (1024 - t.regs.rax.toBitVec.toNat) + 1
  else if l = ".LB.Emission.permute.6" then
    wC t + 2051 * (1024 - t.regs.rcx.toBitVec.toNat) + 2 * (1024 - t.regs.rax.toBitVec.toNat)
  else if l = ".LB.Emission.permute.5" then 1
  else if l = ".LB.Emission.permute.21" ∨ l = ".LB.Emission.permute.12" then 2048 * mD s g t + 1101
  else if l = ".LB.Emission.permute.13" then 2048 * mD s g t + 1100
  else if l = ".LB.Emission.permute.14" then 2048 * mD s g t + 1 + t.regs.rdx.toBitVec.toNat
  else if l = ".LB.Emission.permute.17" ∨ l = ".LB.Emission.permute.22" then 2048 * mD s g t + 2
  else if l = ".LB.Emission.permute.18" ∨ l = ".LB.Emission.permute.19"
    ∨ l = ".LB.Emission.permute.23" then 2048 * mD s g t + 1
  else if l = ".LB.Emission.permute.20" then 2048 * mD s g t
  else if l = ".LB.Emission.permute.15" ∨ l = ".LB.Emission.permute.24" then 1
  else 0

/-! ## The obligation of a block -/

-- The exception continuation of the body triple.
def E [Host] (S : Addr) (g : G) (p0 : Vector Word MAX_N) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => (a = ra ∧ Sep.Post S (permW s ∗ F) 1034 (fun g' t => permuteQ p0 g g' s t) s t
    ∧ Sep.mod.Agree s t) ∨
    (a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧
      Sep.Post S (permW s ∗ F) 1034 (fun g' t => permuteX p0 g g' s t) s t)

-- The obligation of `Program.WP.cfg` for the block `blk`.
def Obl [Host] [FunDecls] (S : Addr) (g : G) (p0 : Vector Word MAX_N) (F : MProp 64)
    (s : MachineData) (ra : Int64) (blk : Program.Block) : Prop :=
  ∀ t, LInv S g p0 F s ra blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      LInv S g p0 F s ra b u ∧ Program.Decreases (V s g) blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels finishAsm) (s.pushRa ra) I' (E S g p0 F s ra)) t

-- The labels used for the block proof of `finishAsm`.
def labels : List CfgLabel :=
  [.entry, .label "_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE",
    .label ".LB.Emission.permute.0", .label ".LB.Emission.permute.1",
    .label ".LB.Emission.permute.2", .label ".LB.Emission.permute.3",
    .label ".LB.Emission.permute.4", .label ".LB.Emission.permute.5",
    .label ".LB.Emission.permute.16", .label ".LB.Emission.permute.6",
    .label ".LB.Emission.permute.7", .label ".LB.Emission.permute.8",
    .label ".LB.Emission.permute.9", .label ".LB.Emission.permute.10",
    .label ".LB.Emission.permute.11", .label ".LB.Emission.permute.12",
    .label ".LB.Emission.permute.13", .label ".LB.Emission.permute.14",
    .label ".LB.Emission.permute.15", .label ".LB.Emission.permute.17",
    .label ".LB.Emission.permute.18", .label ".LB.Emission.permute.19",
    .label ".LB.Emission.permute.20", .label ".LB.Emission.permute.21",
    .label ".LB.Emission.permute.22", .label ".LB.Emission.permute.23",
    .label ".LB.Emission.permute.24", .label ".LB.Emission.permute.25"]

end Permute
end FlatShuffler.Unit
