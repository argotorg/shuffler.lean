import BbuKraken.Unit.Permute.Frame
import BbuKraken.Unit.Permute.Cfg
import BbuKraken.Unit.PermuteModel
import BbuKraken.Unit.PermuteSpecs
import BbuKraken.Unit.Permute.Util

/-!
# `permute`: the invariant and the variant of each block

`n` is the size `g.h.len` of the entry ghost `g`, `top` is `n - 1` and `st` is `flat g`.
The invariant of a block is a predicate `I…` on the state at its label (`LInv`).

* Phase A (`.LB.Emission.permute.0`, `.LB.Emission.permute.2`): `permutation[i] = destinationOf[i]` below `rax`.
* Phase B (`.LB.Emission.permute.3`): `desiredBy[i] = NONE` below the index of `rax`.
* Phase C (`.LB.Emission.permute.14` to `.LB.Emission.permute.8`): the loops of `regroup`. The model vectors `p`, `dB` and `pc`
  are existential; the locals `L.P` and `L.D` agree with them below `n` (`AgB`). `RG st X`: the
  `regroup` of `permute` gives `X`.
* Phase D (`.LB.Emission.permute.15` to `.LB.Emission.permute.26`): the loop of `permute`, with the fuel `f` of `permuteLoop`.

The variant `V` decreases on each back edge. Phase D uses `mu` of the permutation in the stack
(`memVec`): each iteration of the loop makes it smaller (`swapP_mu`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

/-! ## The model vectors -/

-- `v` and `w` agree below `k`.
def AgB (k : Word) (v w : Vector Word MAX_N) : Prop := ∀ i < k, Flat.get v i = Flat.get w i

-- The elements below `n` are below `n`.
def LtB (n : Word) (p : Vector Word MAX_N) : Prop := ∀ i < n, Flat.get p i < n

-- The `regroup` of `permute` gives `X`.
def RG (st : Flat.St) (X : Option (Vector Word MAX_N)) : Prop :=
  ∃ p0, Flat.readDestinations st 0 Flat.initial = some p0
    ∧ Flat.regroup st 0 p0 (Flat.clearDesired st 0 Flat.initial) = X

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

-- The array `permutation` in the stack.
def memVec (s t : MachineData) : Vector Word MAX_N :=
  Vector.ofFn fun i => rd t.dmem (base s + 8208#64 + BitVec.ofNat 64 (8 * i.val))

/-! ## The invariants -/

section
variable (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

-- `.LB.Emission.permute.1`: the result.
def I54 (t : MachineData) : Prop :=
  ∃ g' L, Fm S g' F s ra L t ∧ g'.Ok ∧ permuteQ g g' s t

-- `.LB.Emission.permute.0`: `permutation[i] = destinationOf[i]` below `rax`.
def I57 (t : MachineData) : Prop :=
  ∃ L, Fm S g F s ra L t ∧ t.regs.r15.toBitVec = S ∧ t.regs.rbx.toBitVec = g.h.len
    ∧ t.regs.rax.toBitVec < g.h.len ∧ AgB t.regs.rax.toBitVec L.P g.h.dest

-- `.LB.Emission.permute.2`: and `rdx = destinationOf[rax]`.
def I56 (t : MachineData) : Prop :=
  ∃ L, Fm S g F s ra L t ∧ t.regs.r15.toBitVec = S ∧ t.regs.rbx.toBitVec = g.h.len
    ∧ t.regs.rax.toBitVec < g.h.len ∧ AgB t.regs.rax.toBitVec L.P g.h.dest
    ∧ t.regs.rdx.toBitVec = Flat.get g.h.dest t.regs.rax.toBitVec

-- `.LB.Emission.permute.3`: `desiredBy[i] = NONE` below `k`; `rax` is the address of `desiredBy[k]`.
def I58 (t : MachineData) : Prop :=
  ∃ L, ∃ k : Nat, Fm S g F s ra L t ∧ t.regs.r15.toBitVec = S
    ∧ t.regs.rbx.toBitVec = g.h.len ∧ k < g.h.len.toNat
    ∧ t.regs.rax.toBitVec = base s + 16#64 + BitVec.ofNat 64 (8 * k)
    ∧ t.regs.rdx.toBitVec = base s + 16#64 + BitVec.ofNat 64 (8 * g.h.len.toNat)
    ∧ (∀ i : Word, i.toNat < k → Flat.get L.D i = Flat.NONE) ∧ AgB g.h.len L.P g.h.dest

-- Phase C: the leader `l` in `rbp`.
structure CC (L : Lc) (l : Word) (t : MachineData) : Prop where
  fm : Fm S g F s ra L t
  lt : l < g.h.len
  bp : t.regs.rbp.toBitVec = l
  c0 : L.c0 = l + 1
  c1 : L.c1 = (l + 1) * 8#64
  r12 : t.regs.r12.toBitVec = base s + 16#64
  r15 : t.regs.r15.toBitVec = S
  bx : t.regs.rbx.toBitVec = g.h.len

-- Phase C in a group: `r13` is the stack and `r14` is the slot of the leader.
structure GC (L : Lc) (l : Word) (t : MachineData) : Prop where
  cc : CC S g F s ra L l t
  r13 : t.regs.r13.toBitVec = g.h.data
  r14 : StackSlot.ofWord t.regs.r14.toBitVec = Flat.get (flat g).data l

-- `.LB.Emission.permute.14`: `regroup` from the leader `l`.
def I71 (t : MachineData) : Prop :=
  ∃ L l p dB, CC S g F s ra L l t ∧ RG (flat g) (Flat.regroup (flat g) l p dB)
    ∧ AgB g.h.len L.P p ∧ AgB g.h.len L.D dB ∧ LtB g.h.len p

-- `.LB.Emission.permute.13`: `regroup` from the leader `l + 1`.
def I60 (t : MachineData) : Prop :=
  ∃ L l p dB, CC S g F s ra L l t ∧ RG (flat g) (Flat.regroup (flat g) (l + 1) p dB)
    ∧ AgB g.h.len L.P p ∧ AgB g.h.len L.D dB ∧ LtB g.h.len p

-- `.LB.Emission.permute.5`: `markDesired` from `j`; `rax` is `8 * j`.
def I62 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ p dB j, GC S g F s ra L l t ∧ j ≤ l
    ∧ t.regs.rax.toBitVec = j * 8#64
    ∧ RG (flat g) (pg (flat g) l hl (Flat.get (flat g).data l)
        (Flat.markDesired (flat g) l hl (Flat.get (flat g).data l) p j dB) 0 0 p)
    ∧ AgB g.h.len L.P p ∧ AgB g.h.len L.D dB ∧ LtB g.h.len p

-- `.LB.Emission.permute.4`: `markDesired` from `j + 1`; `rax` is `8 * j`.
def I61 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ p dB j, GC S g F s ra L l t ∧ j ≤ l
    ∧ t.regs.rax.toBitVec = j * 8#64
    ∧ RG (flat g) (pg (flat g) l hl (Flat.get (flat g).data l)
        (Flat.markDesired (flat g) l hl (Flat.get (flat g).data l) p (j + 1) dB) 0 0 p)
    ∧ AgB g.h.len L.P p ∧ AgB g.h.len L.D dB ∧ LtB g.h.len p

-- `.LB.Emission.permute.6`: `placeGroup` from the start.
def I95 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ p dB, GC S g F s ra L l t
    ∧ RG (flat g) (pg (flat g) l hl (Flat.get (flat g).data l) dB 0 0 p)
    ∧ AgB g.h.len L.P p ∧ AgB g.h.len L.D dB ∧ LtB g.h.len p

-- `.LB.Emission.permute.12`: `placeGroup` from `pos` (`rcx`) with `vacant` in `rax`.
def I70 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ dB pos vac pc, GC S g F s ra L l t ∧ pos ≤ l
    ∧ vac ≤ g.h.len ∧ t.regs.rcx.toBitVec = pos ∧ t.regs.rax.toBitVec = vac
    ∧ RG (flat g) (pg (flat g) l hl (Flat.get (flat g).data l) dB pos vac pc)
    ∧ AgB g.h.len L.P pc ∧ AgB g.h.len L.D dB ∧ LtB g.h.len pc

-- `.LB.Emission.permute.11`: `placeGroup` from `pos + 1`.
def I63 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ dB pos vac pc, GC S g F s ra L l t ∧ pos ≤ l
    ∧ vac ≤ g.h.len ∧ t.regs.rcx.toBitVec = pos ∧ t.regs.rax.toBitVec = vac
    ∧ RG (flat g) (pg (flat g) l hl (Flat.get (flat g).data l) dB (pos + 1) vac pc)
    ∧ AgB g.h.len L.P pc ∧ AgB g.h.len L.D dB ∧ LtB g.h.len pc

-- `.LB.Emission.permute.7`: the `vacant` loop from `x` (`rax`) for the slot `pos`.
def I64 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ dB pos x pc, GC S g F s ra L l t ∧ pos ≤ l
    ∧ x ≤ g.h.len ∧ t.regs.rcx.toBitVec = pos ∧ t.regs.rax.toBitVec = x
    ∧ RG (flat g) (nv (flat g) l hl (Flat.get (flat g).data l) dB pos x pc)
    ∧ AgB g.h.len L.P pc ∧ AgB g.h.len L.D dB ∧ LtB g.h.len pc

-- `.LB.Emission.permute.10`: and `x < n`.
def I68 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ dB pos x pc, GC S g F s ra L l t ∧ pos ≤ l
    ∧ x < g.h.len ∧ t.regs.rcx.toBitVec = pos ∧ t.regs.rax.toBitVec = x
    ∧ RG (flat g) (nv (flat g) l hl (Flat.get (flat g).data l) dB pos x pc)
    ∧ AgB g.h.len L.P pc ∧ AgB g.h.len L.D dB ∧ LtB g.h.len pc

-- `.LB.Emission.permute.9`: `x` is not vacant; the loop goes on from `x + 1`.
def I66 (t : MachineData) : Prop :=
  ∃ L l, ∃ hl : l < (flat g).size, ∃ dB pos x pc, GC S g F s ra L l t ∧ pos ≤ l
    ∧ x < g.h.len ∧ t.regs.rcx.toBitVec = pos ∧ t.regs.rax.toBitVec = x
    ∧ RG (flat g) (nv (flat g) l hl (Flat.get (flat g).data l) dB pos (x + 1) pc)
    ∧ AgB g.h.len L.P pc ∧ AgB g.h.len L.D dB ∧ LtB g.h.len pc

-- `.LB.Emission.permute.8`: `regroup` fails.
def I65 (t : MachineData) : Prop :=
  ∃ L, Fm S g F s ra L t ∧ Flat.permute (flat g) = (.assertionFailed, flat g)

-- `.LB.Emission.permute.15`: `regroup` gives `p`.
def I96 (t : MachineData) : Prop :=
  ∃ L p, Fm S g F s ra L t ∧ t.regs.r15.toBitVec = S ∧ t.regs.rbx.toBitVec = g.h.len
    ∧ 0 < g.h.len
    ∧ RG (flat g) (some p) ∧ AgB g.h.len L.P p

-- Phase D: the struct `g'`, the locals `L` and the permutation `p`.
structure DC (g' : G) (L : Lc) (p : Vector Word MAX_N) (t : MachineData) : Prop where
  fm : Fm S g' F s ra L t
  ok : g'.Ok
  keep : Keep g g'
  len : g'.h.len = g.h.len
  pos : 0 < g.h.len
  dl : LtB g.h.len g'.h.dest
  r15 : t.regs.r15.toBitVec = S
  bx : t.regs.rbx.toBitVec = g.h.len
  cx : t.regs.rcx.toBitVec = (g.h.len - 1 : Word)
  si : t.regs.rsi.toBitVec = base s + 8208#64
  agP : AgB g.h.len L.P p
  bij : Bij g.h.len p

-- `.LB.Emission.permute.23`: the head of the loop, with the fuel `f`.
def I84 (t : MachineData) : Prop :=
  ∃ g' L p f, DC S g F s ra g' L p t
    ∧ Flat.permute (flat g) = Flat.permuteLoop f (flat g') (g.h.len - 1) p
    ∧ mu (g.h.len - 1) p ≤ f ∧ g'.h.nops.toNat + f ≤ 6 * g.h.n.toNat

-- `.LB.Emission.permute.16`: `permutation[top] = top`.
def I86 (t : MachineData) : Prop :=
  ∃ g' L p f, DC S g F s ra g' L p t
    ∧ Flat.permute (flat g) = after f (g.h.len - 1) (Flat.permuteStep (flat g') (g.h.len - 1) p)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f + 1 ≤ 6 * g.h.n.toNat
    ∧ Flat.get p (g.h.len - 1) = g.h.len - 1

-- `.LB.Emission.permute.17`: the `candidate` loop at `c` (`rdx`).
def I72 (t : MachineData) : Prop :=
  ∃ g' L p f c, DC S g F s ra g' L p t
    ∧ Flat.permute (flat g) = after f (g.h.len - 1) (Flat.permuteStep (flat g') (g.h.len - 1) p)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f + 1 ≤ 6 * g.h.n.toNat
    ∧ Flat.get p (g.h.len - 1) = g.h.len - 1
    ∧ t.regs.rdx.toBitVec = c ∧ c ≤ g.h.len - 1
    ∧ Flat.misplacedBelow p (g.h.len - 1) (g.h.len - 1)
      = Flat.misplacedBelow p (g.h.len - 1) c

-- `.LB.Emission.permute.19`: `pos = c - 1` is misplaced.
def I74 (t : MachineData) : Prop :=
  ∃ g' L p f c, DC S g F s ra g' L p t
    ∧ Flat.permute (flat g) = after f (g.h.len - 1) (Flat.permuteStep (flat g') (g.h.len - 1) p)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f + 1 ≤ 6 * g.h.n.toNat
    ∧ Flat.get p (g.h.len - 1) = g.h.len - 1
    ∧ t.regs.rdx.toBitVec = c ∧ c ≤ g.h.len - 1 ∧ c ≠ 0
    ∧ t.regs.rax.toBitVec = (c - 1 : Word) ∧ Flat.get p (c - 1) ≠ c - 1
    ∧ Flat.misplacedBelow p (g.h.len - 1) (g.h.len - 1) = c - 1

-- The condition of `swapP_mu` for `pos`.
def Mis (n pos : Word) (p : Vector Word MAX_N) : Prop :=
  pos < n ∧ pos ≠ n - 1
    ∧ (Flat.get p (n - 1) = pos ∨ (Flat.get p (n - 1) = n - 1 ∧ Flat.get p pos ≠ pos))

-- `.LB.Emission.permute.24`: `exchange` of `pos` (`rax`).
def I73 (t : MachineData) : Prop :=
  ∃ g' L p f pos, DC S g F s ra g' L p t ∧ t.regs.rax.toBitVec = pos ∧ Mis g.h.len pos p
    ∧ Flat.permute (flat g) = after f (g.h.len - 1) (Flat.exchange (flat g') (g.h.len - 1) p pos)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f + 1 ≤ 6 * g.h.n.toNat

-- `.LB.Emission.permute.20`: equal slots: `swapDestinations` of `pos` and `top`.
def I98 (t : MachineData) : Prop :=
  ∃ g' L p f pos, DC S g F s ra g' L p t ∧ t.regs.rax.toBitVec = pos ∧ Mis g.h.len pos p
    ∧ Flat.permute (flat g) = Flat.permuteLoop f
        (Flat.swapDestinations (flat g') pos (g.h.len - 1)) (g.h.len - 1)
        (swapP p (g.h.len - 1) pos)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f ≤ 6 * g.h.n.toNat

-- `.LB.Emission.permute.21` and `.LB.Emission.permute.25`: `positionOf[destinationOf[top]] = top` is left.
def I78 (t : MachineData) : Prop :=
  ∃ g' L p f pos, DC S g F s ra g' L p t ∧ t.regs.rax.toBitVec = pos ∧ Mis g.h.len pos p
    ∧ Flat.permute (flat g) = Flat.permuteLoop f
        (posAt (flat g') (g.h.len - 1)) (g.h.len - 1) (swapP p (g.h.len - 1) pos)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f ≤ 6 * g.h.n.toNat

-- `.LB.Emission.permute.22`: the swap of `permutation[pos]` and `permutation[top]` is left.
def I80 (t : MachineData) : Prop :=
  ∃ g' L p f pos, DC S g F s ra g' L p t ∧ t.regs.rax.toBitVec = pos ∧ Mis g.h.len pos p
    ∧ Flat.permute (flat g) = Flat.permuteLoop f (flat g') (g.h.len - 1)
        (swapP p (g.h.len - 1) pos)
    ∧ mu (g.h.len - 1) p ≤ f + 1 ∧ g'.h.nops.toNat + f ≤ 6 * g.h.n.toNat

-- `.LB.Emission.permute.18`: done.
def I97 (t : MachineData) : Prop :=
  ∃ g' L, Fm S g' F s ra L t ∧ g'.Ok ∧ Keep g g' ∧ Flat.permute (flat g) = (.done, flat g')

-- `.LB.Emission.permute.26`: the slot `pos` is too deep; `rdi = size - pos`.
def I99 (t : MachineData) : Prop :=
  ∃ g' L pos, Fm S g' F s ra L t ∧ g'.Ok ∧ Keep g g' ∧ t.regs.r15.toBitVec = S
    ∧ t.regs.rax.toBitVec = pos ∧ t.regs.rdi.toBitVec = (g'.h.len - pos : Word)
    ∧ ¬(g'.h.len - pos - 1 ≤ 16#64)
    ∧ Flat.permute (flat g) = Flat.blockSwapUnreachable (flat g') pos

-- The invariant of each label.
def LInv : CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.permute then t = s.pushRa ra
    else if l = ".LB.Emission.permute.0" then I57 S g F s ra t
    else if l = ".LB.Emission.permute.1" then I54 S g F s ra t
    else if l = ".LB.Emission.permute.2" then I56 S g F s ra t
    else if l = ".LB.Emission.permute.3" then I58 S g F s ra t
    else if l = ".LB.Emission.permute.4" then I61 S g F s ra t
    else if l = ".LB.Emission.permute.5" then I62 S g F s ra t
    else if l = ".LB.Emission.permute.6" then I95 S g F s ra t
    else if l = ".LB.Emission.permute.7" then I64 S g F s ra t
    else if l = ".LB.Emission.permute.8" then I65 S g F s ra t
    else if l = ".LB.Emission.permute.9" then I66 S g F s ra t
    else if l = ".LB.Emission.permute.10" then I68 S g F s ra t
    else if l = ".LB.Emission.permute.11" then I63 S g F s ra t
    else if l = ".LB.Emission.permute.12" then I70 S g F s ra t
    else if l = ".LB.Emission.permute.13" then I60 S g F s ra t
    else if l = ".LB.Emission.permute.14" then I71 S g F s ra t
    else if l = ".LB.Emission.permute.15" then I96 S g F s ra t
    else if l = ".LB.Emission.permute.16" then I86 S g F s ra t
    else if l = ".LB.Emission.permute.17" then I72 S g F s ra t
    else if l = ".LB.Emission.permute.18" then I97 S g F s ra t
    else if l = ".LB.Emission.permute.19" then I74 S g F s ra t
    else if l = ".LB.Emission.permute.20" then I98 S g F s ra t
    else if l = ".LB.Emission.permute.21" then I78 S g F s ra t
    else if l = ".LB.Emission.permute.22" then I80 S g F s ra t
    else if l = ".LB.Emission.permute.23" then I84 S g F s ra t
    else if l = ".LB.Emission.permute.24" then I73 S g F s ra t
    else if l = ".LB.Emission.permute.25" then I78 S g F s ra t
    else if l = ".LB.Emission.permute.26" then I99 S g F s ra t
    else False

end

/-! ## The variant -/

-- Phase C: the leader loop.
def wC (t : MachineData) : Nat := 2 ^ 23 + 2 ^ 22 * (1024 - t.regs.rbp.toBitVec.toNat)

-- Phase D: `mu` of the permutation in the stack.
def mD (s : MachineData) (g : G) (t : MachineData) : Nat := mu (g.h.len - 1) (memVec s t)

def V (s : MachineData) (g : G) (l : Label) (t : MachineData) : Nat :=
  if l = Names.permute then 2 ^ 35
  else if l = ".LB.Emission.permute.0" then 2 ^ 34 + 2 * (1024 - t.regs.rax.toBitVec.toNat) + 1
  else if l = ".LB.Emission.permute.2" then 2 ^ 34 + 2 * (1024 - t.regs.rax.toBitVec.toNat)
  else if l = ".LB.Emission.permute.3" then 2 ^ 33 + (t.regs.rdx.toBitVec - t.regs.rax.toBitVec).toNat
  else if l = ".LB.Emission.permute.14" then wC t + 2 ^ 22 - 1
  else if l = ".LB.Emission.permute.13" then wC t
  else if l = ".LB.Emission.permute.5" then wC t + 2051 * 1025 + (8192 - t.regs.rax.toBitVec.toNat) + 1
  else if l = ".LB.Emission.permute.4" then wC t + 2051 * 1025 + (8192 - t.regs.rax.toBitVec.toNat)
  else if l = ".LB.Emission.permute.6" then wC t + 2051 * 1025
  else if l = ".LB.Emission.permute.12" then wC t + 2051 * (1025 - t.regs.rcx.toBitVec.toNat)
  else if l = ".LB.Emission.permute.11" then wC t + 2051 * (1024 - t.regs.rcx.toBitVec.toNat)
  else if l = ".LB.Emission.permute.7" ∨ l = ".LB.Emission.permute.10" then
    wC t + 2051 * (1024 - t.regs.rcx.toBitVec.toNat) + 2 * (1024 - t.regs.rax.toBitVec.toNat) + 1
  else if l = ".LB.Emission.permute.9" then
    wC t + 2051 * (1024 - t.regs.rcx.toBitVec.toNat) + 2 * (1024 - t.regs.rax.toBitVec.toNat)
  else if l = ".LB.Emission.permute.8" then 1
  else if l = ".LB.Emission.permute.23" ∨ l = ".LB.Emission.permute.15" then 2048 * mD s g t + 1101
  else if l = ".LB.Emission.permute.16" then 2048 * mD s g t + 1100
  else if l = ".LB.Emission.permute.17" then 2048 * mD s g t + 1 + t.regs.rdx.toBitVec.toNat
  else if l = ".LB.Emission.permute.19" ∨ l = ".LB.Emission.permute.24" then 2048 * mD s g t + 2
  else if l = ".LB.Emission.permute.20" ∨ l = ".LB.Emission.permute.21" ∨ l = ".LB.Emission.permute.25" then 2048 * mD s g t + 1
  else if l = ".LB.Emission.permute.22" then 2048 * mD s g t
  else if l = ".LB.Emission.permute.18" ∨ l = ".LB.Emission.permute.26" then 1
  else 0

/-! ## The obligation of a block -/

-- The exception continuation of the body triple.
def E (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ Sep.Post S F 2058 (fun g' t => permuteQ g g' s t) s t ∧ Sep.mod.Agree s t

-- The obligation of `Program.WP.cfg` for the block `blk`.
def Obl [Host] [FunDecls] (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, LInv S g F s ra blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      LInv S g F s ra b u ∧ Program.Decreases (V s g) blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels finishAsm) (s.pushRa ra) I' (E S g F s ra)) t

-- The labels of `finishAsm`, in the order of the blocks.
def labels : List CfgLabel :=
  [.entry, .label "_ZN12_GLOBAL__N_18Emission7permuteEv", .label ".LB.Emission.permute.0", .label ".LB.Emission.permute.1",
    .label ".LB.Emission.permute.2", .label ".LB.Emission.permute.3", .label ".LB.Emission.permute.4", .label ".LB.Emission.permute.5", .label ".LB.Emission.permute.6",
    .label ".LB.Emission.permute.7", .label ".LB.Emission.permute.8", .label ".LB.Emission.permute.9", .label ".LB.Emission.permute.10", .label ".LB.Emission.permute.11",
    .label ".LB.Emission.permute.12", .label ".LB.Emission.permute.13", .label ".LB.Emission.permute.14", .label ".LB.Emission.permute.15", .label ".LB.Emission.permute.16",
    .label ".LB.Emission.permute.17", .label ".LB.Emission.permute.18", .label ".LB.Emission.permute.19", .label ".LB.Emission.permute.20", .label ".LB.Emission.permute.21",
    .label ".LB.Emission.permute.22", .label ".LB.Emission.permute.23", .label ".LB.Emission.permute.24", .label ".LB.Emission.permute.25", .label ".LB.Emission.permute.26"]

end Permute
end Bbu.Unit
