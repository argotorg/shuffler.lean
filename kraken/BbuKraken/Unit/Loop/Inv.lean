import BbuKraken.Unit.Loop.Frame
import BbuKraken.Unit.Loop.Cont
import ProofKit.CfgBlock

/-!
# `buildBottomUp`: the invariant and the variant of each block

`st` is `flat g'` for the ghost `g'` of the state, `R` is `Flat.buildBottomUp (flat g)` for the
entry ghost `g`, and `T` is `r14` (the `targetOffset` of the C++).

* The model: `HInv st T x` is the invariant at the loop head (`FInv`, `T ≤ size`, and the trace
  bound `trace + 2 * pend + 2 * (n - T) ≤ 4 * n + x`). `Bud st T k x`: in the iteration at `T`,
  `k` more operations keep the trace bound at `T + 1`. The trace bound gives the preconditions of
  `generate`, `swapWith` and `permute`. In the unit proofs `x` is `g'.xo`.
* The label invariants `I…`: a body state `Bs` (`Mid`, `g'.Ok`, `Keep g g'`), the registers,
  and the continuation of the label: `Flat.kfin K = R` for the part `K` of `body` that the
  code at the label does (`Cont.lean`).
* The variant `V`: `H S T t = 8192 * (2048 * (1024 - T) + pend)` (`pend` in memory) and a
  constant for each label. A `generate` makes `pend` smaller; the end of an iteration makes `T`
  larger. The inner loops (`urgentToDup` with `rbx`, `candidate` with `rax`) use the constant.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Flat

-- `swapDestinations` up to `.10`: the swap of `dest` and the update of `pos` for `a`.
def swapHalf (st : St) (a b : Word) : St :=
  let dest := put (put st.dest a (get st.dest b)) b (get st.dest a)
  { st with dest, pos := if get dest a ≠ NONE then put st.pos (get dest a) a else st.pos }

-- The rest of `swapDestinations` from `.10`: the update of `pos` for `b`.
def swapRest (st : St) (b : Word) : St :=
  { st with pos := if get st.dest b ≠ NONE then put st.pos (get st.dest b) b else st.pos }

theorem swapDestinations_split (st : St) (a b : Word) :
    swapDestinations st a b = swapRest (swapHalf st a b) b := rfl

end Bbu.Flat

namespace Bbu.Unit
open Bbu.Sep
namespace Loop

/-! ## `Keep` (`Keep.refl` and `Keep.trans` are in `Unit/Generate.lean`, which this file does not
import) -/

theorem keep_refl (g : G) : Keep g g := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem keep_trans {g g1 g2 : G} (h1 : Keep g g1) (h2 : Keep g1 g2) : Keep g g2 :=
  ⟨h2.tgtp.trans h1.tgtp, h2.n.trans h1.n, h2.splp.trans h1.splp, h2.data.trans h1.data,
    h2.ops.trans h1.ops, h2.xs.trans h1.xs, h2.xo.trans h1.xo, h2.tgt.trans h1.tgt,
    h2.spl.trans h1.spl⟩

/-! ## Memory facts that more than one part uses -/

section
variable {S : Addr} {g : G} {F : MProp 64} {m : Mem 64}

theorem rd_pend (h : (View S g ∗ F).get m) : rd m (Fld.pendingGenerations S) = g.h.pend :=
  rd_of_eq h (by unfold View Em; ecancel)

theorem isSome_pend (h : (View S g ∗ F).get m) :
    (m.loadInt (Fld.pendingGenerations S) 8).isSome = true :=
  isSome_of_eq g.h.pend h (by unfold View Em; ecancel)

theorem store_blkOff (h : (View S g ∗ F).get m) (w : Word) :
    (View S { g with h := { g.h with blkOff := w } } ∗ F).get
      (m.storeInt (Fld.blocked_offset S) 8 w.toInt) :=
  swap_of_eq h (A := Wd (Fld.blocked_offset S) g.h.blkOff) (by unfold View Em; ecancel)
    (by unfold View Em; ecancel) (Wd.store · w)

theorem store_blkExc (h : (View S g ∗ F).get m) (w : Word) :
    (View S { g with h := { g.h with blkExc := w } } ∗ F).get
      (m.storeInt (Fld.blocked_excess S) 8 w.toInt) :=
  swap_of_eq h (A := Wd (Fld.blocked_excess S) g.h.blkExc) (by unfold View Em; ecancel)
    (by unfold View Em; ecancel) (Wd.store · w)

theorem Mid.rd_pend {s : MachineData} {ra : Int64} {x0 : Word} {x2 : Lc} {lo : List Word} {w u : Word}
    {t : MachineData} (h : Mid S g F s ra x0 x2 lo w u t) :
    rd t.dmem (Fld.pendingGenerations S) = g.h.pend :=
  Loop.rd_pend h.mem

end

/-! ## The invariants -/

-- The head facts of the iteration at `r14` before a change of the state: `r13 = n`,
-- `r15 = size`, `T < n`, `HInv`, and a pending generation.
def Hd (g' : G) (t : MachineData) : Prop :=
  t.regs.r13.toBitVec = g'.h.n ∧ t.regs.r15.toBitVec = g'.h.len
    ∧ t.regs.r14.toBitVec < g'.h.n ∧ Flat.HInv (flat g') t.regs.r14.toBitVec g'.xo ∧ g'.h.pend ≠ 0

section
variable (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

-- A body state with the ghost `g'` and the local `u` at `8(%rsp)`.
def Bs (g' : G) (u : Word) (t : MachineData) : Prop :=
  ∃ x0 x2 lo w, Mid S g' F s ra x0 x2 lo w u t ∧ g'.Ok ∧ Keep g g'

-- `.13`: the result.
def I13 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ loopQ g g' s t

-- `.28`, `.29`, `.30`: an assertion fails in the state `g'`.
def IAf (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Flat.buildBottomUp (flat g) = (.assertionFailed, flat g')

-- `.31`: the loop ends (`¬T < n`).
def I31 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.r13.toBitVec = g'.h.n
    ∧ Flat.buildBottomUp (flat g) = if (flat g').size ≠ (flat g').targetSize
        then (.assertionFailed, flat g') else (.done, flat g')

-- `.0`: no pending generation; `permute` if `size = n`. `rdx = 0` and `T < n`: the copy loop
-- at `.1` starts at 0 and does one step at least.
def I0 (t : MachineData) : Prop :=
  ∃ g' u T, Bs S g F s ra g' u t ∧ t.regs.r13.toBitVec = g'.h.n
    ∧ t.regs.r15.toBitVec = g'.h.len ∧ Flat.HInv (flat g') T g'.xo ∧ g'.h.pend = 0
    ∧ t.regs.rdx.toBitVec = 0#64 ∧ T < g'.h.n
    ∧ Flat.buildBottomUp (flat g) = if (flat g').size ≠ (flat g').targetSize
        then (.assertionFailed, flat g') else Flat.permuteMapping (flat g')

-- `.1`: the copy of `dest` to the local array `A` (the argument of `permute`) at `rdx < n`;
-- the entries below `rdx` are done.
def I1 (t : MachineData) : Prop :=
  ∃ g' u T x0 x2 lo w, Mid S g' F s ra x0 x2 lo w u t ∧ g'.Ok ∧ Keep g g'
    ∧ t.regs.r13.toBitVec = g'.h.n ∧ g'.h.len = g'.h.n ∧ t.regs.rdx.toBitVec < g'.h.n
    ∧ Flat.HInv (flat g') T g'.xo ∧ g'.h.pend = 0
    ∧ (∀ j (hj : j < MAX_N), j < t.regs.rdx.toBitVec.toNat →
        x2.A[j] = Flat.get g'.h.dest (BitVec.ofNat 64 j))
    ∧ Flat.buildBottomUp (flat g) = Flat.permuteMapping (flat g')

-- `.3`: `blockDupUnreachable` for the source copy `rax`; `rcx = size - rax`.
def I3 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.rcx.toBitVec = g'.h.len - t.regs.rax.toBitVec
    ∧ 15#64 < t.regs.rcx.toBitVec - 1#64
    ∧ Flat.buildBottomUp (flat g) = Flat.blockDupUnreachable (flat g') t.regs.rax.toBitVec

-- `.22`: `blockSwapUnreachable` for `p = rax`; `r15 = size - p`.
def I22 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.r15.toBitVec = g'.h.len - t.regs.rax.toBitVec
    ∧ 16#64 < t.regs.r15.toBitVec - 1#64
    ∧ Flat.buildBottomUp (flat g) = Flat.blockSwapUnreachable (flat g') t.regs.rax.toBitVec

-- `.23`: `blockSwapUnreachable` for `T = r14`; `rax = size - T`.
def I23 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.rax.toBitVec = g'.h.len - t.regs.r14.toBitVec
    ∧ 16#64 < t.regs.rax.toBitVec - 1#64
    ∧ Flat.buildBottomUp (flat g) = Flat.blockSwapUnreachable (flat g') t.regs.r14.toBitVec

-- `.26`: the loop head at `T = r14 < n`.
def I26 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.r13.toBitVec = g'.h.n
    ∧ t.regs.r14.toBitVec < g'.h.n ∧ Flat.HInv (flat g') t.regs.r14.toBitVec g'.xo
    ∧ Flat.loop (flat g') t.regs.r14.toBitVec = Flat.buildBottomUp (flat g)

-- `.25`: the end of an iteration; the next head is `r14 + 1`.
def I25 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Flat.HInv (flat g') (t.regs.r14.toBitVec + 1#64) g'.xo
    ∧ Flat.loop (flat g') (t.regs.r14.toBitVec + 1#64) = Flat.buildBottomUp (flat g)

-- `.24`: `p = T` after the swap of the destinations (`rax = r14`). `T < size` gives
-- `T + 1 ≤ 1024` for the variant at `.25`.
def I24 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.rax.toBitVec = t.regs.r14.toBitVec
    ∧ t.regs.r14.toBitVec < g'.h.len ∧ Flat.HInv (flat g') (t.regs.r14.toBitVec + 1#64) g'.xo
    ∧ Flat.loop (flat g') (t.regs.r14.toBitVec + 1#64) = Flat.buildBottomUp (flat g)

-- `.27`: the slot at `T` is not final.
def I27 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.r13.toBitVec = g'.h.n
    ∧ t.regs.r15.toBitVec = g'.h.len ∧ t.regs.r14.toBitVec < g'.h.n
    ∧ Flat.HInv (flat g') t.regs.r14.toBitVec g'.xo
    ∧ Flat.kfin (Flat.kPend (flat g') t.regs.r14.toBitVec) = Flat.buildBottomUp (flat g)

-- `.5`: the `urgentToDup` loop at the offset `rbx`, with `u` so far.
def I5 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t ∧ t.regs.rbx.toBitVec < g'.h.n
    ∧ Flat.kfin (Flat.kUE (flat g') t.regs.r14.toBitVec
        (Flat.urgentFrom (flat g') t.regs.r14.toBitVec t.regs.rbx.toBitVec u))
      = Flat.buildBottomUp (flat g)

-- `.4`: the `urgentToDup` loop after the offset `rbx`.
def I4 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t ∧ t.regs.rbx.toBitVec < g'.h.n
    ∧ Flat.kfin (Flat.kUE (flat g') t.regs.r14.toBitVec
        (Flat.urgentFrom (flat g') t.regs.r14.toBitVec (t.regs.rbx.toBitVec + 1#64) u))
      = Flat.buildBottomUp (flat g)

-- `.6`: the end of the `urgentToDup` loop.
def I6 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t
    ∧ Flat.kfin (Flat.kU (flat g') t.regs.r14.toBitVec u) = Flat.buildBottomUp (flat g)

-- `.7`: the generation at the top; `al = (u = NONE)`.
def I7 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t ∧ al t = (if u = Flat.NONE then 1#8 else 0#8)
    ∧ Flat.kfin (Flat.kU2 (flat g') t.regs.r14.toBitVec u) = Flat.buildBottomUp (flat g)

-- `.14`: the generation for `u`.
def I14 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t ∧ u ≠ Flat.NONE ∧ u ≠ t.regs.r14.toBitVec
    ∧ Flat.kfin (Flat.kU (flat g') t.regs.r14.toBitVec u) = Flat.buildBottomUp (flat g)

-- `.15`: the generation at the top `size`.
def I15 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t ∧ u = Flat.NONE
    ∧ t.regs.r14.toBitVec < g'.h.len ∧ g'.h.len < g'.h.n
    ∧ Flat.kfin (Flat.kU2 (flat g') t.regs.r14.toBitVec u) = Flat.buildBottomUp (flat g)

-- `.8`: `bound` or the generation for `T`.
def I8 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t
    ∧ Flat.kfin (Flat.kU3 (flat g') t.regs.r14.toBitVec) = Flat.buildBottomUp (flat g)

-- `.16`: the generation for `T`; `rbx = 8 * T`.
def I16 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t ∧ t.regs.rbx.toBitVec = 8#64 * t.regs.r14.toBitVec
    ∧ Flat.kfin (Flat.kGenT (flat g') t.regs.r14.toBitVec) = Flat.buildBottomUp (flat g)

-- `.18`: the `candidate` loop starts; the source is `b = rdx`, `rsi` is its slot word and
-- `rcx` is the address of the stack data.
def I18 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t ∧ t.regs.rbx.toBitVec = 8#64 * t.regs.r14.toBitVec
    ∧ t.regs.rdx.toBitVec < g'.h.len ∧ t.regs.rcx.toBitVec = g'.h.data
    ∧ StackSlot.ofWord t.regs.rsi.toBitVec = Flat.get (flat g').data t.regs.rdx.toBitVec
    ∧ Flat.kfin (Flat.kB (flat g') t.regs.r14.toBitVec t.regs.rdx.toBitVec
        (Flat.candidateFrom (flat g') (Flat.get (flat g').data t.regs.rdx.toBitVec)
          t.regs.rdx.toBitVec ((flat g').size - 1#64)))
      = Flat.buildBottomUp (flat g)

-- `.20`: the `candidate` loop at `c = rax`, with `b < c < size`.
def I20 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t ∧ t.regs.rbx.toBitVec = 8#64 * t.regs.r14.toBitVec
    ∧ t.regs.rdx.toBitVec < t.regs.rax.toBitVec ∧ t.regs.rax.toBitVec < g'.h.len
    ∧ t.regs.rcx.toBitVec = g'.h.data
    ∧ StackSlot.ofWord t.regs.rsi.toBitVec = Flat.get (flat g').data t.regs.rdx.toBitVec
    ∧ Flat.kfin (Flat.kB (flat g') t.regs.r14.toBitVec t.regs.rdx.toBitVec
        (Flat.candidateFrom (flat g') (Flat.get (flat g').data t.regs.rdx.toBitVec)
          t.regs.rdx.toBitVec t.regs.rax.toBitVec))
      = Flat.buildBottomUp (flat g)

-- `.19`: the `candidate` loop after `c = rax`, with `b < c < size`.
def I19 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t ∧ t.regs.rbx.toBitVec = 8#64 * t.regs.r14.toBitVec
    ∧ t.regs.rdx.toBitVec < t.regs.rax.toBitVec ∧ t.regs.rax.toBitVec < g'.h.len
    ∧ t.regs.rcx.toBitVec = g'.h.data
    ∧ StackSlot.ofWord t.regs.rsi.toBitVec = Flat.get (flat g').data t.regs.rdx.toBitVec
    ∧ Flat.kfin (Flat.kB (flat g') t.regs.r14.toBitVec t.regs.rdx.toBitVec
        (Flat.candidateFrom (flat g') (Flat.get (flat g').data t.regs.rdx.toBitVec)
          t.regs.rdx.toBitVec (t.regs.rax.toBitVec - 1#64)))
      = Flat.buildBottomUp (flat g)

-- `.21`: no candidate; the position is the source `b = rdx`.
def I21 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ Hd g' t ∧ t.regs.rbx.toBitVec = 8#64 * t.regs.r14.toBitVec
    ∧ t.regs.rdx.toBitVec < g'.h.len
    ∧ Flat.kfin (Flat.kB (flat g') t.regs.r14.toBitVec t.regs.rdx.toBitVec t.regs.rdx.toBitVec)
      = Flat.buildBottomUp (flat g)

-- `.9`: the swap of the destinations of `p = rax` and `b = rdx`.
def I9 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.r15.toBitVec = g'.h.len
    ∧ t.regs.rbx.toBitVec = 8#64 * t.regs.r14.toBitVec
    ∧ t.regs.rax.toBitVec < g'.h.len ∧ t.regs.rdx.toBitVec < g'.h.len
    ∧ Flat.FInv (flat g') ∧ Flat.Bud (flat g') t.regs.r14.toBitVec 2 g'.xo
    ∧ Flat.kfin (Flat.kBoundSw (Flat.swapDestinations (flat g') t.regs.rax.toBitVec
        t.regs.rdx.toBitVec) t.regs.r14.toBitVec t.regs.rax.toBitVec)
      = Flat.buildBottomUp (flat g)

-- `.10`: in the swap; the memory has `swapHalf st₀ p b`.
def I10 (t : MachineData) : Prop :=
  ∃ g' u st₀, Bs S g F s ra g' u t ∧ t.regs.r15.toBitVec = st₀.size
    ∧ t.regs.rbx.toBitVec = 8#64 * t.regs.r14.toBitVec ∧ t.regs.rsi = t.regs.rax
    ∧ t.regs.rax.toBitVec < st₀.size ∧ t.regs.rdx.toBitVec < st₀.size
    ∧ Flat.FInv st₀ ∧ Flat.Bud st₀ t.regs.r14.toBitVec 2 g'.xo
    ∧ flat g' = Flat.swapHalf st₀ t.regs.rax.toBitVec t.regs.rdx.toBitVec
    ∧ Flat.kfin (Flat.kBoundSw (Flat.swapDestinations st₀ t.regs.rax.toBitVec
        t.regs.rdx.toBitVec) t.regs.r14.toBitVec t.regs.rax.toBitVec)
      = Flat.buildBottomUp (flat g)

-- `.11`: after the swap of the destinations; `p = rax = rsi`.
def I11 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.r15.toBitVec = g'.h.len
    ∧ t.regs.rbx.toBitVec = 8#64 * t.regs.r14.toBitVec ∧ t.regs.rsi = t.regs.rax
    ∧ t.regs.rax.toBitVec < g'.h.len
    ∧ Flat.FInv (flat g') ∧ Flat.Bud (flat g') t.regs.r14.toBitVec 2 g'.xo
    ∧ Flat.kfin (Flat.kBoundSw (flat g') t.regs.r14.toBitVec t.regs.rax.toBitVec)
      = Flat.buildBottomUp (flat g)

-- `.12`: `placeTop` at `T`.
def I12 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.rbx.toBitVec = 8#64 * t.regs.r14.toBitVec
    ∧ Flat.FInv (flat g') ∧ Flat.Bud (flat g') t.regs.r14.toBitVec 1 g'.xo
    ∧ Flat.kfin (Flat.placeTop (flat g') t.regs.r14.toBitVec) = Flat.buildBottomUp (flat g)

-- `.17`: the end of `placeTop` at `T < size`; `rax = size`.
def I17 (t : MachineData) : Prop :=
  ∃ g' u, Bs S g F s ra g' u t ∧ t.regs.rax.toBitVec = g'.h.len
    ∧ t.regs.r14.toBitVec < g'.h.len
    ∧ Flat.FInv (flat g') ∧ Flat.Bud (flat g') t.regs.r14.toBitVec 1 g'.xo
    ∧ Flat.kfin (Flat.kTail (flat g') t.regs.r14.toBitVec) = Flat.buildBottomUp (flat g)

-- The invariant of each label (the order of `labels`). `.2` (`dest[rdx] = NONE`) is not
-- reachable: `FInv` gives `dest[i] < n` below `size`.
def LInv : CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.buildBottomUp then t = s.pushRa ra
    else if l = ".LB.Emission.buildBottomUp.0" then I0 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.1" then I1 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.2" then False
    else if l = ".LB.Emission.buildBottomUp.3" then I3 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.4" then I4 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.5" then I5 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.6" then I6 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.7" then I7 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.8" then I8 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.9" then I9 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.10" then I10 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.11" then I11 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.12" then I12 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.13" then I13 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.14" then I14 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.15" then I15 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.16" then I16 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.17" then I17 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.18" then I18 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.19" then I19 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.20" then I20 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.21" then I21 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.22" then I22 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.23" then I23 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.24" then I24 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.25" then I25 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.26" then I26 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.27" then I27 S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.28" then IAf S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.29" then IAf S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.30" then IAf S g F s ra t
    else if l = ".LB.Emission.buildBottomUp.31" then I31 S g F s ra t
    else False

end

/-! ## The variant -/

-- The weight of the iteration at `T`: `T` goes up, or `T` stays and `pend` (in memory) goes
-- down. The constants of the labels are below 8192.
def H (S : Addr) (T : Word) (t : MachineData) : Nat :=
  8192 * (2048 * (1024 - T.toNat) + (rd t.dmem (Fld.pendingGenerations S)).toNat)

def V (S : Addr) (l : Label) (t : MachineData) : Nat :=
  if l = Names.buildBottomUp then 2 ^ 36
  else if l = ".LB.Emission.buildBottomUp.26" ∨ l = ".LB.Emission.buildBottomUp.27" then H S t.regs.r14.toBitVec t + 4200
  else if l = ".LB.Emission.buildBottomUp.25" then H S (t.regs.r14.toBitVec + 1#64) t + 4200
  else if l = ".LB.Emission.buildBottomUp.5" then
    H S t.regs.r14.toBitVec t + 2103 + 2 * (1024 - t.regs.rbx.toBitVec.toNat)
  else if l = ".LB.Emission.buildBottomUp.4" then
    H S t.regs.r14.toBitVec t + 2102 + 2 * (1024 - t.regs.rbx.toBitVec.toNat)
  else if l = ".LB.Emission.buildBottomUp.6" ∨ l = ".LB.Emission.buildBottomUp.7" ∨ l = ".LB.Emission.buildBottomUp.14" ∨ l = ".LB.Emission.buildBottomUp.15" then
    H S t.regs.r14.toBitVec t + 2102
  else if l = ".LB.Emission.buildBottomUp.8" then H S t.regs.r14.toBitVec t + 2101
  else if l = ".LB.Emission.buildBottomUp.18" then H S t.regs.r14.toBitVec t + 2100
  else if l = ".LB.Emission.buildBottomUp.20" then H S t.regs.r14.toBitVec t + 12 + 2 * t.regs.rax.toBitVec.toNat
  else if l = ".LB.Emission.buildBottomUp.19" then H S t.regs.r14.toBitVec t + 11 + 2 * t.regs.rax.toBitVec.toNat
  else if l = ".LB.Emission.buildBottomUp.21" then H S t.regs.r14.toBitVec t + 11
  else if l = ".LB.Emission.buildBottomUp.9" ∨ l = ".LB.Emission.buildBottomUp.10" ∨ l = ".LB.Emission.buildBottomUp.11" ∨ l = ".LB.Emission.buildBottomUp.12" ∨ l = ".LB.Emission.buildBottomUp.17"
      ∨ l = ".LB.Emission.buildBottomUp.24" ∨ l = ".LB.Emission.buildBottomUp.16" then H S t.regs.r14.toBitVec t + 10
  else if l = ".LB.Emission.buildBottomUp.0" then 1026
  else if l = ".LB.Emission.buildBottomUp.1" then 1 + (1024 - t.regs.rdx.toBitVec.toNat)
  else if l = ".LB.Emission.buildBottomUp.13" then 0
  else 1
/-- The variant goal of `cfg_goto`: `V` at the two literal labels, then `omega` if it can. -/
macro "loop_dec" : tactic => `(tactic| (
  simp only [V, Names.buildBottomUp, String.reduceEq, ↓reduceIte, or_self, or_false, false_or,
    true_or, or_true, Nat.lt_irrefl, true_and, and_true]
  try omega))

/-! ## The obligation of a block -/

-- The exception continuation of the body triple.
def E (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ Sep.Post S F 2068 (fun g' t => loopQ g g' s t) s t ∧ Sep.mod.Agree s t

-- The obligation of `Program.WP.cfg` for the block `blk`.
def Obl [Host] [FunDecls] (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, LInv S g F s ra blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      LInv S g F s ra b u ∧ Program.Decreases (V S) blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels loopAsm) (s.pushRa ra) I' (E S g F s ra)) t

-- The labels of `loopAsm`, in the order of the blocks.
def labels : List CfgLabel :=
  [.entry, .label "_ZN12_GLOBAL__N_18Emission13buildBottomUpEv",
    .label ".LB.Emission.buildBottomUp.0",
    .label ".LB.Emission.buildBottomUp.1",
    .label ".LB.Emission.buildBottomUp.2",
    .label ".LB.Emission.buildBottomUp.3",
    .label ".LB.Emission.buildBottomUp.4",
    .label ".LB.Emission.buildBottomUp.5",
    .label ".LB.Emission.buildBottomUp.6",
    .label ".LB.Emission.buildBottomUp.7",
    .label ".LB.Emission.buildBottomUp.8",
    .label ".LB.Emission.buildBottomUp.9",
    .label ".LB.Emission.buildBottomUp.10",
    .label ".LB.Emission.buildBottomUp.11",
    .label ".LB.Emission.buildBottomUp.12",
    .label ".LB.Emission.buildBottomUp.13",
    .label ".LB.Emission.buildBottomUp.14",
    .label ".LB.Emission.buildBottomUp.15",
    .label ".LB.Emission.buildBottomUp.16",
    .label ".LB.Emission.buildBottomUp.17",
    .label ".LB.Emission.buildBottomUp.18",
    .label ".LB.Emission.buildBottomUp.19",
    .label ".LB.Emission.buildBottomUp.20",
    .label ".LB.Emission.buildBottomUp.21",
    .label ".LB.Emission.buildBottomUp.22",
    .label ".LB.Emission.buildBottomUp.23",
    .label ".LB.Emission.buildBottomUp.24",
    .label ".LB.Emission.buildBottomUp.25",
    .label ".LB.Emission.buildBottomUp.26",
    .label ".LB.Emission.buildBottomUp.27",
    .label ".LB.Emission.buildBottomUp.28",
    .label ".LB.Emission.buildBottomUp.29",
    .label ".LB.Emission.buildBottomUp.30",
    .label ".LB.Emission.buildBottomUp.31"]

end Loop
end Bbu.Unit
