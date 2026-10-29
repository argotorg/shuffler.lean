import BbuKraken.Kit

/-!
The definitions of the proof of `loop_body` (`c/bbu/<Names.buildBottomUp>.S`): the model
steps between the cut labels, the invariant at each label, the variant, and the
obligation of one block of the cfg as a standalone `Prop`.

`buildBottomUp` pushes `r15`, `r14`, `r13`, `r12`, `rbp` and `rbx`, then makes 24
bytes of locals. So `rsp` is `rsp s - 80` in the body, the callees are at
`rsp s - 80`, and the local `urgentToDup` is the word at `rsp s - 72`. The body
keeps the struct in `rbp`, `n` in `r13`, `targetOffset` in `r14` and
`len` in `r15` (at the loop head). The `urgentToDup` scan keeps its offset in
`rbx` and the target word in `r12`.

Each label of the loop keeps `Ctx`: the state at the loop head, at `targetOffset`,
gives the result of the whole loop. `step e st0 targetOffset` is then split into the parts
that the code does between two labels.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

/-! ## The parts of `step` -/

-- The branch of `step` on the slot bound for `targetOffset`, after `takeBound`.
def afterTake (targetOffset : Nat) (r : St × Bool) : M (St × Next) :=
  if r.2 then .ok (r.1, .next (targetOffset + 1)) else placeTop r.1 targetOffset

-- The branch of `step` after `generate` of the slot for `targetOffset`.
def afterGen (targetOffset : Nat) (st : St) : M (St × Next) :=
  if targetOffset < st.len ∧ st.dest targetOffset = targetOffset then
    .ok (st, .next (targetOffset + 1))
  else placeTop st targetOffset

-- The branch of `step` on `positionOf st targetOffset`.
def bound (e : Env) (st : St) (targetOffset : Nat) : M (St × Next) :=
  if (positionOf st targetOffset).isSome then
    (takeBound st targetOffset).bind (afterTake targetOffset)
  else (generate e st targetOffset).bind (afterGen targetOffset)

-- The branch of `step` on the result `urgentToDup` of `urgent`.
def afterUrgent (e : Env) (st : St) (targetOffset urgentToDup : Nat) : M (St × Next) :=
  if urgentToDup ≠ e.n ∧ urgentToDup ≠ targetOffset ∧
      st.len < targetOffset + MAX_SWAP_DEPTH then
    (generate e st urgentToDup).map (·, .next targetOffset)
  else if urgentToDup = e.n ∧ targetOffset < st.len ∧ st.len < e.n ∧
      positionOf st st.len = none ∧ st.len < targetOffset + MAX_SWAP_DEPTH then
    (generate e st st.len).map (·, .next targetOffset)
  else bound e st targetOffset

-- `takeBound st targetOffset` and `afterTake targetOffset` for
-- `positionOf st targetOffset = some sourceForTargetOffset` and
-- `targetOffset ≤ sourceForTargetOffset`, when the slot at `pos` goes to
-- `sourceForTargetOffset`.
def afterPos (st : St) (targetOffset sourceForTargetOffset pos : Nat) : M (St × Next) :=
  if st.val pos ≠ st.val sourceForTargetOffset then .error .assertion
  else
  let st := swapDestinations st pos sourceForTargetOffset
  if pos = targetOffset then .ok (st, .next (targetOffset + 1))
  else if pos ≠ st.len - 1 then
    let depth := st.len - 1 - pos
    if MAX_SWAP_DEPTH < depth then .error (.blocked pos (depth - MAX_SWAP_DEPTH))
    else (swapWith st pos).bind (placeTop · targetOffset)
  else placeTop st targetOffset

-- The search of `movableCopy st sourceForTargetOffset` from `candidate` down to
-- `sourceForTargetOffset + 1`.
def movFrom (st : St) (sourceForTargetOffset candidate : Nat) : Option Nat :=
  ((List.range (candidate + 1)).reverse.take (candidate - sourceForTargetOffset)).find?
    (fun copy => st.val copy == st.val sourceForTargetOffset && st.dest copy != copy)

-- The word of `urgentToDup`: `n` (none) is `-1`.
def encU (n urgentToDup : Nat) : Word :=
  if urgentToDup = n then -1#64 else BitVec.ofNat 64 urgentToDup

/-! ## Invariants -/

-- The registers that `buildBottomUp` saves, in the order of the pushes.
abbrev regs : List Reg64 := [.r15, .r14, .r13, .r12, .rbp, .rbx]

abbrev Fm := Kit.Fm loopF regs

section
variable (s : MachineData) (ra : Int64)

-- The result of the loop at the call.
abbrev R0 : M St := loop (env s) (st s) 0

-- The local `urgentToDup` in `t`.
abbrev urgentToDupWord (t : MachineData) : Word := rd t.dmem (rsp s - 72#64)

-- The invariant of `loop` at `targetOffset`, and `targetOffset ≤ len`.
def InvL (e : Env) (st0 : St) (targetOffset : Nat) : Prop :=
  Inv e st0 targetOffset ∧ targetOffset ≤ st0.len

-- The loop head at `targetOffset < n` with the state `st0` gives the result of the loop.
def Ctx (targetOffset : Nat) (st0 : St) : Prop :=
  targetOffset < (env s).n ∧ InvL (env s) st0 targetOffset
    ∧ loop (env s) st0 targetOffset = R0 s

-- An iteration at `targetOffset` from a loop head gives `r`.
def Iter (targetOffset : Nat) (r : M (St × Next)) : Prop :=
  ∃ st0, Ctx s targetOffset st0 ∧ step (env s) st0 targetOffset = r

-- The memory and the fixed registers after the prologue.
structure Base (t : MachineData) : Prop where
  fm : Fm s ra t.dmem
  rsp : t.regs.rsp.toBitVec = rsp s - 80#64
  rbp : t.regs.rbp.toBitVec = rdi s

-- `.LB85`: the loop head at `targetOffset`.
def At85 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.r13.toBitVec = BitVec.ofNat 64 (env s).n
    ∧ ∃ targetOffset, t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
      ∧ Ctx s targetOffset (st' s t)

-- `.LB64`: the end of an iteration; `targetOffset'` is the next offset.
def At64 (t : MachineData) : Prop :=
  Base s ra t ∧ ∃ targetOffset', t.regs.r14.toBitVec + 1#64 = BitVec.ofNat 64 targetOffset'
    ∧ InvL (env s) (st' s t) targetOffset' ∧ loop (env s) (st' s t) targetOffset' = R0 s

-- `.LB92`: as `.LB64`, with the offset in `rsi`.
def At92 (t : MachineData) : Prop :=
  Base s ra t ∧ ∃ targetOffset', t.regs.rsi.toBitVec + 1#64 = BitVec.ofNat 64 targetOffset'
    ∧ InvL (env s) (st' s t) targetOffset' ∧ loop (env s) (st' s t) targetOffset' = R0 s

-- `.LB106`: as `.LB64`, with the offset in `r14`.
def At106 (t : MachineData) : Prop :=
  Base s ra t ∧ ∃ targetOffset', t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset'
    ∧ InvL (env s) (st' s t) targetOffset' ∧ loop (env s) (st' s t) targetOffset' = R0 s

-- `.LB63`: the slot at `targetOffset` is not final.
def At63 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.r13.toBitVec = BitVec.ofNat 64 (env s).n
    ∧ t.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len
    ∧ ∃ targetOffset, t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
      ∧ Ctx s targetOffset (st' s t)
      ∧ ¬ (targetOffset < (st' s t).len ∧ (st' s t).dest targetOffset = targetOffset)

-- `.LB65`: no slot is pending.
def At65 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.r13.toBitVec = BitVec.ofNat 64 (env s).n
    ∧ t.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len
    ∧ ∃ targetOffset, Ctx s targetOffset (st' s t)
      ∧ ¬ (targetOffset < (st' s t).len ∧ (st' s t).dest targetOffset = targetOffset)
      ∧ (st' s t).pendingGenerations = 0

-- `.LB62`: the loop is at its end.
def At62 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.r13.toBitVec = BitVec.ofNat 64 (env s).n
    ∧ R0 s = if (st' s t).len = (env s).n then .ok (st' s t) else .error .assertion

-- The labels that set `-2`: an assertion fails.
def AtErr (t : MachineData) : Prop :=
  Base s ra t ∧ R0 s = .error .assertion

-- `.LB103`: a copy is out of reach for a dup.
def At103 (t : MachineData) : Prop :=
  Base s ra t ∧ ∃ pos excess, t.regs.rax.toBitVec = BitVec.ofNat 64 pos
    ∧ t.regs.rcx.toBitVec - 16#64 = BitVec.ofNat 64 excess ∧ R0 s = .error (.blocked pos excess)

-- `.LB108`: the slot at `rsi` is out of reach for a swap.
def At108 (t : MachineData) : Prop :=
  Base s ra t ∧ ∃ pos excess, t.regs.rsi.toBitVec = BitVec.ofNat 64 pos
    ∧ t.regs.r15.toBitVec - 17#64 = BitVec.ofNat 64 excess ∧ R0 s = .error (.blocked pos excess)

-- `.LB109`: the slot at `r14` is out of reach for a swap.
def At109 (t : MachineData) : Prop :=
  Base s ra t ∧ ∃ pos excess, t.regs.r14.toBitVec = BitVec.ofNat 64 pos
    ∧ t.regs.rax.toBitVec - 17#64 = BitVec.ofNat 64 excess ∧ R0 s = .error (.blocked pos excess)

-- `.LB61`: the result is in `rax` and memory.
def At61 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ t.regs.rsp.toBitVec = rsp s - 80#64 ∧ loopR s t

-- The registers of the `urgentToDup` scan at the slot for `offset`, with the
-- result `urgentToDup` so far.
def Scan (targetOffset offset urgentToDup : Nat) (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.r13.toBitVec = BitVec.ofNat 64 (env s).n
    ∧ t.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len
    ∧ t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
    ∧ t.regs.rbx.toBitVec = BitVec.ofNat 64 offset
    ∧ urgentToDupWord s t = encU (env s).n urgentToDup
    ∧ urgentToDup ≤ (env s).n ∧ offset < (env s).n
    ∧ Ctx s targetOffset (st' s t) ∧ (st' s t).pendingGenerations ≠ 0

-- `.LB66`: the scan at `offset`.
def At66 (t : MachineData) : Prop :=
  ∃ targetOffset offset urgentToDup, Scan s ra targetOffset offset urgentToDup t
    ∧ step (env s) (st' s t) targetOffset
      = (urgentFrom (env s) (st' s t) targetOffset offset urgentToDup).bind
        (afterUrgent (env s) (st' s t) targetOffset)

-- `.LB73`: `offset` is done.
def At73 (t : MachineData) : Prop :=
  ∃ targetOffset offset urgentToDup, Scan s ra targetOffset offset urgentToDup t
    ∧ step (env s) (st' s t) targetOffset
      = (urgentFrom (env s) (st' s t) targetOffset (offset + 1) urgentToDup).bind
        (afterUrgent (env s) (st' s t) targetOffset)

-- `.LB102`: the scan gives `urgentToDup`.
def At102 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.r13.toBitVec = BitVec.ofNat 64 (env s).n
    ∧ t.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len
    ∧ ∃ targetOffset urgentToDup, t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
      ∧ urgentToDupWord s t = encU (env s).n urgentToDup
      ∧ urgentToDup ≤ (env s).n ∧ Ctx s targetOffset (st' s t) ∧ (st' s t).pendingGenerations ≠ 0
      ∧ step (env s) (st' s t) targetOffset
        = afterUrgent (env s) (st' s t) targetOffset urgentToDup

-- `.LB67`: as `.LB102`, and `urgentToDup` is none or `targetOffset`.
def At67 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.r13.toBitVec = BitVec.ofNat 64 (env s).n
    ∧ t.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len
    ∧ ∃ targetOffset urgentToDup, t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
      ∧ urgentToDupWord s t = encU (env s).n urgentToDup
      ∧ urgentToDup ≤ (env s).n ∧ (urgentToDup = (env s).n ∨ urgentToDup = targetOffset)
      ∧ Ctx s targetOffset (st' s t) ∧ (st' s t).pendingGenerations ≠ 0
      ∧ step (env s) (st' s t) targetOffset
        = afterUrgent (env s) (st' s t) targetOffset urgentToDup

-- `.LB104`: generate the urgent slot `urgentToDup`.
def At104 (t : MachineData) : Prop :=
  Base s ra t ∧ ∃ targetOffset urgentToDup, t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
    ∧ urgentToDupWord s t = BitVec.ofNat 64 urgentToDup ∧ urgentToDup < (env s).n
    ∧ Ctx s targetOffset (st' s t) ∧ (st' s t).pendingGenerations ≠ 0
    ∧ step (env s) (st' s t) targetOffset
      = (generate (env s) (st' s t) urgentToDup).map (·, .next targetOffset)

-- `.LB74`: the slot bound for `targetOffset`.
def At74 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len
    ∧ ∃ targetOffset, t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
      ∧ Ctx s targetOffset (st' s t) ∧ (st' s t).pendingGenerations ≠ 0
      ∧ step (env s) (st' s t) targetOffset = bound (env s) (st' s t) targetOffset

-- `.LB75`: no slot is bound for `targetOffset`.
def At75 (t : MachineData) : Prop :=
  Base s ra t ∧ ∃ targetOffset, t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
    ∧ Ctx s targetOffset (st' s t) ∧ (st' s t).pendingGenerations ≠ 0
    ∧ step (env s) (st' s t) targetOffset
      = (generate (env s) (st' s t) targetOffset).bind (afterGen targetOffset)

-- The registers of the search of a copy of the slot `sourceForTargetOffset`:
-- `rax` is its position, `rcx` points to `m_data` and `r8` is the offset of its
-- word in `m_dest`.
def Copy (targetOffset sourceForTargetOffset : Nat) (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len
    ∧ t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
    ∧ t.regs.rax.toBitVec = BitVec.ofNat 64 sourceForTargetOffset
    ∧ t.regs.rcx.toBitVec = dataOf t.dmem (rdi s)
    ∧ t.regs.r8.toBitVec = BitVec.ofNat 64 (8 * sourceForTargetOffset)
    ∧ sourceForTargetOffset < (st' s t).len ∧ Ctx s targetOffset (st' s t)

-- The word of the slot `sourceForTargetOffset` in `rdi`.
abbrev SrcWord (sourceForTargetOffset : Nat) (t : MachineData) : Prop :=
  t.regs.rdi.toBitVec = rd t.dmem (wordAt (dataOf t.dmem (rdi s)) sourceForTargetOffset)

-- `.LB105`: the slot `sourceForTargetOffset` is bound for `targetOffset` and has
-- not the value of the slot at `targetOffset`.
def At105 (t : MachineData) : Prop :=
  ∃ targetOffset sourceForTargetOffset, Copy s ra targetOffset sourceForTargetOffset t
    ∧ SrcWord s sourceForTargetOffset t
    ∧ step (env s) (st' s t) targetOffset = afterPos (st' s t) targetOffset sourceForTargetOffset
      ((movableCopy (st' s t) sourceForTargetOffset).getD sourceForTargetOffset)

-- `.LB80`: the search at `candidate`.
def At80 (t : MachineData) : Prop :=
  ∃ targetOffset sourceForTargetOffset candidate,
    Copy s ra targetOffset sourceForTargetOffset t ∧ SrcWord s sourceForTargetOffset t
    ∧ t.regs.rsi.toBitVec = BitVec.ofNat 64 candidate
    ∧ sourceForTargetOffset < candidate ∧ candidate < (st' s t).len
    ∧ step (env s) (st' s t) targetOffset = afterPos (st' s t) targetOffset sourceForTargetOffset
      ((movFrom (st' s t) sourceForTargetOffset candidate).getD sourceForTargetOffset)

-- `.LB78`: `candidate` is not a movable copy.
def At78 (t : MachineData) : Prop :=
  ∃ targetOffset sourceForTargetOffset candidate,
    Copy s ra targetOffset sourceForTargetOffset t ∧ SrcWord s sourceForTargetOffset t
    ∧ t.regs.rsi.toBitVec = BitVec.ofNat 64 candidate
    ∧ sourceForTargetOffset < candidate ∧ candidate < (st' s t).len
    ∧ step (env s) (st' s t) targetOffset = afterPos (st' s t) targetOffset sourceForTargetOffset
      ((movFrom (st' s t) sourceForTargetOffset (candidate - 1)).getD sourceForTargetOffset)

-- `.LB90` and `.LB107`: no copy is movable, so the slot at
-- `sourceForTargetOffset` stays.
def At90 (t : MachineData) : Prop :=
  ∃ targetOffset sourceForTargetOffset, Copy s ra targetOffset sourceForTargetOffset t
    ∧ step (env s) (st' s t) targetOffset
      = afterPos (st' s t) targetOffset sourceForTargetOffset sourceForTargetOffset

-- `.LB77`: the slot at `pos` goes to `sourceForTargetOffset`.
def At77 (t : MachineData) : Prop :=
  ∃ targetOffset sourceForTargetOffset pos, Copy s ra targetOffset sourceForTargetOffset t
    ∧ t.regs.rsi.toBitVec = BitVec.ofNat 64 pos ∧ pos < (st' s t).len
    ∧ step (env s) (st' s t) targetOffset
      = afterPos (st' s t) targetOffset sourceForTargetOffset pos

-- `.LB81`: swap the top into `targetOffset`.
def At81 (t : MachineData) : Prop :=
  Base s ra t ∧ ∃ targetOffset, t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
    ∧ Iter s targetOffset (placeTop (st' s t) targetOffset) ∧ (st' s t).trace.length < cap s
    ∧ Pos (env s).n (st' s t)

-- `.LB83`: as `.LB81`, and the slot at `targetOffset` is not final.
def At83 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.rax.toBitVec = BitVec.ofNat 64 (st' s t).len
    ∧ ∃ targetOffset, t.regs.r14.toBitVec = BitVec.ofNat 64 targetOffset
      ∧ Iter s targetOffset (placeTop (st' s t) targetOffset) ∧ (st' s t).trace.length < cap s
      ∧ targetOffset < (st' s t).len ∧ (st' s t).dest targetOffset ≠ targetOffset
      ∧ Pos (env s).n (st' s t)

-- The invariant at each label.
def LInv : CfgLabel → MachineData → Prop
  | .entry, t | .label "buildBottomUp", t => t = s.pushRa ra
  | .label ".LB65", t => At65 s ra t
  | .label ".LB103", t => At103 s ra t
  | .label ".LB73", t => At73 s ra t
  | .label ".LB66", t => At66 s ra t
  | .label ".LB102", t => At102 s ra t
  | .label ".LB74", t => At74 s ra t
  | .label ".LB64", t => At64 s ra t
  | .label ".LB85", t => At85 s ra t
  | .label ".LB63", t => At63 s ra t
  | .label ".LB67", t => At67 s ra t
  | .label ".LB104", t => At104 s ra t
  | .label ".LB61", t => At61 s ra t
  | .label ".LB106", t => At106 s ra t
  | .label ".LB105", t => At105 s ra t
  | .label ".LB78", t => At78 s ra t
  | .label ".LB80", t => At80 s ra t
  | .label ".LB107", t | .label ".LB90", t => At90 s ra t
  | .label ".LB77", t => At77 s ra t
  | .label ".LB81", t => At81 s ra t
  | .label ".LB83", t => At83 s ra t
  | .label ".LB108", t => At108 s ra t
  | .label ".LB75", t => At75 s ra t
  | .label ".LB109", t => At109 s ra t
  | .label ".LB92", t => At92 s ra t
  | .label ".LB62", t => At62 s ra t
  | .label ".LB87", t | .label ".LB89", t | .label ".LB93", t | .label ".LB94", t
  | .label ".LB95", t | .label ".LB96", t => AtErr s ra t
  | _, _ => False

/-! ## Variant -/

-- The part of the variant of the loop at `targetOffset`: `targetOffset` goes up,
-- or `pending` goes down.
def outer (t : MachineData) (targetOffset : Nat) : Nat :=
  ((env s).n - targetOffset) * 2048 + (st' s t).pendingGenerations

-- The weight of `outer`: it is larger than each value in one iteration.
def W : Nat := 8192

-- The variant: each jump goes to a label with a smaller value.
def V : Label → MachineData → Nat
  | "buildBottomUp", _ => 2 ^ 40
  | ".LB64", t => W * outer s t (t.regs.r14.toBitVec + 1#64).toNat + 8100
  | ".LB92", t => W * outer s t (t.regs.rsi.toBitVec + 1#64).toNat + 8150
  | ".LB106", t => W * outer s t t.regs.r14.toBitVec.toNat + 8150
  | ".LB85", t => W * outer s t t.regs.r14.toBitVec.toNat + 8000
  | ".LB63", t => W * outer s t t.regs.r14.toBitVec.toNat + 7999
  | ".LB66", t => W * outer s t t.regs.r14.toBitVec.toNat + 3002
      + 3 * ((env s).n - t.regs.rbx.toBitVec.toNat)
  | ".LB73", t => W * outer s t t.regs.r14.toBitVec.toNat + 3000
      + 3 * ((env s).n - t.regs.rbx.toBitVec.toNat)
  | ".LB102", t => W * outer s t t.regs.r14.toBitVec.toNat + 2900
  | ".LB104", t => W * outer s t t.regs.r14.toBitVec.toNat + 2850
  | ".LB67", t => W * outer s t t.regs.r14.toBitVec.toNat + 2800
  | ".LB74", t => W * outer s t t.regs.r14.toBitVec.toNat + 2700
  | ".LB75", t => W * outer s t t.regs.r14.toBitVec.toNat + 2600
  | ".LB105", t => W * outer s t t.regs.r14.toBitVec.toNat + 2500
  | ".LB80", t => W * outer s t t.regs.r14.toBitVec.toNat + 201 + 2 * t.regs.rsi.toBitVec.toNat
  | ".LB78", t => W * outer s t t.regs.r14.toBitVec.toNat + 200 + 2 * t.regs.rsi.toBitVec.toNat
  | ".LB107", t | ".LB90", t => W * outer s t t.regs.r14.toBitVec.toNat + 150
  | ".LB77", t => W * outer s t t.regs.r14.toBitVec.toNat + 140
  | ".LB81", t => W * outer s t t.regs.r14.toBitVec.toNat + 130
  | ".LB83", t => W * outer s t t.regs.r14.toBitVec.toNat + 120
  | ".LB65", _ => 4
  | ".LB62", _ => 3
  | ".LB103", _ | ".LB108", _ | ".LB109", _ | ".LB87", _ | ".LB89", _ | ".LB93", _
  | ".LB94", _ | ".LB95", _ | ".LB96", _ => 1
  | _, _ => 0

/-! ## The obligation of one block -/

variable [Host] [FunDecls]

-- The postcondition of `Body` for the call `s`.
abbrev Ex : Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ Post loopF loopR s t ∧ (mod loopF s).Agree s t

/-- The obligation of `Program.WP.cfg` for the block `blk`. -/
def Obl (blk : Program.Block) : Prop :=
  ∀ t, LInv s ra blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      LInv s ra b u ∧ Program.Decreases (V s) blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels loopAsm) (s.pushRa ra) I' (Ex s ra)) t

/-- The obligation of the block with the label `l`. -/
def OblAt (l : CfgLabel) : Prop := loopAsm.ForallBlocks fun blk => blk.label = l → Obl s ra blk

end


/-! ## Blocks by label -/

theorem forallBlocksFrom_cases {P : Program.Block → Prop} {L : List CfgLabel} :
    ∀ {bs : List (Label × Program)} {b : CfgLabel} {j : Nat} {body : Program},
      Program.forallBlocksFrom (fun blk => blk.label ∈ L) b j body bs →
      (∀ l ∈ L, Program.forallBlocksFrom (fun blk => blk.label = l → P blk) b j body bs) →
      Program.forallBlocksFrom P b j body bs
  | [], _, _, _, hc, h => h _ hc rfl
  | (_, _) :: _, _, _, _, hc, h =>
    ⟨(h _ hc.1).1 rfl, forallBlocksFrom_cases hc.2 fun l hl => (h l hl).2⟩

-- A block obligation from one obligation for each label in `L`, if each block has a
-- label in `L`.
theorem forallBlocks_cases {p : Program} {P : Program.Block → Prop} (L : List CfgLabel)
    (hc : p.ForallBlocks fun blk => blk.label ∈ L)
    (h : ∀ l ∈ L, p.ForallBlocks fun blk => blk.label = l → P blk) : p.ForallBlocks P :=
  forallBlocksFrom_cases hc h

/-- Reduce `OblAt s ra l` to the obligation of the block with the label `l`:
`∀ t, LInv s ra l t → WP.wp body ..`. -/
macro "loop_case" : tactic =>
  `(tactic|
    (unfold OblAt
     cfg_view as hview
     have hlabels : Program.labels _ = _ :=
       (Program.labels_view _).trans (congrArg (fun v => List.map (·.1) v.2) hview)
     simp only [List.map_cons, List.map_nil] at hlabels
     rw [Program.ForallBlocks, hview]
     clear hview
     simp only [Obl, Program.forallBlocksFrom, hlabels, CfgLabel.label.injEq, reduceCtorEq,
       String.reduceEq, Nat.reduceAdd, false_implies, true_implies, and_true, true_and]
     clear hlabels))

/-- A jump to a label of the cfg: the goals are the stack, the invariant and the variant. -/
macro "loop_goto" : tactic =>
  `(tactic|
    (apply Program.Intercept.intro_label
     · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
       apply List.getElem?_cons_zero
     refine Or.inl ⟨?_, ?_, ?_⟩))

end Loop

end Bbu
