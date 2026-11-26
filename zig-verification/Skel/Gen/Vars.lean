import Skel.Gen.Types

/-! The variables of the generated model, from the blocks (`docs/one-way-lift-g1-plan-20261118.md`, section 2.3 and rule 3
of section 2.4; task G1-06).

An input field is a register that some block reads at its start, when some path from the entry reaches that block with
no write of the register on the path. `rsp` is in no field. A state field is a register that some block writes, including
the `rax` result of a call. `mem` is
true when some block stores through a register other than `rsp`; a store to the stack is not a store of the memory. A call
sets the caller-saved registers, so a path through a call carries no entry value of them (a decision of G1-06: the plan
does not state the effect of a call). -/

namespace Skel.Gen

/-- The fields in the order of `Reg64`, without `rsp`. -/
private def fieldRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The registers that a call sets: the caller-saved registers of the System V ABI. -/
private def callerSaved : List Reg64 := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

mutual
/-- The registers that a value reads. A value is in terms of the block start, so each register it names is read
before any write of the block. -/
private def valRegs : Val → List Reg64
  | .reg r => [r]
  | .lit _ | .load _ | .retAddr _ => []
  | .add a b | .sub a b | .mul a b => valRegs a ++ valRegs b
  | .shr a _ | .zext32 a | .not a | .neg a | .shl a _ | .extract _ _ a _ | .zext _ a | .sext _ a => valRegs a
  | .and a b | .or a b | .xor a b | .replaceLow _ a b => valRegs a ++ valRegs b
  | .setcc c => condRegs c
  | .ite c a b => condRegs c ++ valRegs a ++ valRegs b

/-- The registers that a condition reads. -/
private def condRegs : Cond → List Reg64
  | .eq a b | .ule a b | .ult a b | .slt a b | .slt32 a b => valRegs a ++ valRegs b
  | .not c => condRegs c
  | .iff p q => condRegs p ++ condRegs q
  | .flag _ => []
end

private def accessRegs : Access → List Reg64
  | .load _ addr _ => valRegs addr
  | .store _ addr _ v => valRegs addr ++ valRegs v

/-- A store through an address that does not use `rsp`: a store of the memory of the state. -/
private def isHeapStore : Access → Bool
  | .load .. => false
  | .store _ addr _ _ => !(valRegs addr).contains .rsp

private def exitsOf : Term → List Exit
  | .exit e => [e]
  | .branch _ y n => [y, n]

/-- `rax` when the block returns and does not write `rax`: the value of the model's `ret` is then `rax` of the block start
(N13: `toyMark` returns with no write of `rax`). -/
private def retRegs (b : Block) : List Reg64 :=
  match b.term with
  | .exit .ret => if b.regs.any (·.1 == .rax) then [] else [.rax]
  | _ => []

/-- The registers that a block writes, without `rsp`. -/
def writesOf (b : Block) : List Reg64 := (b.regs.map (·.1)).filter (· != .rsp)

/-- The registers that the exits of a block read: the argument registers of the callee of a call exit, in the order of
the callee's `inputs`. A call passes the registers as they are at the end of the block. A register that the block writes
is read through its written value (`regs`), so it is not read at the start; an unknown callee has no argument. -/
private def exitRegs (callees : List Callee) (b : Block) : List Reg64 :=
  (exitsOf b.term).flatMap fun
    | .call n _ => ((callees.find? (·.name == n)).map (·.inputs)).getD [] |>.filter (!(b.regs.map (·.1)).contains ·)
    | .goto _ | .ret | .trap => []

private def termRegs : Term → List Reg64
  | .exit _ => []
  | .branch c _ _ => condRegs c

/-- The registers that a block reads at its start: in its accesses, written values, branch and kept flag conditions,
`rax` of a return that does not write it, and the argument registers of its call exits. -/
def readsOf (callees : List Callee) (b : Block) : List Reg64 :=
  b.accesses.flatMap accessRegs ++ b.regs.flatMap (fun p => valRegs p.2) ++ termRegs b.term ++
    b.flags.flatMap (fun p => condRegs p.2) ++ retRegs b ++ exitRegs callees b

/-- The block that an exit goes to, with the registers that the exit sets before it. A return and a trap go nowhere. -/
private def edgeOf : Exit → Option (Nat × List Reg64)
  | .goto t => some (t, [])
  | .call _ c => some (c, callerSaved)
  | .ret | .trap => none

/-- The start sets of the blocks, by offset: the registers that reach the start of the block with no write. The entry,
at offset 0, starts with every field; the other blocks start with none. -/
private def startSets (bs : List Block) : List (Nat × List Reg64) :=
  bs.map fun b => (b.offset, if b.offset == 0 then fieldRegs else [])

/-- One pass over the blocks. Each block passes its start set on to the targets of its exits, without the registers
that it writes and the registers that the exit sets. -/
private def pass (bs : List Block) (sets : List (Nat × List Reg64)) : List (Nat × List Reg64) :=
  bs.foldl (init := sets) fun acc b =>
    let out := (List.lookup b.offset acc).getD []
    (exitsOf b.term).foldl (init := acc) fun acc e =>
      match edgeOf e with
      | none => acc
      | some (t, set) =>
        let flow := out.filter fun r => !((writesOf b ++ set).contains r)
        -- a set has no repeat: with repeats a loop doubles a set on each pass (N11: `closestCopy` of the pilot)
        acc.map fun (o, s) => if o == t then (o, s ++ flow.filter (!s.contains ·)) else (o, s)

/-- The start sets after enough passes. A simple path from the entry has at most `bs.length - 1` edges, and each pass
extends every path by one edge, so `bs.length` passes reach every simple path. -/
private def startSetsAfterPasses (bs : List Block) : List (Nat × List Reg64) :=
  (List.range bs.length).foldl (fun sets _ => pass bs sets) (startSets bs)

/-- The variables of the blocks: the input fields, the state fields, and whether the state has memory: a store through a
register, or a call of a callee with memory (PIL-CALL). -/
def vars (bs : List Block) (callees : List Callee := []) : Vars :=
  let sets := startSetsAfterPasses bs
  let unsetAt (b : Block) : List Reg64 := (List.lookup b.offset sets).getD []
  { inputs := fieldRegs.filter fun r => bs.any fun b => (readsOf callees b).contains r && (unsetAt b).contains r
    state := fieldRegs.filter fun r => bs.any fun b =>
      (writesOf b).contains r || (r == .rax && (exitsOf b.term).any fun
        | .call .. => true
        | _ => false)
    mem := bs.any fun b => b.accesses.any isHeapStore || (exitsOf b.term).any fun
      | .call n _ => (callees.find? (·.name == n)).any (·.mem)
      | _ => false }

end Skel.Gen
