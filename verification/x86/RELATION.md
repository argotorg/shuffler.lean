# State relation for the x86 proof

This file describes the proof interface. It is not a proof of the assembly.

The x86 side must use `ArchSemX86.X86Inst.sail_tiny_x86_sem` and
`SequentialModel.sequential_model_outcome`. The former fetches and decodes
machine bytes through the Sail model. The latter handles actual register and
memory events. An instruction AST supplied by a separate decoder is not the
execution subject.

## Memory

ArchSem's `memoryMap` is `gmap (bv 64) (bv 8)`. Its `mem_lookup address 4` reads
four bytes in little-endian order. `read_mem_seq_state` uses the same operation.
Its store handler checks that every destination byte exists before writing.

Use the existing CompCert memory as a common witness for the LLVM and x86
states. Keep the LLVM relation unchanged:

```coq
cells_related layout c llvm
```

`X86Memory.machine_cells_related` requires, for every mapped cell `b, k`:

```coq
mem_present (Z_to_bv 64 (cell_address layout b k)) 4 machine = true
```

If `Mem.load Mint32 c b (4 * Z.of_nat k) = Some (Vint x)`, it also requires:

```coq
mem_lookup (Z_to_bv 64 (cell_address layout b k)) 4 machine =
  Some (Z_to_bv 32 (Int.unsigned x))
```

The complete relation contains both clauses with the same `c`. This preserves
the existing treatment of scratch cells: they need allocated memory but need
no initial integer value. It does not map Vellvm's symbolic bytes directly to
concrete x86 bytes.

`X86Layout.finite_layout` extends `allocation_layout` with a proof that each
nonempty block satisfies:

```text
0 <= base
base + 4 * number_of_cells <= 2^64
```

These bounds make address conversion injective on the mapped bytes. Together
with `blocks_disjoint`, they show that separate cells cannot alias after
conversion to 64-bit addresses. They also show that each four-byte access and
each in-range array index has the same address in integer and bitvector
arithmetic.

`X86CellAddress` proves the address equations for Sail's `add_vec` and `shiftl`
operations. A base pointer plus a zero-extended 32-bit index shifted left by
two equals the mapped cell address. It also proves that reading the low
32 bits after zero extension recovers the original word. These lemmas use no
axioms.

`X86MemoryStore.machine_cells_related_write` pairs ArchSem's actual write
handler with a supplied `Mem.store` result. It establishes the new cell value
and preserves every other mapped cell. Its state is built by
`stored_bytes_state`, which preserves registers and adds the written byte
addresses to `seq_state.written`. The LLVM proof can use the same `Mem.store`
result from `CellRelation.related_store`.

`X86MemoryInstructions` proves the actual Sail `read_memory` and `write_memory`
traces for four-byte and eight-byte accesses. This includes the Sail byte
conversion loops. `X86MemoryFrame` proves that disjoint writes preserve code
bytes and their status as unwritten bytes. `X86StackLayout` and `X86StackFrame`
prove stack-slot mapping, separation from buffers and code, and read results
after writes to separate locations. `X86SavedFrame` proves the five saved
register words and the return-address read after the prologue.

`X86CallFrame` proves that mapped four-byte buffer stores preserve all saved
stack words, the return address, and RSP and RBP. Its `cell_store_frame` theorem
combines this fact with preservation of code and register presence, and the
updated CompCert memory witness. Register writes to registers other than RSP
and RBP also preserve the call stack relation.

The memory handler and Sail conversion lemmas use no axioms. The memory
relation store lemmas retain the existing LLVM/CompCert assumptions:
`classic`, `functional_extensionality_dep`, `sig_not_dec`, and
`sig_forall_dec`.

## Entry and return

The assembly uses the SysV AMD64 integer argument locations:

| Argument | Entry location |
| --- | --- |
| size | low 32 bits of RDI |
| data | RSI |
| permutation | RDX |
| target | RCX |
| used | R8 |
| trace | R9 |
| output | eight-byte word at entry RSP + 8 |

The return address is the eight-byte word at entry RSP. The code first loads
the output pointer into R10. It then pushes RBX, R12, R13, R14, and R15, in that
order. The stack frame occupies `[entry RSP - 40, entry RSP)`. It uses no stack
locals and makes no calls. RBP is unchanged.

At return, RBX, RBP, and R12 through R15 equal their entry values. RIP equals
the saved return address and RSP equals entry RSP + 8. The low 32 bits of RAX
contain the result code. The source-level contract continues to observe data,
permutation, trace prefix, and the three output fields.

Require all registers touched by the instruction model to exist in the initial
register map. ArchSem rejects a write to an absent register. Initial values of
caller-saved registers can remain arbitrary. Require the return address and
output-pointer stack words to be mapped, and require the five save slots to be
mapped before the pushes.

Keep the code bytes disjoint from all six buffers and the stack frame. Keep
the stack interval `[entry RSP - 40, entry RSP + 16)` disjoint from the six
buffers. State the stack bounds in integers before converting addresses to
bitvectors. ArchSem records all writes and rejects instruction fetch from a
byte that was written earlier in the execution.

`X86Call.call_stack` relates the five saved stack words to their register
values in the initial state. It also records the saved return address, current
RSP, and unchanged RBP. `enter_call` proves the nine instructions through the
three zero output stores. `finish_call` proves the five POP instructions and
RET with nondeterminism enabled. It establishes the return ABI and leaves
memory unchanged. The body can preserve `call_stack` without requiring all
registers or all memory to remain unchanged.

## Execution result

Use one thread and a termination condition containing only the return address.
The return address must not occur at an earlier reachable instruction address.
Prove the actual sequential model reaches that state without an error. Its
fuel count includes one step per instruction and one final termination step.

Use the semantics with nondeterminism enabled, or prove that enabling it does
not change execution of this instruction subset. The upstream executable tests
use `sail_tiny_x86_sem false`; that flag replaces undefined choices by fixed
defaults. Tests with that flag alone do not establish the general statement.

The flat Sail model does not prove virtual-memory translation, access rights,
canonical-address checks, or the operating system's ABI. A theorem about this
model must say so. Low-half canonical addresses can be an additional input
condition when relating this model to a user-space process.

## Current proof scope

`X86EmptyCall.empty_call_run_agrees` relates complete LLVM and machine calls
for empty input. `X86OversizedCall.oversized_call_run_agrees` covers sizes above
1024. Both include the three output stores, register saves and restores, and
RET. They use the actual machine-byte decoder and nondeterminism enabled in
the Sail execution model. The two runs share the final CompCert memory witness.

`X86ValidationPass.validation_pass_agrees` relates the complete validation
pass for positive sizes through 1024. Each machine iteration and LLVM
iteration use the same two `Mem.store` results: mark the destination as used,
then write the source value into that destination in the target array. The
machine pass takes `14 * size + 2` instructions and preserves the argument
registers and saved call stack.

`X86FixedAgreement.fixed_pass_agrees` relates the normalization pass. The two
executions share the stores that set fixed destinations and their used flags.
`X86FixedMemory.fixed_store_step` supplies these stores from the array
invariant and the common memory relation.

`X86SearchLoop.search_found_loop` proves that the machine search reaches the
first unused target with a matching 32-bit value. It uses actual target and
used-array loads from the common CompCert memory. The search leaves memory
unchanged. It preserves all register reads except RIP, RBX, R13, and RFLAGS,
and returns the chosen index in R13 at offset 243. The separate
`search_preheader` proof starts at offset 201 and sets the search index to
zero. These statements allow nondeterminism in the Sail semantics.
`X86SearchModel.first_free_machine_search` links this execution to the same
`first_free` result used by the LLVM proof, with target and used arrays from
the model.

`X86ChoiceModel.choose_machine_permutation` relates the machine choice scan
to `Legacy.Permute.choose`. It starts at offset 275. A selected position
reaches offset 322 with that position in R13. If the model selects no
position, the machine reaches the zero-result path at offset 419. The proof
leaves memory unchanged and preserves the same register set as the search
proof, including R12 and R15. It covers the zero-index case and the loop
that scans destinations in descending order.

`X86ExchangeAgreement` relates all three exchange cases. Equal source values
cause only the permutation stores. A swap within the depth limit writes the
data, trace entry, trace count, and permutation. For unequal source values,
a choice beyond the depth limit writes the blocked position and excess
depth, then returns code 1.
Each case uses the same CompCert store results for LLVM and machine memory.

`X86MainLoop.main_loop_agrees` combines these cases with the choice proof and
the model's decreasing rank. The initial rank bound supplies enough fuel for
the model and space for the trace. The theorem proves the complete main loop
and its exact model result, through the machine cleanup entry at offset 428.
The three branch-proof premises of `main_loop_from_exchange_agreements` are
supplied by the exchange proofs in `main_loop_agrees`.

`X86NonemptyCall.nonempty_call_run_agrees` joins the entry, validation,
normalization, fill, main loop, and return proofs. It derives the complete
LLVM function call and machine execution from the input memory relation and
ABI entry conditions. It uses `sail_tiny_x86_sem true`. The machine run has
exactly one final state and no errors, and restores the callee-saved registers
and stack pointer. The final LLVM and machine memories share one CompCert
memory witness, which contains the exact model result's data, permutation,
trace prefix, and three output fields.

The nonempty theorem requires sizes from 1 through 1024, unsigned 32-bit
source values, a permutation destination map, and six separate arrays with
the stated capacities. It has no execution or branch-proof premise.
Malformed destination arrays are outside this theorem. Trace tails and
initial scratch values remain outside the model's result observations. This
is a complete-call result in the flat Sail model, not a step-for-step
bisimulation or a theorem about a hardware or operating-system implementation.
