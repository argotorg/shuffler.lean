# x86 permute

`permute.S` implements the full non-allocating `permute` routine. It uses the
System V AMD64 calling convention. Its 438 code bytes contain 136 instructions.
The instruction set is MOV, XOR, CMP, ADD, SUB, PUSH, POP, RET, JNE, JNS, and JMP.
The assembly retains the LLVM block names where the blocks correspond.

For compiler-generated alternatives and the measured Sail decoder coverage,
see [CODEGEN.md](CODEGEN.md).

The first six arguments are `n`, `data`, `permutation`, `target`, `used`, and
`trace`, in EDI, RSI, RDX, RCX, R8, and R9. The output pointer is the seventh
argument, at entry RSP + 8. The routine saves RBX and R12–R15 in 40 stack bytes.
It leaves RBP unchanged. RET advances RSP to entry RSP + 8.

## Native checks

First build the proved LLVM object as described in `../llvm/full/README.md`.
Then run from the repository root:

```sh
nix develop .#full-llvm -c python3 verification/x86/test_native.py \
  verification/x86/build \
  verification/llvm/full/permute.proved.o \
  spikes/clight-permute/permute.c
```

The test builds the actual assembly and compares it with the proved LLVM object
and generated C. It checks all six buffers, guards, unused trace cells, return
values, and all six callee-saved registers. It also rejects an assembly mutation
that changes the invalid return value, and rejects an added NOP in the byte audit.
The current run passes 1,004 cases and 1,004 register-preservation checks.

## Byte export

```sh
nix develop .#full-llvm -c python3 verification/x86/generate_program.py \
  verification/x86/build/permute.o verification/x86/X86Program.v
nix develop .#full-llvm -c python3 verification/x86/test_program.py
```

The generator reads the object's `.text` section. It checks that the disassembly
covers every byte in order. It exports bytes, instruction offsets and lengths,
and retained label offsets. It rejects unresolved relocations and missing labels.
The test also checks that export is deterministic and changes after a real
instruction mutation. Assemble with `clang -Wa,-L` to retain local labels.

`X86Program.v` checks the size, instruction lengths, byte coverage, and label
boundaries. These structural checks do not establish decoder correctness.

## Sail checks and Rocq proofs

`archsem.nix` patches the generated Sail model to add JMP rel32 decoding and
execution and correct the auxiliary-carry flag helpers. A third patch changes
an ArchSem module alias to an included module so that the independent Rocq
checker accepts the adapter. `test_semantics.py` checks the patched instructions
through the actual Sail decoder and execution functions.

`test_model.py` compiles the actual model through Sail's C backend. Pass the Sail
executable, patched model source, output directory, assembly object, and proved
LLVM object, in that order. The `archsem-x86` Nix package exposes the patched
model at `share/sail-tiny-x86`; the `x86-equiv` shell provides Sail.

The current model run checks all 136 instruction decodings and lengths, then
executes 55 complete calls. These cases include empty and oversized inputs,
invalid destinations, depth boundaries, blocked returns after partial progress,
and a 1,024-element identity permutation. Expected results come from the proved
LLVM object. The test supplies fixtures; it does not implement x86 semantics.

Rocq uses the generated Sail decoder through ArchSem. `X86Decode.v` supplies a
read-only event evaluator with a soundness proof. `X86DecodeReplay.v` records
every actual fetch request and proves the instruction lengths and fetch requests
for arbitrary code addresses and register values. A recorded request can be
used in an execution proof only after its address and value have been checked
against the actual ArchSem memory handler.

The native and Sail tests are finite tests. The Sail C runtime returns zero for
absent memory, so these tests do not prove ArchSem memory-access safety.

## Complete call proofs

`X86EmptyCall.empty_call_agrees` proves agreement of the empty-input LLVM and
x86 calls. `X86OversizedCall.oversized_call_agrees` proves agreement for every
unsigned input length greater than 1024. Both use the actual code bytes, Sail
decoder and execution functions, and ArchSem memory handlers. Both enable
nondeterminism in the semantics.

The empty call takes 24 instructions. The oversized call takes 19 or 21
instructions, according to the input's high bit. Their `*_call_run_agrees`
theorems give an exact singleton result of `opModel.run`, with no errors and
one extra fuel step to observe termination. The proofs derive execution from
the entry conditions; execution is not an input assumption.

The entry conditions include the ABI arguments, readable return address and
seventh argument, mapped save slots, code bytes, and code/stack/buffer
separation. A shared CompCert memory relates the LLVM state to the x86 bytes.
The return proofs establish related final memory, return code, zero output
fields, saved-register restoration, and the return PC and stack pointer.
See `RELATION.md` for these conditions.

`X86NonemptyCall.nonempty_call_agrees` proves the complete call for valid
permutations of length 1 through 1024 and arbitrary 32-bit source words. It
composes validation, normalization, choice, exchanges, and return. The LLVM
call and actual x86 execution reach memory states related to one CompCert
memory. The model determines the data, permutation, trace prefix, three output
fields, and return code. This includes blocked returns after partial progress.
The theorem derives execution from ABI and memory conditions; it has no
execution premise.

`X86NonemptyCall.nonempty_call_run_agrees` also proves an exact singleton
`opModel.run` result with no errors, for a finite instruction count plus one
termination step. It includes saved-register restoration, the return PC and
stack pointer, and the memory frame for caller arrays outside the six buffers.
Malformed destination arrays are outside this nonempty contract. Scratch
initial values and the unwritten trace tail have the same scope as in the
LLVM/model contract.

These are complete-call agreement theorems, not a step-for-step bisimulation.
The proved machine execution uses ArchSem's single-thread flat-memory model;
virtual-memory translation and hardware access checks are outside that model.

## Nonempty prefix

`X86Prefix.initialized_prefix_agrees` proves agreement from call entry through
output initialization, the size checks, and the complete used-array clearing
loop. For `0 < size <= 1024`, this takes `16 + 4 * size` actual x86 instructions.
LLVM and x86 reach the validation preheader with a shared final CompCert memory.
The theorem retains the output stores, array-clearing stores, LLVM local values,
argument registers, and saved stack data needed to continue the proof.

`X86CheckedPrefix.checked_prefix_agrees` extends this result through the complete
validation loop for valid permutation inputs. It derives `18 + 18 * size`
instructions from ABI entry to the normalization preheader. The common final
memory satisfies the existing Clight validation invariant. The proof preserves
the LLVM local values, output fields, caller arrays outside the written buffers,
machine argument registers, and saved stack data.

`X86FixedPrefix.fixed_prefix_agrees` extends this prefix through the loop that
marks positions where data equals target. It reaches the search-and-fill
preheader with the existing `FixedPrefix.fixed_prefix_arrays` result. The
complete prefix takes between `19 + 27 * size` and `19 + 29 * size` instructions;
each fixed-position iteration takes 9 or 11 instructions.

`X86NormalizedPrefix.normalized_prefix_agrees` adds the complete search-and-fill
pass. It derives execution from ABI entry to offset 262 and proves that both
memories contain the model's normalized permutation. The search uses the first
available matching target. LLVM and x86 use the same two assignment stores.

`X86MainPrefix.main_prefix_agrees` adds the four setup instructions and reaches
the main loop at offset 275. It establishes the existing Clight loop arrays and
LLVM main registers, together with x86 R12 equal to the top index and R15 equal
to the trace capacity. `X86ChoiceAgreement.main_choose_agrees` connects the
choice scan in both semantics. Both select the same position, or both take the
completion path. `X86ExchangeAgreement.v` connects equal, successful, and
blocked exchanges with shared store witnesses. `X86MainLoop.v` composes these
branches by induction on the model's rank bound and reaches the return path.

`X86ArrayDecode.v` proves decoding for all 28 scaled array memory instructions.
`X86UsedZero.v` proves every iteration and the complete clearing loop for a
shared store witness. These proofs use the actual code bytes and Sail semantics.
