# Compiler-generated x86

The compiler probe generates x86 from the exact printed, proved LLVM module.
It measures instruction coverage in the patched Sail model used by ArchSem.
It does not prove the generated code equivalent to the LLVM function.
The existing full-call x86 proof still covers `permute.S`.

## Reproduce

```sh
nix build .#x86-codegen-probe
cat result/results.json
cat result/clang-entry.log
```

This target uses the pinned LLVM 20.1.8 and Sail 0.20.3 packages. It consumes
`verified-permute-llvm/permute.proved.ll`; it does not change that LLVM input.
It builds assembly and object files, then loads the object's actual text bytes
into the Sail interpreter and invokes the production decoder at every
instruction boundary. LLVM's disassembler supplies the candidate boundaries;
the probe checks byte coverage, decoded instruction kind, and decoded length.
It rejects unresolved text relocations and incomplete interpreter reports.

The handwritten implementation is a positive control. An assembled `UD2`
instruction is a negative control for this model. The probe reports unsupported
instructions as results; a successful probe build does not mean the candidates
are accepted by ArchSem.

The output contains assembly, objects, text bytes, disassembly, interpreter
commands and logs, tool versions, source hashes, and commands for each variant.
The decoder runs with zeroed general-purpose registers at code address
`0x100000`. This is a concrete coverage check, not a proof for arbitrary machine
states, operand values, or memory maps.

## Observed results

The LLVM input SHA-256 is
`47b5bf5a460f0fb4b051998275d2e86c2afda7def4cee8e16fd6a18334baf72b`.
Counts include alignment instructions in the actual object.

| Variant | Bytes | Instructions | Accepted | Unsupported |
| --- | ---: | ---: | ---: | ---: |
| Handwritten control | 438 | 136 | 136 | 0 |
| Clang backend O2 | 489 | 137 | 100 | 37 |
| llc O0 | 1309 | 291 | 266 | 25 |
| llc O2 | 489 | 138 | 101 | 37 |
| llc O2, loop alignment 1 | 410 | 127 | 101 | 26 |
| llc O2, loop alignment 1, slow INC/DEC | 417 | 127 | 108 | 19 |

Clang backend O2 uses `-O2 -Xclang -disable-llvm-passes`. The LLVM input already
comes from the proved C-to-LLVM stage, whose Clang command uses `-O1`.
`llc` produces its objects directly, without invoking Clang.

The smallest remaining coverage gap in this experiment uses:

```sh
llc -O=2 -mtriple=x86_64-unknown-linux-gnu \
  -align-loops=1 -mattr=+slow-incdec \
  -filetype=obj permute.proved.ll -o permute.o
```

For this input, these settings remove all eleven padding NOPs and replace all
seven INC/DEC instructions. The remaining unsupported instructions are:

| Mnemonic | Count | Forms observed |
| --- | ---: | --- |
| JE | 9 | Signed 8-bit and 32-bit relative displacements |
| JBE | 1 | Signed 8-bit relative displacement |
| JAE | 2 | Signed 8-bit relative displacement |
| JB | 1 | Signed 32-bit relative displacement |
| TEST | 3 | 8-bit and 32-bit register operands |
| LEA | 2 | 32-bit and 64-bit destinations, base plus displacement |
| SETB | 1 | R8B destination |

Adding `+slow-lea,+slow-3ops-lea` and `-disable-x86-lea-opt` produces the same
text bytes as the slow-INC/DEC variant. These settings are compiler preferences,
not an instruction allowlist.

The entry execution probe initializes an empty Clang-backend-O2 call, its return
address, stack argument, and registers. The first eight instructions execute.
The ninth instruction, `JBE` at function offset `0x20`, fails decoding.
The Sail interpreter's memory fixture does not establish ArchSem memory safety.

## Required semantics work

The remaining extensions belong in `sail-tiny-x86`: add instruction
representations, decoder clauses, and execution clauses for the four operation
groups above. The existing Nix patch mechanism can carry the changes and
regenerate the Rocq model.

Tests must cover branch conditions and displacements, register widths and
partial writes, and LEA's address calculation without a data-memory read.
TEST's auxiliary-carry flag is unspecified; proofs must not depend on its value.
Instruction lemmas and the equivalence proof for the generated function remain
to be written. No instruction extension is included in this probe.
