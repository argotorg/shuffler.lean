# Zig source of the shuffler

## shuffler.zig

- SHA-256: `fd2d09d73e1224ff06449ac9560907a32382b18be2f47f18c9423e332dcd07e6` (1,573 lines, 71,836 bytes).
- Origin: `libyul/backends/evm/ssa/stack/shuffler.zig` of the solidity worktree `solidity-proof`
  (branch `shuffler-proof`, ref `b86f67bd4`; `Lift/LLVM/README.md` names the same commit and hash).
  Copied byte for byte. The review export confirms the blob at the full commit
  `b86f67bd4cc712eda85b937f0090b4b820ed6360` by importing its Git bundle and checking SHA-256.
- Licence: the file has a GPL-3.0 header (SPDX `GPL-3.0`); the origin project (solidity) has `LICENSE.txt`, GPL v3.
- It imports only `std` and `builtin`, so it compiles alone.

Command (the rule of `libyul/CMakeLists.txt`, as in `Lift/LLVM/compile.sh shuffler`), zig 0.17.1:

    zig build-obj shuffler.zig -target x86_64-linux-none -mcpu=baseline -O ReleaseSmall -fPIC -fstrip
      -fsingle-threaded -fomit-frame-pointer -fno-unwind-tables -fno-stack-check -fno-stack-protector
      -fno-builtin -fno-compiler-rt -fno-ubsan-rt -fno-emit-bin -femit-llvm-bc=shuffler.bc
    zig cc -target x86_64-linux-none -mcpu=baseline -S -O2 -Xclang -disable-llvm-passes -fPIC
      -fno-verbose-asm -fno-addrsig -Wno-override-module -Wno-unused-command-line-argument shuffler.bc -o shuffler.s

| Claim | Status |
| --- | --- |
| This command, with `zig` 0.17.1 (nix store `m096jak4...-zig-0.17.1`), gives `shuffler.bc` byte-equal to `Lift/LLVM/data/shuffler/shuffler.bc` (sha256 `84d565c2...`) | confirmed by a build and compare |
| The same command gives `shuffler.s` byte-equal to `Lift/LLVM/data/shuffler/shuffler.s` (sha256 `ffe4a915...`, 31 functions) | confirmed by a build and compare |
| The string in `Lift/Shuffler/Code.lean` (`shufflerProgram(...)`; until K4 in `Lift/P1/Test/ShufflerCode.lean`) is byte-equal to that `shuffler.s` (the header hash `ffe4a915...` is the hash of this text) | confirmed by compare |
| `tools/shuffler-pilot/extract.py` on the built `shuffler.s` gives `Lift/Level3/data/pilot.s` (sha256 `4e960ddc...`, 8 functions, 171 instructions), so `Lift/Level3/Code.lean` comes from this source | confirmed by a build and compare |
| The build used LLVM 22.1.8 `llc` checks of `compile.sh` (`llc` of the `.bc` gives `.s`) | from notes only (`Lift/LLVM/README.md`); not run |
| `shuffler.ll`, `shuffler.dbg.ll`, `shuffler.mir`, `types.json` come from this source | from notes only; not rebuilt |

## Other variants (not in this directory)

Compiled with the same command, these give assembly that is not the checked-in assembly:

- `solidity/.../shuffler.zig` (sha256 `96752574...`, has tail calls): `shuffler.s` sha256 `ceef0bd7...`.
- `solidity-notail/.../shuffler.zig` (sha256 `89456463...`, `@call(.never_tail, ...)` at 4 places): `shuffler.s` sha256 `05aedbc5...`.
- `solidity-workspace/.../shuffler.zig` (sha256 `09d2cc98...`, earlier form): `shuffler.s` sha256 `95fd1c47...`.

All are confirmed by a build and compare. The scratch directory `.claude/scratch/zignotail/` holds the first two.
