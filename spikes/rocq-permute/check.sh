#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu

# Run inside the shell from shell.nix. Compile a copy to keep build files out
# of the working tree. The source files remain the ones used by the tests.
spike_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=$(mktemp -d)
trap 'find "$build_dir" -type f -delete; rmdir "$build_dir"' EXIT HUP INT TERM
cp "$spike_dir"/*.v "$build_dir/"
cd "$build_dir"

for module in Permute Proofs Compute CycleProbe Tests; do
  coqc -w -notation-overridden "$module.v"
done
coqchk -silent Permute Proofs Compute CycleProbe Tests
