#!/bin/sh
set -eu

# Run from the repository root. Use the same module build as the editor.
lake build Experiments

# Keep derived fixtures in .lake.
check_dir=$(mktemp -d .lake/build-bottom-up-experiments.XXXXXX)
trap 'rm -rf "$check_dir"' EXIT HUP INT TERM

# Use the production fixtures without keeping a second copy of their states.
# compareAndRun compares the result stack, every trace operand, and error excess.
for fixture in BuildBottomUpBranches BuildBottomUpProofs; do
  sed \
    -e 's/import Shuffler.BuildBottomUp.Defs/import Experiments.BuildBottomUp.Comparison/' \
    -e 's/build_bottom_up /BuildBottomUpExperiments.compareAndRun /g' \
    -e 's/\.Blocked excess/.blocked excess/g' \
    -e 's/| .ok _ => none/| .ok _ => none\n    | .error (.assertion _) => none/' \
    "Tests/$fixture.lean" > "$check_dir/$fixture.lean"
  lake env lean "$check_dir/$fixture.lean"
done
