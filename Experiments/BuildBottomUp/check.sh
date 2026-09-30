#!/bin/sh
set -eu

# Run from the repository root. Use the same module build as the editor.
mode=${1:-all}
case "$mode" in
  all) lake build Experiments ;;
  --independent) lake build Experiments.BuildBottomUp.Tests Experiments.BuildBottomUp.Fixtures ;;
  *) echo "usage: $0 [--independent]" >&2; exit 2 ;;
esac

# Keep derived fixtures in .lake.
check_dir=$(mktemp -d .lake/build-bottom-up-experiments.XXXXXX)
trap 'rm -rf "$check_dir"' EXIT HUP INT TERM

# Use the production fixtures without keeping a second copy of their states.
# compareAndRun compares the result stack, every trace operand, and error excess.
for fixture in BuildBottomUpBranches BuildBottomUpProofs; do
  if [ "$mode" = all ]; then
    sed \
      -e 's/import Shuffler.BuildBottomUp.Defs/import Experiments.BuildBottomUp.Comparison/' \
      -e 's/build_bottom_up /BuildBottomUpExperiments.compareAndRun /g' \
      -e 's/\.Blocked excess/.blocked excess/g' \
      -e 's/| .ok _ => none/| .ok _ => none\n    | .error (.assertion _) => none/' \
      "Tests/$fixture.lean" > "$check_dir/$fixture.lean"
    lake env lean "$check_dir/$fixture.lean"
  fi

  # Check the same fixtures using only checked code, proofs, and core modules.
  sed \
    -e 's/import Shuffler.BuildBottomUp.Defs/import Experiments.BuildBottomUp.Fixtures/' \
    -e 's/build_bottom_up/BuildBottomUpExperiments.Checked.runFixture/g' \
    -e 's/LoopInvariant/BuildBottomUpExperiments.Checked.Processed/g' \
    -e 's/is_available/isAvailable/g' \
    -e 's/is_final/isFinal/g' \
    -e 's/State.generate_effects/BuildBottomUpExperiments.Checked.generate_contract/g' \
    -e 's/State.generate_preserves/BuildBottomUpExperiments.Checked.Generation.invariant/g' \
    "Tests/$fixture.lean" > "$check_dir/Checked$fixture.lean"
  lake env lean "$check_dir/Checked$fixture.lean"
done
