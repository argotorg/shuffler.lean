#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=${PERMUTE_GUIDED_BUILD:-"$test_dir/../build/guided"}
build_dir=$(CDPATH= cd -- "$build_dir" && pwd)
exec "$build_dir/fuzz/permute-fuzz" "$build_dir/corpus" \
    -artifact_prefix="$build_dir/artifacts/" -max_len=8195 -timeout=10 \
    -rss_limit_mb=2048 -print_final_stats=1 "$@"
