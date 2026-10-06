#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# Use the pinned shell. Optional arguments select retained corpus directories.
set -eu
ulimit -c 0
test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir="$test_dir/../build/filc"
mkdir -p "$build_dir"
build_dir=$(CDPATH= cd -- "$build_dir" && pwd)
archive="$build_dir/filc-0.686-linux-x86_64.tar.xz"
filc_dir="$build_dir/filc-0.686-linux-x86_64"
case $(uname -sm) in
    'Linux x86_64') ;;
    *) printf 'This runner pins the Linux x86_64 Fil-C package.\n' >&2; exit 1 ;;
esac
if [ ! -f "$archive" ]; then
    curl -fL https://github.com/pizlonator/fil-c/releases/download/v0.686/filc-0.686-linux-x86_64.tar.xz \
        -o "$archive.tmp"
    mv "$archive.tmp" "$archive"
fi
printf '60bfbe8ee63d7e462394aa8d5e44fee675de892bcf800d9cc80d86378cad6b07  %s\n' \
    "$archive" | sha256sum -c -
if [ ! -d "$filc_dir" ]; then
    tar -xJf "$archive" -C "$build_dir"
fi
if [ ! -d "$filc_dir/pizfix/os-include" ]; then
    (cd "$filc_dir" && sh setup.sh) > "$build_dir/setup.log" 2>&1
fi
# Nix lacks /lib64/ld-linux-x86-64.so.2. Change only the downloaded host
# compiler, using the same loader as the running shell. Target libraries keep
# Fil-C's own loader. No global paths, loaders, or configuration are changed.
compiler="$filc_dir/build/bin/clang-20"
if [ ! -e "$(patchelf --print-interpreter "$compiler")" ]; then
    host_loader=$(patchelf --print-interpreter "$(readlink -f "$(command -v sh)")")
    patchelf --set-interpreter "$host_loader" --set-rpath "$(dirname "$host_loader")" "$compiler"
fi
export FILC_DIR="$filc_dir"
if python3 "$test_dir/filc-run.py" "$@" > "$build_dir/run.log" 2>&1; then
    cat "$build_dir/run.log"
else
    cat "$build_dir/run.log" >&2
    exit 1
fi
