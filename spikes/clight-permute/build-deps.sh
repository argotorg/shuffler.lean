#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
cd "$(dirname "$0")"
python3 audit-deps.py --stage
find build/compcert -name '*.v' -print | sort > build/compcert-sources.txt
coqdep -sort -R build/compcert compcert $(cat build/compcert-sources.txt) > build/compcert-order.txt
for source in $(cat build/compcert-order.txt); do
    object="${source%.v}.vo"
    if [ ! -f "$object" ] || [ "$source" -nt "$object" ]; then
        printf 'Compile %s\n' "$source"
        coqc -w -deprecated-from-Coq -R build/compcert compcert "$source"
    fi
done
