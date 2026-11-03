#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
spike_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
sh "$spike_dir/build.sh"
mkdir -p "$spike_dir/build/proofs" "$spike_dir/build/legacy"
python3 - "$spike_dir" <<'PY'
import importlib.util
from pathlib import Path
import re
import shutil
import sys

root = Path(sys.argv[1])
spec = importlib.util.spec_from_file_location("audit", root / "audit-deps.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
audit.audit_project(root)
legacy = root / "build/legacy"
proofs = root / "build/proofs"
for module in sorted(audit.LEGACY_MODULES):
    source = (root.parent / "rocq-permute" / (module + ".v")).read_text()
    audit.imports(source, audit.LEGACY_MODULES,
                  external=("Coq", "Stdlib", "mathcomp"))
    source = re.sub(r"(?m)^Require Import ", "From Legacy Require Import ", source)
    (legacy / (module + ".v")).write_text(source)
for source in root.glob("*.v"):
    shutil.copy2(source, proofs / source.name)

modules = sorted(source.stem for source in root.glob("*.v"))
qualified = [(module, proofs / (module + ".v")) for module in modules]
qualified += [("Legacy." + module, legacy / (module + ".v"))
              for module in sorted(audit.LEGACY_MODULES)]
statements = []
theorems = []
for module, path in qualified:
    statements.append(f"Require Import {module}.")
    for name in re.findall(
        r"(?m)^(?:Theorem|Lemma|Example|Corollary|Fact|Proposition)\s+([\w']+)",
        audit.uncomment(path.read_text()),
    ):
        qualified_name = module + "." + name
        theorems.append(qualified_name)
        statements += ["Goal True.", f'idtac "{qualified_name}".', "Abort.",
                       f"Print Assumptions {qualified_name}."]
(proofs / "Assumptions.v").write_text("\n".join(statements) + "\n")
(proofs / "assumption-theorems.txt").write_text("\n".join(theorems) + "\n")
for name in ("ProofContract.v", "ReachabilityContract.v", "PublicContract.v"):
    contract = root / "tests/proof-challenge" / name
    audit.imports(contract.read_text(), set(modules) | {Path(name).stem for name in audit.ALLOWED},
                  external=("Coq", "Stdlib", "Flocq", "mathcomp"))
    shutil.copy2(contract, proofs / contract.name)
checked = modules + ["Legacy." + module for module in sorted(audit.LEGACY_MODULES)]
checked += ["compcert." + name[:-2].replace("/", ".")
            for name in sorted(audit.ALLOWED) if name.endswith(".v")]
(proofs / "checked-modules.txt").write_text("\n".join(checked) + "\n")
PY
cd "$spike_dir/build/legacy"
for module in Permute Proofs Compute CycleProbe Tests; do
    coqc -w -notation-overridden -Q . Legacy "$module.v"
done
cd "$spike_dir/build/proofs"
coqdep -sort -R ../compcert compcert -Q ../legacy Legacy \
    $(cat checked-modules.txt | sed -n '/^[^.]*$/s/$/.v/p') > source-order.txt
for source in $(cat source-order.txt); do
    # coqdep -sort also lists transitive sources in other load paths.
    # Dependencies have already been built. Compile project copies only.
    case "$source" in
        */*) ;;
        *) coqc -w -notation-overridden,-deprecated-from-Coq \
             -R ../compcert compcert -Q ../legacy Legacy "$source" ;;
    esac
done
coqc -R ../compcert compcert -Q ../legacy Legacy Assumptions.v \
    > "$spike_dir/build/proof-assumptions.txt"
python3 "$spike_dir/test-assumptions.py"
python3 "$spike_dir/check-assumptions.py" "$spike_dir/build/proof-assumptions.txt" \
    assumption-theorems.txt
coqc -R ../compcert compcert -Q ../legacy Legacy ProofContract.v
coqc -R ../compcert compcert -Q ../legacy Legacy ReachabilityContract.v
coqc -R ../compcert compcert -Q ../legacy Legacy PublicContract.v
coqchk -silent -o -R ../compcert compcert -Q ../legacy Legacy \
    $(cat checked-modules.txt) ProofContract ReachabilityContract PublicContract \
    > "$spike_dir/build/proof-kernel.stdout" \
    2> "$spike_dir/build/proof-kernel-context.txt"
python3 "$spike_dir/check-assumptions.py" --kernel "$spike_dir/build/proof-kernel-context.txt"
printf 'Project, legacy, and allowed CompCert modules pass coqchk\n'
printf 'Proof assumptions: %s/build/proof-assumptions.txt\n' "$spike_dir"
