#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Restore only the pinned, allowlisted CompCert source files."""
import hashlib
import importlib.util
from pathlib import Path
import urllib.request

BASE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("audit", BASE / "audit-deps.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
REVISION = "7b1f02b09954b9b916eb2a91d283c9b5355bf172"
records = [line.split("  ", 1)
           for line in (BASE / "vendor/compcert.sha256").read_text().splitlines()]
if len(records) != len(audit.ALLOWED) or {name for _, name in records} != audit.ALLOWED:
    raise SystemExit("manifest differs from the license allowlist")
for digest, name in records:
    url = f"https://raw.githubusercontent.com/AbsInt/CompCert/{REVISION}/{name}"
    with urllib.request.urlopen(url, timeout=30) as response:
        data = response.read()
    if hashlib.sha256(data).hexdigest() != digest:
        raise SystemExit(f"upstream digest mismatch: {name}")
    path = BASE / "vendor/compcert" / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
audit.audit()
print(f"Restored {len(records)} pinned files; selected LGPL-2.1-or-later.")
