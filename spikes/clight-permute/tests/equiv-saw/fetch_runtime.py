#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Fetch unchanged libstdc++ allocation functions with fixed source hashes."""
import hashlib
from pathlib import Path
import urllib.request

REVISION = "4db0e8df15bef836558857c291c323add11d035c"
FILES = {
    "new_op.cc": "c269d087c62f36bc42a2f3320ed47890feec6a68206bb23b7415039064acb6f8",
    "new_opnt.cc": "4c2466f46ae448de78523a245600acbbbca8680409e7f477f1939de28bac48c0",
    "del_op.cc": "f1c216491477950df95c492943630379a83b64b971ab679d2900536a5ca64215",
    "del_ops.cc": "f0358ddb704ea1a884d38c5c3ef28f8a640e24a497dbc2ba67427681e20334dc",
}


def fetch(directory):
    directory.mkdir(parents=True, exist_ok=True)
    paths = []
    for name, digest in FILES.items():
        path = directory / name
        if not path.exists():
            url = (f"https://raw.githubusercontent.com/gcc-mirror/gcc/{REVISION}/"
                   f"libstdc%2B%2B-v3/libsupc%2B%2B/{name}")
            data = urllib.request.urlopen(url, timeout=60).read()
            if hashlib.sha256(data).hexdigest() != digest:
                raise ValueError(f"runtime download hash differs: {name}")
            path.write_bytes(data)
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"runtime source hash differs: {name}")
        paths.append(path)
    return paths
