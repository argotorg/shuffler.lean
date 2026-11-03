# SPDX-License-Identifier: GPL-3.0-or-later
"""Fetch the unchanged libstdc++ nothrow allocation wrapper."""
import hashlib
from pathlib import Path
import sys
import urllib.request

REVISION = "4db0e8df15bef836558857c291c323add11d035c"
SHA256 = "4c2466f46ae448de78523a245600acbbbca8680409e7f477f1939de28bac48c0"


def fetch(directory):
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / "new_opnt.cc"
    if not path.exists():
        url = (f"https://raw.githubusercontent.com/gcc-mirror/gcc/{REVISION}/"
               "libstdc%2B%2B-v3/libsupc%2B%2B/new_opnt.cc")
        data = urllib.request.urlopen(url, timeout=60).read()
        if hashlib.sha256(data).hexdigest() != SHA256:
            raise ValueError("nothrow runtime download hash differs")
        path.write_bytes(data)
    if hashlib.sha256(path.read_bytes()).hexdigest() != SHA256:
        raise ValueError("nothrow runtime source hash differs")
    return path


if __name__ == "__main__":
    print(fetch(Path(sys.argv[1])))
