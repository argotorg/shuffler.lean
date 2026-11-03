#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Fetch pinned solc sources. Copy selected definitions without changes."""

import hashlib
from pathlib import Path
import sys
import urllib.request

REVISION = "cd1b0a209b17d3f6dd124bd89e1b9bcdff79b912"
BASE = f"https://raw.githubusercontent.com/argotorg/solidity/{REVISION}/"
FILES = {
    "Shuffler.cpp": (
        "libyul/backends/evm/ssa/stack/Shuffler.cpp",
        "b8f832c633b057e491afc3fed321de02ba6a89c6a10185a563609179f1baca7c",
    ),
    "Stack.h": (
        "libyul/backends/evm/ssa/Stack.h",
        "311fa0f7588c5383301cc0748b5a87ecd3a104c186feeeb8fb923667bee89df2",
    ),
    "StackSlot.h": (
        "libyul/backends/evm/ssa/StackSlot.h",
        "57c314be66b9d5bc9c7224744bb33de8d5a5cf15088b0b52bdf2b98c23e143d6",
    ),
}


def checked_source(directory, name):
    path, digest = FILES[name]
    cached = directory / name
    if not cached.exists():
        with urllib.request.urlopen(BASE + path, timeout=60) as response:
            data = response.read()
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError(f"download hash mismatch: {name}")
        cached.write_bytes(data)
    data = cached.read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(f"cached hash mismatch: {name}")
    return data.decode("utf-8")


def definition(source, signature):
    """Copy the selected braced definition from these hash-checked sources."""
    if source.count(signature) != 1:
        raise ValueError(f"signature is not unique: {signature}")
    start = source.index(signature)
    opening = source.index("{", start)
    depth = 1
    end = opening + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    if source[end:end + 1] == ";":
        end += 1
    return source[start:end] + "\n"


def prepare(directory):
    directory.mkdir(parents=True, exist_ok=True)
    sources = {name: checked_source(directory, name) for name in FILES}
    shuffler = sources["Shuffler.cpp"]
    stack = sources["Stack.h"]
    slots = sources["StackSlot.h"]
    # Preserve the complete upstream copyright and license notice.
    notice = shuffler[:shuffler.index("#include")]
    outputs = {
        "solc_types.inc": slots[
            slots.index("struct StackOffset\n"):
            slots.index("\n\n}", slots.index("struct StackDepth\n"))
        ],
        "solc_mapping.inc": definition(shuffler, "class Mapping\n"),
        "solc_permute.inc": definition(
            shuffler, "\t[[nodiscard]] std::optional<Blocked> permute("
        ),
        "solc_emission_helpers.inc": "\n".join(
            definition(shuffler, signature) for signature in (
                "\tDestination const& destinationOf(StackOffset const _pos) const\n",
                "\tbool isFinal(StackOffset const _pos) const\n",
                "\tStackDepth depthOf(StackOffset const _pos) const\n",
                "\tbool isSwapReachable(StackOffset const _pos) const\n",
                "\tvoid swapWith(StackOffset const _pos)\n",
                "\t[[nodiscard]] Blocked block(StackOffset const _position,",
                "\t[[nodiscard]] Blocked blockSwapUnreachable(StackOffset const _position)",
            )
        ),
        "solc_stack_helpers.inc": "\n".join(
            definition(stack, signature) for signature in (
                "\tvoid swap(Offset const& _offset)\n",
                "\tbool isValidSwapTarget(Offset const& _offset)",
                "\tbool isValidSwapTarget(Depth const& _depth)",
                "\tbool isBeyondSwapRange(Depth const& _depth)",
                "\tsize_t size() const",
                "\tDepth offsetToDepth(Offset const& _offset) const\n",
            )
        ),
    }
    for name, body in outputs.items():
        (directory / name).write_text(notice + body, encoding="utf-8")
    print(f"solc oracle: {REVISION}; {len(FILES)} source hashes checked")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: prepare_oracle.py CACHE_DIRECTORY")
    prepare(Path(sys.argv[1]))
