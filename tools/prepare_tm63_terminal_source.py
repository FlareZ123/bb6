#!/usr/bin/env python3
"""Materialize original TM63 terminal Lean sources stored in tracked xz/Base64.

This is preparation of byte-pinned *source files*, not use of an imported
binary theorem or an axiom. A source-closure build still compiles all imports.
The authoritative TerminalLeft source supersedes the older archive copy.
"""
from __future__ import annotations

import base64
import hashlib
import io
import lzma
import pathlib
import tarfile

HERE = pathlib.Path(__file__).resolve().parents[1]
BASE = HERE / "im-results" / "agent42-champion-terminal"
ARCHIVE = BASE / "TerminalProofs.tar.xz.b64"
LEFT = BASE / "TerminalLeftExact.lean.xz.b64"
EXPECTED = {
    "TerminalFinish.lean": "12329036c66c3846f9261167b8f9aebd1778d9b6ea6044309956c2fa0b3e49b7",
    "TerminalLeft.lean": "1bce2075fc4e0cd7d740fb71b3796088b190ddb6766e04640d992dadd1b650ff",
}


def write_untracked(name: str, data: bytes) -> None:
    if not name.endswith(".lean") or "/" in name:
        raise ValueError(f"invalid Lean source name: {name!r}")
    existing = list((HERE / "im-results").rglob(name))
    if existing:
        print("Reusing tracked", existing[0].relative_to(HERE))
        return
    out = BASE / name
    out.write_bytes(data)
    print("Materialized", out.relative_to(HERE), len(data), "bytes")


with tarfile.open(fileobj=io.BytesIO(base64.b64decode(ARCHIVE.read_text())), mode="r:xz") as archive:
    for member in archive.getmembers():
        if not member.isfile() or not member.name.endswith(".lean"):
            continue
        name = pathlib.PurePosixPath(member.name).name
        if name == "TerminalLeft.lean":
            continue  # authoritative replacement follows
        stream = archive.extractfile(member)
        if stream is None:
            raise ValueError(f"missing archive source: {member.name}")
        data = stream.read()
        if name in EXPECTED:
            digest = hashlib.sha256(data).hexdigest()
            if digest != EXPECTED[name]:
                raise ValueError(f"{name} archive SHA256 mismatch: {digest}")
        write_untracked(name, data)

left = lzma.decompress(base64.b64decode(LEFT.read_text()))
digest = hashlib.sha256(left).hexdigest()
if digest != EXPECTED["TerminalLeft.lean"]:
    raise ValueError(f"TerminalLeft authoritative SHA256 mismatch: {digest}")
write_untracked("TerminalLeft.lean", left)
for name, wanted in EXPECTED.items():
    file = BASE / name
    if not file.exists() or hashlib.sha256(file.read_bytes()).hexdigest() != wanted:
        raise ValueError(f"{name} missing or wrong SHA256 after source materialization")
print("Original TM63 terminal source preparation complete")
