#!/usr/bin/env python3
"""Raise only a generated Raw112 module's elaborator recursion limit."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def patch_file(path: Path, depth: int = 300000) -> dict:
    original = path.read_bytes()
    text = original.decode("utf-8")
    old = "set_option maxRecDepth 100000"
    new = f"set_option maxRecDepth {depth}"
    if text.count(new) == 1 and old not in text:
        return {"path": str(path), "changed": False, "sha256": sha256(original), "depth": depth}
    if text.count(old) != 1:
        raise ValueError(
            f"expected exactly one {old!r} in {path}, found {text.count(old)}"
        )
    patched = text.replace(old, new, 1).encode("utf-8")
    path.write_bytes(patched)
    return {
        "path": str(path),
        "changed": True,
        "old_sha256": sha256(original),
        "sha256": sha256(patched),
        "depth": depth,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("path", type=Path)
    parser.add_argument("--depth", type=int, default=300000)
    args = parser.parse_args()
    print(json.dumps(patch_file(args.path, args.depth), sort_keys=True))


if __name__ == "__main__":
    main()
