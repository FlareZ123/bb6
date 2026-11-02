"""Adapt the upstream-independent Agent 4 Lean sources to Lean's module system.

Exactly their initial import is promoted; all proof declarations remain unchanged.
This is for isolated CI verification, leaving shared original sources untouched.
"""
from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path


def convert(path: Path) -> None:
    data = path.read_text(encoding="utf-8")
    first, sep, rest = data.partition("\n")
    if not sep or not first.startswith("import "):
        raise ValueError(f"Expected a single first-line import: {path}")
    transformed = "module\n\npublic " + first + "\n\n@[expose] public section\n\n" + rest
    fd, temp_name = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.")
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as out:
            out.write(transformed)
            out.flush()
            os.fsync(out.fileno())
        os.replace(temp_name, path)
    finally:
        if os.path.exists(temp_name):
            os.unlink(temp_name)


if __name__ == "__main__":
    for filename in sys.argv[1:]:
        convert(Path(filename))
