"""Deterministic source-preserving Lean module splitter for mixed-192 proof audits.

This splits a complete input source at theorem boundaries; it never substitutes
axioms, changes proof bodies, or omits a theorem. The final Back192Step depends
on all four preceding verified modules.
"""
from __future__ import annotations
import fcntl
import os
from pathlib import Path
import sys
import tempfile

STARTS = (
    ("Back192Defs", "import BackwardMod", "theorem low_transfer"),
    ("Back192Low", "theorem low_transfer", "theorem zero_a0"),
    ("Back192Zero", "theorem zero_a0", "theorem high_a0_even"),
    ("Back192High", "theorem high_a0_even", "theorem backward_step"),
    ("Back192Step", "theorem backward_step", "end A4Backward192"),
)

def split_file(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    assert text.count("namespace A4Backward192\n") == 1
    assert text.count("end A4Backward192\n") == 1
    header = (
        "set_option maxHeartbeats 0\n"
        "set_option maxRecDepth 8000\n"
        "namespace A4Backward192\n"
        "open A4Backward\n\n"
    )
    with open(path.parent / ".mixed192-split.lock", "a+", encoding="utf-8") as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        for i, (module, begin, end) in enumerate(STARTS):
            a = text.index(begin)
            b = text.index(end, a)
            if i == 0:
                # Retain the exact original module header and definitions.
                content = text[a:b] + "\nend A4Backward192\n"
            else:
                content = f"import {STARTS[i-1][0]}\n" + header
                content += text[a:b] + "\nend A4Backward192\n"
            out = path.parent / f"{module}.lean"
            with tempfile.NamedTemporaryFile(
                "w", encoding="utf-8", dir=out.parent, delete=False
            ) as handle:
                handle.write(content)
                temp = handle.name
            os.replace(temp, out)
            print(f"Emitted {out.name}: {len(content)} chars", flush=True)

if __name__ == "__main__":
    split_file(Path(sys.argv[1]))
