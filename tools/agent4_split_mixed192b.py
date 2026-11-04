"""Deterministic source-preserving Lean module splitter for mixed-192 proof audits.

This splits a complete input source at theorem boundaries; it never substitutes
axioms, changes proof bodies, or omits a theorem. The final Back192BStep depends
on all four preceding verified modules.
"""
from __future__ import annotations
import fcntl
import os
from pathlib import Path
import sys
import tempfile

STARTS = (
    ("Back192BDefs", "import BackwardMod", "theorem low_transfer"),
    ("Back192BLow", "theorem low_transfer", "private theorem high_not_sum_one"),
    ("Back192BZero", "private theorem high_not_sum_one", "theorem zero_a_pos"),
    ("Back192BZeroPos", "theorem zero_a_pos", "private theorem high_no_sum_zero_mod4"),
    ("Back192BHighEven", "private theorem high_no_sum_zero_mod4", "theorem high_a0_odd"),
    ("Back192BHighOdd", "theorem high_a0_odd", "theorem high_a_pos"),
    ("Back192BHighPos", "theorem high_a_pos", "theorem backward_step"),
    ("Back192BStep", "theorem backward_step", "end A4Backward192B"),
)

def split_file(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    assert text.count("namespace A4Backward192B\n") == 1
    assert text.count("end A4Backward192B\n") == 1
    header = (
        "set_option maxHeartbeats 0\n"
        "set_option maxRecDepth 8000\n"
        "namespace A4Backward192B\n"
        "open A4Backward\n\n"
    )
    with open(path.parent / ".mixed192b-split.lock", "a+", encoding="utf-8") as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        for i, (module, begin, end) in enumerate(STARTS):
            a = text.index(begin)
            b = text.index(end, a)
            if i == 0:
                # Retain the exact original module header and definitions.
                content = text[a:b] + "\nend A4Backward192B\n"
            else:
                content = f"import {STARTS[i-1][0]}\n" + header
                content += text[a:b] + "\nend A4Backward192B\n"
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
