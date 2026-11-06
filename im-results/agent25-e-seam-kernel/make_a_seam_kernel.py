"""Generate a Lean-kernel finite-window certificate for the A boundary.

Python discovers an abstract graph under the literal 11-entry D table; Lean
independently checks every state, successor, seed and quantified path closure.
"""
from __future__ import annotations

import sys
from collections import deque
from pathlib import Path
from filelock import FileLock
import make_e_seam_kernel as e

RULE = (
    ((1, 1, 1), (0, 1, 4)),
    ((1, -1, 2), (0, 1, 0)),
    ((1, -1, 0), (1, -1, 3)),
    ((1, -1, 2), (1, -1, 5)),
    ((0, -1, 2), (0, -1, 1)),
    ((1, -1, 4), None),
)


def successors(code: int) -> list[int]:
    state, off, bits = code & 7, (code >> 3) & 31, code >> 8
    scanned = (bits >> off) & 1
    if off == 1 or (state == 5 and scanned):
        return []
    if state == 5 and scanned == 0 and bits & ((1 << off) - 1) == 0:
        return []
    write, direction, next_state = RULE[state][scanned]
    new_bits = (bits | (1 << off)) if write else (bits & ~(1 << off))
    next_off = off + direction
    if next_off == 17:
        return [(new_bits << 8) | (16 << 3) | s for s in range(6)]
    return [(new_bits << 8) | (next_off << 3) | next_state]


def find_invariant() -> list[int]:
    seeds = [((171 + 1024 * r) << 8) | (9 << 3) for r in range(128)]
    seen = set(seeds)
    pending = deque(seeds)
    while pending:
        v = pending.popleft()
        for w in successors(v):
            if w not in seen:
                seen.add(w)
                pending.append(w)
    if len(seen) != 4733 or sum(len(successors(v)) for v in seen) != 5462:
        raise AssertionError("Unexpected abstract A graph")
    return sorted(seen)


def generate(output: Path) -> None:
    numbers = find_invariant()
    blocks = [numbers[i:i + e.BLOCK_SIZE] for i in range(0, len(numbers), e.BLOCK_SIZE)]
    base = e.LEAN_BASE.replace("__BLOCKS__", "\n".join(
        f"def block{i} : Tree := {e.balanced_tree(b)}" for i, b in enumerate(blocks)
    )).replace("__ROOT__", e.block_tree(blocks, list(range(len(blocks)))))
    base = base.replace(
        "off <= 17 && state <= 5 && bits < 262144",
        "off <= 16 && state <= 5 && bits < 131072",
    ).replace(
        "(off != 1 || (state == 2 && bits.testBit 1))",
        "(off != 1 || ((state == 2 || state == 0) && bits.testBit 1))",
    ).replace(
        "bits.land (262143 - mask)", "bits.land (131071 - mask)"
    ).replace("nextOff == 18", "nextOff == 17").replace(
        "encode 17 s nextBits", "encode 16 s nextBits"
    )
    master = e.master_file(len(blocks)).replace(
        "encode 10 4 (171+2048*", "encode 9 0 (171+1024*"
    ).replace("E-boundary", "A-boundary")
    output.mkdir(parents=True, exist_ok=True)
    with FileLock(str(output / ".generate.lock")):
        e.write_atomic(output / "ESeamTreeBase.lean", base)
        for i in range(len(blocks)):
            src = (
                "import ESeamTreeBase\nset_option maxRecDepth 100000\n"
                "set_option maxHeartbeats 0\nnamespace BB6.TreeCert\n"
                f"theorem block{i}_good : allGood block{i} = true := by decide\n"
                f"#print axioms block{i}_good\nend BB6.TreeCert\n"
            )
            e.write_atomic(output / f"ESeamTreeBlock{i}.lean", src)
        e.write_atomic(output / "ESeamTreeMaster.lean", master)
    print("A-seam graph", len(numbers), "states", len(blocks), "Lean blocks")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python make_a_seam_kernel.py OUTPUT_DIRECTORY")
    generate(Path(sys.argv[1]).resolve())
