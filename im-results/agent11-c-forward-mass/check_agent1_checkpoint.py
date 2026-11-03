"""Independent exact-arithmetic audit of Agent1's 16 original m8 Lean segments.

Reads existing committed source; intentionally has no network or file writes.
This Python check does not replace the Lean kernel or genuine source-import CI.
"""
from __future__ import annotations

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "im-results" / "agent1-c-m8-trace" / "M8TraceCert.lean"
SEGMENT = re.compile(
    r"def seg(\d+)\s*:\s*List\s*\(Nat\s*×\s*\(Nat\s*×\s*Nat\)\)\s*"
    r":=\s*\[([^\]]*)\]",
    re.MULTILINE,
)
ENTRY = re.compile(r"\((\d+),\s*\((\d+),\s*(\d+)\)\)")


def bounce(k: int, c: int) -> tuple[int, int] | None:
    while c >= 4:
        if k % 2:
            if c <= 2 * k + 6:
                return 2 * k + 6 - c, c
            c, k = c - (2 * k + 3), 2 * k + 3
        else:
            if c == 4:
                return 2 * k + 2, 3
            if c == 5:
                return None
            if c <= 2 * k + 8:
                return 2 * k + 8 - c, c - 1
            c, k = c - (2 * k + 5), 2 * k + 4
    return None


def step(a: int, k: int) -> tuple[int, int] | None:
    if a == 0:
        if k == 0:
            return None
        if k == 1:
            return 0, 4
        return bounce(1, 2 * k + 1)
    if a == 1:
        if k == 0:
            return 5, 1
        if k == 1:
            return 2, 3
        if k == 2:
            return 2, 5
        if k == 3:
            return 0, 7
        return bounce(4, 2 * k - 3)
    if k == 0:
        return a - 2, 2
    if 2 * k <= a:
        return a - 2 * k, 2 * k + 2
    return bounce(a - 1, 2 * k - a + 3)


def main() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    blocks = list(SEGMENT.finditer(text))
    assert len(blocks) == 16, f"Expected 16 source segments, got {len(blocks)}"
    state = (5, 1)
    time = 0
    checkpoints = 0
    last_weight = 7

    for i, match in enumerate(blocks):
        assert int(match.group(1)) == i
        entries = list(ENTRY.finditer(match.group(2)))
        assert entries, f"Empty segment {i}"
        for entry in entries:
            steps, x, y = map(int, entry.groups())
            for _ in range(steps):
                updated = step(*state)
                assert updated is not None, f"Unexpected stop at return {time}"
                weight = updated[0] + 2 * updated[1]
                assert weight >= last_weight + 2, (time, state, updated)
                assert updated != (1, 524260), f"m8 gate hit at return {time + 1}"
                state = updated
                last_weight = weight
                time += 1
            assert state == (x, y), (
                f"Segment {i}, checkpoint {checkpoints}: {state} != {(x,y)}"
            )
            checkpoints += 1

    assert checkpoints == 151
    assert time == 150052
    assert state == (621619, 213453)
    assert last_weight == 1048525
    print(f"PASS: {len(blocks)} segments, {checkpoints} checkpoints, {time} returns.")
    print(f"Endpoint {state}, weight {last_weight}; m8 gate (1,524260), weight 1048521.")
    print("Independent finite arithmetic audit only; original-source Lean CI pending.")


if __name__ == "__main__":
    main()
