"""Exact bit-packed A-section return simulator for rooted BB(6) row262.

Uses the source-certified 9q shortcut (PairBurst.lean, PairBurstSafe.lean).
Finite simulation only: reaching a cutoff without halt is not nonhalting proof.
"""
from __future__ import annotations
from dataclasses import dataclass

@dataclass(frozen=True)
class Snapshot:
    sections: int
    primitive_steps: int
    left: int
    head: int
    right: int
    coordinate: int

def run_sections(limit: int) -> tuple[Snapshot, dict[str, int]]:
    """Run at most limit authentic blank-root A-to-A sections, exactly."""
    assert limit >= 0
    left = right = head = p = raw = sections = 0
    counts = {k: 0 for k in ("odd", "b0", "d0", "d1c0", "d1c1", "burst", "burst_pairs")}
    while sections < limit:
        if head:
            e = ((left + 1) & (-left - 1)).bit_length() - 1
            head = (left >> (e + 1)) & 1
            left >>= e + 2
            right = 1 | (right << (e + 2))
            p -= e + 2
            raw += e + 4
            sections += 1
            counts["odd"] += 1
            continue
        if not right & 1:
            head = 1
            right |= 1
            raw += 2
            sections += 1
            counts["b0"] += 1
            continue
        if right & 3 == 3:
            raise RuntimeError(f"blank-root frozen F1 halt at primitive time {raw+2}; A-index {sections}")
        # Right prefix 10 followed by the maximal number of 001 triples.
        if ((right >> 2) & 7) == 4 and limit - sections >= 2:
            # Lean-certified maximal burst count from v₂(7R+9).
            numerator = 7*right + 9
            valuation = (numerator & -numerator).bit_length() - 1
            q = (valuation - 2)//3
            q = min(q, (limit-sections)//2)
            assert q >= 1
            left = (left << (3*q)) | (6 * ((1 << (3*q)) - 1) // 7)
            right = 1 | ((right >> (3*q+2)) << 2)
            p += 3*q
            raw += 9*q
            sections += 2*q
            counts["burst"] += 1
            counts["burst_pairs"] += q
            continue
        if not (right >> 3) & 1:
            x = (right >> 2) & 1
            left = (left << 5) | (24 + 2*x)
            head = (right >> 4) & 1
            right >>= 5
            p += 5
            raw += 5
            sections += 1
            counts["d0"] += 1
            continue
        if not (right >> 2) & 1:
            left = (left << 2) | 3
            right = 1 | ((right >> 4) << 2)
            p += 2
            raw += 6
            sections += 1
            counts["d1c0"] += 1
            continue
        left = (left << 1) | 1
        head = 1
        right = 1 | ((right >> 4) << 3)
        p += 1
        raw += 7
        sections += 1
        counts["d1c1"] += 1
    return Snapshot(sections, raw, left, head, right, p), counts

if __name__ == "__main__":
    for n in (100, 1000, 10000, 100000, 1000000, 10000000):
        state, counts = run_sections(n)
        print(f"A={state.sections:,}, raw={state.primitive_steps:,}, p={state.coordinate}, occupied={state.left.bit_count()+state.head+state.right.bit_count()}, bursts={counts['burst']}, pairs={counts['burst_pairs']}",flush=True)
    state, counts = run_sections(10000000)
    assert (state.primitive_steps, state.coordinate, state.left.bit_count()+state.head+state.right.bit_count()) == (46717881,2741,2722)
    assert (counts["burst"],counts["burst_pairs"]) == (12702,3292741)
    print("PASS independent bounded original-root checkpoint; no global nonhalting inference")
