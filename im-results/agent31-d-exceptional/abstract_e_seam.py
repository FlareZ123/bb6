"""Finite-window abstraction for the E-boundary first-marker safety property.

Scope: original D 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---,
state E on scanned zero, left nearest-first 00(10)^m11, arbitrary right
binary tape (including infinite support).

The exact region from -(2m+4) through R is tracked. Every excursion beyond
R is OVERAPPROXIMATED by an immediate possible reentry at R in ANY of the
six live states, with tracked cells unchanged. This includes all physical
runs, regardless of unknown far-right tape. We stop at first visit to the
left marker x=-(2m+3), at F/1 or at a physical F/0 event. If the finite
reachable-state closure contains only C/1 marker entries, the corresponding
UNIVERSAL right-tape safety claim follows by simulation.
"""
from collections import deque
from cylinder_first_event import RULE


def audit(m: int = 3, radius: int = 7, limit: int = 1000000):
    if m < 3 or radius < 0:
        raise ValueError("expected m>=3, radius>=0")
    left = [0, 0] + [x for _ in range(m) for x in (1, 0)] + [1, 1]
    lowest = -len(left)
    marker = lowest + 1
    known_bit_mask = (1 << (radius - lowest + 1)) - 1
    left_mask = sum(bit << idx for idx, bit in enumerate(reversed(left)))
    initial = [
        (0, 4, left_mask | (right << (1 - lowest)))
        for right in range(1 << radius)
    ]
    visited = set(initial)
    pending = deque(initial)
    marker_states = set()
    transitions = 0
    while pending:
        head, state, tape = pending.popleft()
        bit = (tape >> (head - lowest)) & 1
        if head == marker:
            marker_states.add((state, bit))
            continue
        if state == 5 and bit:
            continue  # F/1: first halt event
        # F/0 physically blank strictly left: first return event
        if state == 5 and not bit and tape & ((1 << (head - lowest)) - 1) == 0:
            continue
        write, direction, next_state = RULE[(state, bit)]
        one = 1 << (head - lowest)
        modified = (tape | one) if write else (tape & ~one)
        next_head = head + direction
        if next_head < lowest:
            raise AssertionError("crossed unseen left marker")
        if next_head <= radius:
            choices = [(next_head, next_state, modified)]
        else:
            # Arbitrary remote continuation can return in any state.
            choices = [(radius, s, modified) for s in range(6)]
        for successor in choices:
            transitions += 1
            if successor not in visited:
                visited.add(successor)
                pending.append(successor)
                if len(visited) > limit:
                    raise RuntimeError("abstraction state cap reached")
    if marker_states != {(2, 1)}:
        raise AssertionError(("unsafe abstraction", m, radius, marker_states))
    return {
        "m": m,
        "radius": radius,
        "reachable_states": len(visited),
        "transition_checks": transitions,
        "marker_states": sorted(marker_states),
        "verified": True,
    }


if __name__ == "__main__":
    import sys
    import json
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    radius = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    print(json.dumps(audit(m, radius), indent=2))
