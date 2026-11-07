#!/usr/bin/env python3
"""Reproduce the 7-cell Root119 reverse-preimage closure used by Lean."""
from collections import deque
import json

# (write_bit, move, next_state); None denotes the A1 halt.
RULES = {
    "A": ((1, "R", "B"), None),
    "B": ((1, "L", "C"), (1, "L", "F")),
    "C": ((1, "L", "D"), (0, "L", "C")),
    "D": ((0, "L", "E"), (1, "R", "F")),
    "E": ((1, "R", "A"), (1, "L", "A")),
    "F": ((1, "L", "B"), (0, "R", "D")),
}


def mask(pattern: str) -> int:
    """Encode left-to-right h-3,...,h+3; bit 0 is h-3."""
    assert len(pattern) == 7 and set(pattern) <= {"0", "1"}
    return sum((ch == "1") << i for i, ch in enumerate(pattern))


def pattern(value: int) -> str:
    return "".join(str((value >> i) & 1) for i in range(7))


def step(state: tuple[str, int], edge: int):
    q, tape = state
    symbol = (tape >> 3) & 1
    rule = RULES[q][symbol]
    if rule is None:
        return None
    write, move, q2 = rule
    updated = (tape & ~(1 << 3)) | (write << 3)
    if move == "R":
        tape2 = (updated >> 1) | (edge << 6)
    else:
        tape2 = ((updated << 1) & 0x7F) | edge
    return q2, tape2


all_states = [(q, tape) for q in RULES for tape in range(128)]
initial = ("A", 0)
targets = {
    ("B", mask("1010000")),
    ("B", mask("1010110")),
}

# Reverse closure: every abstract predecessor of a bad state is bad.
reverse = {state: [] for state in all_states}
for state in all_states:
    for edge in (0, 1):
        successor = step(state, edge)
        if successor is not None:
            reverse[successor].append((state, edge))

bad = set(targets)
queue = deque(targets)
while queue:
    state = queue.popleft()
    for predecessor, edge in reverse[state]:
        if predecessor not in bad:
            bad.add(predecessor)
            queue.append(predecessor)

assert len(bad) == 12, len(bad)
assert initial not in bad
assert targets <= bad
assert all(pred in bad for state in bad for pred, _ in reverse[state])

# Independent forward audit of the finite abstraction.
reachable = {initial}
queue = deque([initial])
while queue:
    state = queue.popleft()
    for edge in (0, 1):
        successor = step(state, edge)
        if successor is not None and successor not in reachable:
            reachable.add(successor)
            queue.append(successor)
assert len(reachable) == 342, len(reachable)
assert not (targets & reachable)

rows = [
    {"state": q, "window": pattern(tape), "mask": tape}
    for q, tape in sorted(bad, key=lambda item: ("ABCDEF".index(item[0]), item[1]))
]
print(json.dumps({
    "window": "h-3,...,h+3; bit0 is leftmost",
    "abstract_state_count": len(all_states),
    "forward_reachable_count": len(reachable),
    "target_windows": [
        {"state": q, "window": pattern(tape), "mask": tape}
        for q, tape in sorted(targets)
    ],
    "reverse_preimage_closure_count": len(bad),
    "initial_in_reverse_closure": initial in bad,
    "reverse_preimage_closure": rows,
}, indent=2))
