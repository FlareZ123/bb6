"""Prefix-cylinder audit for the original six-state D cryptid.

For each certified prefix, both boundary runs finish their first physical
F/0-or-F/1 event without examining the unknown right suffix. Therefore each
accepted prefix represents EVERY possible infinite or finite suffix extension.
The result is intentionally restricted to m=3 versus m=7, not all k.
"""
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
import sys
import time

# Literal table 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---
# Each entry = (written bit, signed direction, next state).
RULE = {
    (0, 0): (1, 1, 1), (0, 1): (0, 1, 4),
    (1, 0): (1, -1, 2), (1, 1): (0, 1, 0),
    (2, 0): (1, -1, 0), (2, 1): (1, -1, 3),
    (3, 0): (1, -1, 2), (3, 1): (1, -1, 5),
    (4, 0): (0, -1, 2), (4, 1): (0, -1, 1),
    (5, 0): (1, -1, 4),
}


@dataclass(frozen=True)
class Event:
    kind: str
    steps: int
    head: int
    ones: frozenset[int]


def evaluate(phase: int, m: int, prefix: str, cap: int = 300000) -> Event | None:
    """Return event only when it is independent of all unread right bits."""
    if phase not in (0, 4):
        raise ValueError("Use A boundary 0 or E boundary 4")
    if not set(prefix) <= {"0", "1"}:
        raise ValueError("prefix is binary")
    left = ([0] if phase == 0 else [0, 0])
    left += [bit for _ in range(m) for bit in (1, 0)] + [1, 1]
    ones = {-i - 1 for i, bit in enumerate(left) if bit}
    ones.update(i + 1 for i, bit in enumerate(prefix) if bit == "1")
    head, state, left_count = 0, phase, sum(left)
    last_known = len(prefix)
    for steps in range(cap + 1):
        # The first bit beyond the prefix has never been read or written.
        if head > last_known:
            return None
        bit = int(head in ones)
        if state == 5:
            if bit:
                return Event("halt", steps, head, frozenset(ones))
            if steps > 0 and left_count == 0:
                return Event("return", steps, head, frozenset(ones))
        if steps == cap:
            raise RuntimeError(f"step cap: {phase=} {m=} {prefix=}")
        write, direction, state = RULE[(state, bit)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        if direction == 1:
            left_count += write
        head += direction
        if direction == -1:
            left_count -= int(head in ones)
    raise AssertionError("unreachable")


def check(phase: int, lo: Event, hi: Event) -> bool:
    """Check exactly the bounded first-event shift, including physical tape."""
    if lo.kind != hi.kind:
        return False
    if phase == 4:
        if hi.steps - lo.steps != (8 if lo.kind == "return" else 0):
            return False
    else:
        dt = hi.steps - lo.steps
        if dt < 0 or dt % 24 != (8 if lo.kind == "return" else 0):
            return False
    if lo.kind == "return":
        if lo.head - hi.head != 8:
            return False
        if any(i not in hi.ones for i in range(hi.head + 1, lo.head + 1)):
            return False
        if {i for i in lo.ones if i > lo.head} != {
            i for i in hi.ones if i > lo.head
        }:
            return False
    return True


def certify(phase: int, depth: int) -> dict:
    if depth < 0:
        raise ValueError("negative depth")
    pending = [""]
    counts = Counter()
    certificates = []
    for d in range(depth + 1):
        next_pending = []
        for prefix in pending:
            a = evaluate(phase, 3, prefix)
            b = evaluate(phase, 7, prefix)
            if a is None or b is None:
                if d < depth:
                    next_pending.extend((prefix + "0", prefix + "1"))
                continue
            if not check(phase, a, b):
                raise AssertionError((phase, prefix, a, b))
            counts[a.kind] += 1
            certificates.append((prefix, a.kind, a.steps, b.steps,
                                 a.head, b.head))
        pending = next_pending
        if not pending:
            break
    # The cylinders are prefix-free; each prefix of length d <= depth
    # covers exactly 2^(depth-d) depth-depth binary continuations.
    covered = sum(2 ** (depth - len(w)) for w, *_ in certificates)
    return {
        "phase": phase,
        "depth": depth,
        "closed_cylinders": len(certificates),
        "closed_halt": counts["halt"],
        "closed_return": counts["return"],
        "covered_numer": covered,
        "covered_denom": 2 ** depth,
        "unresolved_at_depth": 2 ** depth - covered,
        "witnesses": certificates,
    }


def main(depth: int = 22) -> None:
    for phase in (0, 4):
        start = time.perf_counter()
        result = certify(phase, depth)
        witnesses = result.pop("witnesses")
        data = json.dumps(witnesses, separators=(",", ":")).encode()
        print(json.dumps(result, indent=2))
        print("witnesses_sha256", hashlib.sha256(data).hexdigest())
        print("elapsed_seconds", round(time.perf_counter() - start, 3),
              flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 22)
