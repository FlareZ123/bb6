"""Independent finite-window BFS for the original D-machine E-frontier lemma.

The window covers positions -8..7; head position 8 represents an arbitrary
excursion to the right. Re-entry from 8 to position 7 may occur in any state.
Stopping on first entry to -9 yields a conservative, unrestricted-suffix
finite transition system.

The source transition table is exactly
1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.
"""
from collections import Counter, deque

RULES = (
    ((1, 1, 1), (0, 1, 4)),
    ((1, -1, 2), (0, 1, 0)),
    ((1, -1, 0), (1, -1, 3)),
    ((1, -1, 2), (1, -1, 5)),
    ((0, -1, 2), (0, -1, 1)),
    ((1, -1, 4), None),
)
WINDOW_LEFT, WINDOW_RIGHT = -8, 7
EXTERNAL_POSITION = 8


def successors(config: tuple[int, int, int]) -> tuple[tuple[int, int, int], ...]:
    bits, pos, state = config
    if pos == EXTERNAL_POSITION:
        return tuple((bits, WINDOW_RIGHT, target) for target in range(6))
    symbol = (bits >> (pos - WINDOW_LEFT)) & 1
    rule = RULES[state][symbol]
    if rule is None:
        return ()
    written, direction, target = rule
    offset = pos - WINDOW_LEFT
    new_bits = (bits & ~(1 << offset)) | (written << offset)
    return ((new_bits, pos + direction, target),)


def initial_states() -> set[tuple[int, int, int]]:
    # The nearest-to-head left tape has 00 (10)^3.
    prefix = (0, 0, 1, 0, 1, 0, 1, 0)
    low_bits = sum(bit << (8 - index) for index, bit in enumerate(prefix, 1))
    return {(low_bits | (right << 9), 0, 4) for right in range(128)}


def verify() -> tuple[int, Counter[int]]:
    starts = initial_states()
    reached = set(starts)
    queue = deque(sorted(starts))
    exits: Counter[int] = Counter()
    while queue:
        config = queue.popleft()
        for nxt in successors(config):
            if nxt[1] == WINDOW_LEFT - 1:
                exits[nxt[2]] += 1
            elif nxt not in reached:
                reached.add(nxt)
                queue.append(nxt)

    # The following are assertions about a completed finite invariant.
    assert len(starts) == 128
    assert len(reached) == 6568, len(reached)
    assert exits == Counter({2: 95}), exits
    assert all(
        nxt[1] == WINDOW_LEFT - 1 or nxt in reached
        for source in reached for nxt in successors(source)
    )
    assert all(0 <= bits < 65536 and -8 <= pos <= 8 and 0 <= state <= 5
               for bits, pos, state in reached)
    return len(reached), exits


if __name__ == "__main__":
    count, exits = verify()
    print(f"Verified {count} abstract states from all 128 prefix seeds.")
    print(f"Left-frontier edges by entry state: {dict(exits)}")
