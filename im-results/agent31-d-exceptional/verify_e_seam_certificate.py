"""Validate a finite inductive invariant, without running any graph search.

ESeamClosedStates.txt lists 6399 explicitly encoded states. Checking (1)
inclusion of all 128 possible initial right windows, (2) closure under every
concrete transition and arbitrary outside reentry, and (3) absence of a
forbidden marker state is sufficient by induction to prove the base safety
property for EVERY possible right tape. The checker does not need to trust
the algorithm that originally discovered the certificate.
"""
from pathlib import Path

TABLE = (
    ((1, 1, 1), (0, 1, 4)),
    ((1, -1, 2), (0, 1, 0)),
    ((1, -1, 0), (1, -1, 3)),
    ((1, -1, 2), (1, -1, 5)),
    ((0, -1, 2), (0, -1, 1)),
    ((1, -1, 4), None),
)


def encode(head: int, state: int, tape: int) -> int:
    return (tape << 8) | ((head + 10) << 3) | state


def verify() -> None:
    path = Path(__file__).with_name("ESeamClosedStates.txt")
    invariant = {
        int(line) for line in path.read_text().splitlines()
        if line and not line.startswith("#")
    }
    if len(invariant) != 6399:
        raise AssertionError(("incorrect certificate size", len(invariant)))
    for right in range(128):
        initial = encode(0, 4, 171 | (right << 11))
        if initial not in invariant:
            raise AssertionError(("missing initial state", right))
    marker_count = 0
    transitions = 0
    for encoded in invariant:
        state = encoded & 7
        offset = (encoded >> 3) & 31
        head = offset - 10
        tape = encoded >> 8
        if not (-9 <= head <= 7 and 0 <= state <= 5 and tape < 1 << 18):
            raise AssertionError(("bad encoding", encoded))
        scanned = (tape >> offset) & 1
        if head == -9:
            marker_count += 1
            if (state, scanned) != (2, 1):
                raise AssertionError(("unsafe marker contact", encoded))
            continue
        if (state, scanned) == (5, 1):
            continue  # First entry to undefined F/1
        if state == 5 and scanned == 0 and tape & ((1 << offset) - 1) == 0:
            continue  # First physically blank-left F/0
        instruction = TABLE[state][scanned]
        if instruction is None:
            raise AssertionError(("undefined transition", encoded))
        write, direction, next_state = instruction
        new_tape = (tape | (1 << offset)) if write else (tape & ~(1 << offset))
        next_head = head + direction
        if next_head < -10:
            raise AssertionError(("fell off left window", encoded))
        destinations = (
            (encode(7, s, new_tape) for s in range(6))
            if next_head > 7
            else (encode(next_head, next_state, new_tape),)
        )
        for successor in destinations:
            transitions += 1
            if successor not in invariant:
                raise AssertionError(("invariant not closed", encoded, successor))
    if (marker_count, transitions) != (95, 7306):
        raise AssertionError(("certificate mismatch", marker_count, transitions))
    print("PASS: 6399-state E3 invariant; 128 seeds; 7306 edges; 95 safe marker contacts")


if __name__ == "__main__":
    verify()
