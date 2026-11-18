#!/usr/bin/env python3
"""Reproduce the positive-z q4 first-cycle S0-drain splice checks.

No third-party packages are required.  For z <= 3 the middle S0 drain is
simulated directly.  For z >= 4 it is replaced by its *predicted* generic
S0-drain endpoint (left d1^a and a symbolic right unary interval); the short
postlude is then simulated.  The latter is an endpoint-splice test, not a
direct simulation of the enormous middle phase.

Run:
    python3 q4_s0_drain_splice_check.py
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Optional


D0 = (0, 0, 1)
D1 = (1, 1, 1)
LH = (1, 1, 0, 1, 1, 1)
RIGHT0 = (0, 1, 1, 1, 0, 0, 1, 1, 1)

# (write_bit, head_move, next_state); None denotes the halting transition.
TRANSITIONS = {
    (0, 0): (1, 1, 1),
    (0, 1): None,
    (1, 0): (1, -1, 2),
    (1, 1): (0, 1, 5),
    (2, 0): (1, 1, 4),
    (2, 1): (0, -1, 3),
    (3, 0): (0, -1, 2),
    (3, 1): (1, 1, 1),
    (4, 0): (1, 1, 0),
    (4, 1): (1, 1, 4),
    (5, 0): (1, 1, 4),
    (5, 1): (0, 1, 3),
}


def bin_dec(width: int, value: int) -> list[int]:
    """The repository's head-facing BinDec convention."""
    p = 2 ** (width + 1) - 1 - value
    out: list[int] = []
    for _ in range(width):
        if p <= 1:
            break
        out.extend(D0 if p % 2 == 0 else D1)
        p //= 2
    return out


def rle(bits: list[int]) -> list[tuple[int, int]]:
    if not bits:
        return []
    out: list[tuple[int, int]] = []
    bit = bits[0]
    count = 0
    for item in bits:
        if item == bit:
            count += 1
        else:
            out.append((bit, count))
            bit, count = item, 1
    out.append((bit, count))
    return out


@dataclass
class SparseTape:
    """Finite support plus at most one all-one interval and zero exceptions."""

    ones: set[int] = field(default_factory=set)
    interval: Optional[tuple[int, int]] = None
    exceptions: set[int] = field(default_factory=set)

    def read(self, position: int) -> int:
        if self.interval is not None:
            lo, hi = self.interval
            if lo <= position <= hi:
                return 0 if position in self.exceptions else 1
        return int(position in self.ones)

    def write(self, position: int, value: int) -> None:
        value = int(bool(value))
        if self.interval is not None:
            lo, hi = self.interval
            if lo <= position <= hi:
                if value:
                    self.exceptions.discard(position)
                else:
                    self.exceptions.add(position)
                return
        if value:
            self.ones.add(position)
        else:
            self.ones.discard(position)

    def add_one_interval(self, lo: int, hi: int) -> None:
        assert lo <= hi
        self.ones = {p for p in self.ones if not (lo <= p <= hi)}
        self.interval = (lo, hi)
        self.exceptions.clear()


@dataclass
class Machine:
    tape: SparseTape
    state: int = 3
    head: int = 0
    steps: int = 0

    def step(self) -> None:
        read = self.tape.read(self.head)
        transition = TRANSITIONS[(self.state, read)]
        if transition is None:
            raise RuntimeError(f"machine halted at step {self.steps}, head {self.head}")
        write, move, next_state = transition
        self.tape.write(self.head, write)
        self.head += move
        self.state = next_state
        self.steps += 1

    def run(self, count: int) -> None:
        for _ in range(count):
            self.step()

    def run_to_first_q4_checkpoint(self, limit: int = 1_000_000) -> None:
        for _ in range(limit + 1):
            if self.state == 4 and self.head == 1 and self.tape.read(self.head) == 0:
                return
            self.step()
        raise RuntimeError("first q4 checkpoint not reached within limit")


def initial_machine(A: int, L: int, z: int) -> tuple[Machine, int, int]:
    assert A >= 1 and L >= 0 and 0 < z < 2**A
    width = A + L + 2
    M = 2**A * (2 ** (L + 2) - 1)
    # markerWord(1) = [1,0,1].
    left = bin_dec(A, z) + [1, 0, 1] + [0, 0, 1] + [1] * (3 * L) + list(LH)

    tape = SparseTape()
    for i, bit in enumerate(left):
        if bit:
            tape.write(-i, bit)
    for i, bit in enumerate(RIGHT0):
        if bit:
            tape.write(1 + i, bit)
    return Machine(tape), width, M


def check_left_frame(machine: Machine, width: int, M: int, checkpoint: int) -> None:
    expected = [0, 1, 1] + bin_dec(width, M - checkpoint) + list(LH)
    expected_support = {
        1 - i for i, bit in enumerate(expected) if bit
    }
    actual_support = {p for p in machine.tape.ones if p <= 1}
    assert actual_support == expected_support, (
        f"left frame mismatch at checkpoint {checkpoint}"
    )


def check_checkpoint1_right_tail(machine: Machine, z: int) -> None:
    right_positions = [p for p in machine.tape.ones if p > 1]
    assert right_positions
    max_right = max(right_positions)
    actual = rle([machine.tape.read(p) for p in range(2, max_right + 5)])
    expected = [
        (0, 3),
        (1, 3 * z + 5),
        (0, 2),
        (1, 3 * 2**z),
        (0, 4),
    ]
    assert actual == expected, (actual, expected)


def check_s0_input(machine: Machine, z: int, a: int, N: int, h: int) -> None:
    assert machine.state == 3 and machine.head == h
    assert bin_dec(a, N) == list(D0) * a
    for i in range(3 * a):
        assert machine.tape.read(h - i) == D0[i % 3]
    for i, bit in enumerate(RIGHT0):
        assert machine.tape.read(h + 1 + i) == bit
    assert not any(p > h + 9 for p in machine.tape.ones)

    # The residual left context begins with 1^(3z+7), then a zero.
    tail_start = h - 3 * a
    for i in range(3 * z + 7):
        assert machine.tape.read(tail_start - i) == 1
    assert machine.tape.read(tail_start - (3 * z + 7)) == 0


def check_predicted_drain_output(
    machine: Machine, a: int, h: int, N: int, expected_ones: Optional[set[int]] = None
) -> None:
    assert machine.state == 3 and machine.head == h
    for i in range(3 * a):
        assert machine.tape.read(h - i) == 1
    for i, bit in enumerate((0, 1, 1, 1, 0, 0)):
        assert machine.tape.read(h + 1 + i) == bit

    lo = h + 7
    hi = h + 6 + 3 * (N + 1)
    if expected_ones is not None:
        assert machine.tape.interval is None
        assert machine.tape.ones == expected_ones
    else:
        assert machine.tape.interval == (lo, hi)
        assert not machine.tape.exceptions
        assert not any(p > hi for p in machine.tape.ones)


def install_predicted_drain_output(machine: Machine, a: int, h: int, N: int) -> None:
    for i in range(3 * a):
        machine.tape.write(h - i, 1)
    lo = h + 7
    hi = h + 6 + 3 * (N + 1)
    machine.tape.add_one_interval(lo, hi)
    machine.state = 3
    machine.head = h


def check_checkpoint2_right_tail(machine: Machine, h: int, a: int) -> None:
    lo = h + 7
    hi = h + 6 + 3 * 2**a
    assert machine.tape.interval == (lo, hi)
    assert not machine.tape.exceptions

    for p in (2, 3, 4, h + 5, h + 6):
        assert machine.tape.read(p) == 0
    for p in range(5, h + 5):
        assert machine.tape.read(p) == 1
    assert not any(p > 1 and not (5 <= p <= h + 4) for p in machine.tape.ones)
    for p in range(hi + 1, hi + 5):
        assert machine.tape.read(p) == 0


def check_case(A: int, L: int, z: int) -> dict[str, object]:
    machine, width, M = initial_machine(A, L, z)
    machine.run_to_first_q4_checkpoint()
    cp1 = machine.steps
    check_left_frame(machine, width, M, 1)
    check_checkpoint1_right_tail(machine, z)

    a = 2**z - 1
    N = 2**a - 1
    P = 3 * 2**z + 3 * z + 58
    h = 3 * 2**z + 3 * z + 7
    Q = 9 * 2**z + 9 * z + 16
    D = 6 * 4**a + 42 * 2**a - 12 * a - 48

    machine.run(P)
    check_s0_input(machine, z, a, N, h)
    input_ones = set(machine.tape.ones)

    if z <= 3:
        machine.run(D)
        assert machine.state == 3 and machine.head == h
        expected_ones = set(input_ones)
        expected_ones.update(h - i for i in range(3 * a))
        expected_ones.update(h + 7 + i for i in range(3 * 2**a))
        check_predicted_drain_output(machine, a, h, N, expected_ones)
        machine.tape.add_one_interval(h + 7, h + 6 + 3 * 2**a)
        drain_mode = "direct"
    else:
        install_predicted_drain_output(machine, a, h, N)
        check_predicted_drain_output(machine, a, h, N)
        machine.steps += D
        drain_mode = "endpoint-splice"

    machine.run(Q)
    assert machine.state == 4 and machine.head == 1
    assert machine.tape.read(1) == 0
    check_left_frame(machine, width, M, 2)
    check_checkpoint2_right_tail(machine, h, a)

    return {
        "A": A,
        "L": L,
        "z": z,
        "checkpoint1_step": cp1,
        "prefix_P": P,
        "head_h": h,
        "counter_width_a": a,
        "counter_value_N": N,
        "drain_D": D,
        "drain_mode": drain_mode,
        "postlude_Q": Q,
        "checkpoint2_step": machine.steps,
        "cycle_cost": P + D + Q,
        "left_frame_and_right_tail": "pass",
    }


def main() -> None:
    cases = [(3, 2, z) for z in range(1, 6)]
    cases += [(4, 2, 2), (2, 4, 2), (3, 4, 2), (4, 2, 3), (3, 4, 3)]
    for A, L, z in cases:
        print(json.dumps(check_case(A, L, z), sort_keys=True))


if __name__ == "__main__":
    main()
