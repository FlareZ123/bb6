"""Validate synthetic halting configurations for the P1 BB6 reduction.

This experiment starts from P1(2,c), not the blank tape.
The unbounded theorem is independently proved in Packet.lean.
"""
from verify_p1 import RawMachine, next_hub


def critical(n: int) -> int:
    return 14 * (1 << n) - 2 * n - 10


def verify_macro(n: int) -> None:
    state = (2, critical(n))
    for i in range(2*n+1):
        state = next_hub(*state)
        assert state is not None, (n, i, "early halt")
    assert state[0] % 2 == 1 and state[1] == 2, (n, state)
    assert next_hub(*state) is None, n


def verify_raw(n: int, limit: int = 2_000_000) -> tuple[int, int]:
    raw = RawMachine()
    raw.ones.update(range(-2, 0))
    raw.ones.update(range(critical(n)))
    for t in range(limit):
        if not raw.tick():
            return t, len(raw.ones)
    raise RuntimeError(f"raw horizon exceeded for n={n}, limit={limit}")


if __name__ == "__main__":
    for n in range(8):
        verify_macro(n)
        steps, ones = verify_raw(n)
        print(f"n={n} c={critical(n)} defined_TM_steps={steps} final_ones={ones}")
