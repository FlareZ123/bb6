"""Deterministic differential tests of the #746 source-C first-reset accelerator."""

from random import Random
from time import perf_counter_ns


def source_step(a: int, b: int) -> tuple[int, int] | None:
    if b == 0:
        return 2, 2 * a + 1
    if b == 1:
        return None
    d = b - 2
    if d >= 2 * a:
        return 2 * a + 2, d - 2 * a
    q = 6 * a + d + (5 if d & 1 else 8)
    return q // 4, q % 4


def source_first_outcome(h: int) -> int | None:
    state = (h, 0)
    while True:
        state = source_step(*state)
        if state is None:
            return None
        if state[1] == 0:
            return state[0]


def scan_first_failure(h: int) -> int:
    k = 0
    while h + k + 5 >= 8 << k:
        k += 1
    return k


def bit_first_failure(h: int) -> int:
    k = (h + 5).bit_length() - 3
    return k + (h + k + 5 >= 8 << k)


def bit_first_outcome(h: int) -> int | None:
    k = bit_first_failure(h)
    if h + k + 4 == 4 << k:
        return None
    if (h + k) % 2 == 0:
        return (4 << k) + (h + k) // 2
    x = (4 << k) + (h + k) // 2 + 3
    t = (x & -x).bit_length() - 1
    odd = x >> t
    return (3 ** (t + 1) * odd - 5) // 2


def verify() -> None:
    r = Random(746)
    for h in range(100000):
        assert bit_first_failure(h) == scan_first_failure(h), h
        if h < 10000:
            assert bit_first_outcome(h) == source_first_outcome(h), h
    print("PASS first-failed sweep for all 100000 small h")
    print("PASS first-reset Outcome against actual Cstep for all 10000 small h")
    for nbits in (10, 25, 50, 100, 250, 1000, 10000):
        for _ in range(50):
            h = r.getrandbits(nbits)
            assert bit_first_failure(h) == scan_first_failure(h), (nbits, h)
    print("PASS 350 deterministic random large integer sweep comparisons")
    for nbits in (1024, 8192, 65536):
        h = r.getrandbits(nbits)
        count = 12
        a = perf_counter_ns()
        for _ in range(count):
            scan_first_failure(h)
        b = perf_counter_ns()
        for _ in range(count):
            bit_first_failure(h)
        c = perf_counter_ns()
        print(f"benchmark bits={nbits}: scan_ms={(b-a)/count/1e6:.3f}, fast_ms={(c-b)/count/1e6:.3f}, speedup={(b-a)/(c-b):.1f}x")


if __name__ == "__main__":
    verify()
