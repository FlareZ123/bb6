"""Tests proof-shaped #746 source-C multi-reset even-block witnesses."""
from random import Random
from verify_fast_sweep import bit_first_failure, bit_first_outcome


def at_height(k: int, m: int, d: int) -> int:
    return (8 << k) + k - (1 << m) * d


def block_valid(h: int, k: int, m: int, d: int) -> bool:
    return m > 0 and h == at_height(k, m, d) and d >= 2 * k + 6 and h >= 4 << k


def propose_block(h: int, cap: int) -> tuple[int, int, int, int] | None:
    k = bit_first_failure(h)
    p = 1 << k
    if h < 4 * p:
        return None
    a = 8 * p + k
    delta = a - h
    q = delta // (2 * k + 6)
    if q == 0:
        return None
    valuation = (delta & -delta).bit_length() - 1
    m = min(valuation, q.bit_length() - 1, cap)
    if not m:
        return None
    d = delta >> m
    assert block_valid(h, k, m, d)
    return k, m, d, at_height(k, 0, d)


def direct(h: int, count: int) -> int | None:
    for _ in range(count):
        if h is None:
            break
        h = bit_first_outcome(h)
    return h


def test() -> None:
    rng = Random(746042)
    for m in (1, 3, 10, 100, 1000):
        k = 2 * m + 10
        d = 4 * m + 26
        h = at_height(k, m, d)
        result = propose_block(h, m)
        assert result is not None and result[:3] == (k, m, d)
        assert direct(h, m) == result[3]
        print(f"PASS parameter-uniform family m={m}, k={k}, input_bits={h.bit_length()}")

    sampled = accepted = 0
    for bits in (10, 30, 100, 1000, 10000):
        for _ in range(100):
            h = rng.getrandbits(bits)
            result = propose_block(h, bits)
            sampled += 1
            if result:
                k, m, d, u = result
                assert block_valid(h, k, m, d)
                assert direct(h, m) == u
                assert not block_valid(h, k, m, d + 1)
                accepted += 1
    print(f"PASS {sampled} reproducible random inputs, {accepted} certified multi-step batches")

    n = 10000
    plain = direct(2, n)
    h, step, blocks, saved, max_block = 2, 0, 0, 0, 0
    while step < n:
        proposed = propose_block(h, n - step)
        if proposed is not None:
            k, m, d, h = proposed
            step += m
            blocks += 1
            saved += m - 1
            max_block = max(max_block, m)
        else:
            h = bit_first_outcome(h)
            step += 1
    assert h == plain
    print(f"PASS genuine C(2,0)-root trajectory for {n} resets, "
          f"{blocks} checked blocks, {saved} ordinary calls saved, "
          f"longest block={max_block}, final_bits={h.bit_length()}")


if __name__ == "__main__":
    test()
