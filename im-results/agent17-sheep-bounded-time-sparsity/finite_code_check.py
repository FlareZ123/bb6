"""Exact finite dyadic-cylinder regression for the Sheep generic first-even map.

No floating point, third-party dependencies, random data, or repository writes.
Finite tests only; README contains the all-parameter mathematical proof.
"""
from math import comb


def generic_step(x: int) -> tuple[int, int]:
    assert x > 0 and x % 2 == 0
    a = (x & -x).bit_length() - 1
    u = x >> a
    f = x + a + (u - 1) // 2
    z = f - 1
    h = (z & -z).bit_length() - 1
    return 1 + 3**h * (z >> h), a + h + 1


def iterate(x: int, steps: int) -> tuple[int, int]:
    cost = 0
    for _ in range(steps):
        x, c = generic_step(x)
        cost += c
    return x, cost


def check() -> None:
    checks = 0
    for p in range(5, 13):
        inputs = list(range(2, (1 << p) + 1, 2))
        for i in range(4):
            records = [iterate(x, i) for x in inputs]
            for R in range(1, p):
                m = p - R
                expensive = sum(cost > m for _, cost in records)
                tail_numer = (
                    sum(comb(m, j) for j in range(min(m, 2 * i - 1) + 1))
                    if i > 0
                    else 0
                )
                expected_expensive = tail_numer << (p - 1 - m)
                assert expensive == expected_expensive, (p, i, R, expensive, expected_expensive)
                low_cost_hits = sum(
                    cost <= m and (value % (1 << R) == 0)
                    for value, cost in records
                )
                assert low_cost_hits <= (1 << (p - R)), (p, i, R, low_cost_hits)
                checks += 1
        print(f"p={p}: complete 2^p residue enumeration passed")
    print(f"PASS exact finite coding identities, {checks} parameter checks")


if __name__ == "__main__":
    check()
