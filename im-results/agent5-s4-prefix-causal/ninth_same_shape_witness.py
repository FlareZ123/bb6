"""Construct equal-prefix, equal-mass, equal-length synthetic S4 gate failures.

This is a finite, deterministic source-shaped experiment. It starts at the
verified six-digit reduced S4 root, checks the source-certified 18-digit
checkpoint at return 5457, and examines 81920 subsequent returns. It outputs
first-G(509) synthetic gate completions, never a genuine-root halt.

The construction is elementary: for an L-digit suffix of mass m (L >= 3),
freeze the highest L-3 digit blocks to zero. Their total weight is 2**L-8.
For t=m-(L-3) and K=k+2**L-8, choose the first power p>=t+K+4.
If t>=K+8, then t+4<=p-K<3*t, realizable by three positive block masses
a0=t-r-q, a1=r, a2=q, where d=p-K-t, q=(d-1)//3, r=d-3*q.
"""

from collections import Counter

from ninth_gate_census import weight

ROOT = (301, 650, 645, 322, 163, 160)
STATE_5457 = (
    283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050,
    366446, 435688, 443554, 1702180, 1770018, 211301, 281569,
    35137, 35134,
)


def h(a: int, xs: tuple[int, ...]) -> tuple[int, ...] | None:
    out: list[int] = []
    i = 0
    while i < len(xs):
        b = xs[i]
        if a % 2 == 0:
            return tuple(out) + (a // 2 + 2, b + a // 2) + xs[i + 1:]
        out.append(a // 2)
        a = b + a // 2 + 1
        i += 1
    while a % 2:
        if a <= 1:
            return None
        out.append(a // 2)
        a //= 2
    if a == 0:
        return None
    return tuple(out) + (a // 2 + 2, a // 2 - 1)


def g(c: int, xs: tuple[int, ...]) -> tuple[int, ...] | None:
    if not xs:
        return h(c - 1, ())
    return h(xs[0] + c, xs[1:])


def p_step(xs: tuple[int, ...]) -> tuple[int, ...] | None:
    for c in (509, 290, 219):
        xs = g(c, xs)
        if xs is None:
            return None
    return xs


def mass(xs: tuple[int, ...]) -> int:
    return sum(digit + 1 for digit in xs)


def same_shape_suffix(prefix: tuple[int, ...], length: int, m: int) -> tuple[int, ...]:
    assert len(prefix) == 9
    assert length >= 3
    a = weight(prefix) + 509
    assert a % 512 == 0
    k = a // 512
    t = m - (length - 3)
    effective_k = k + (1 << length) - 8
    assert t >= max(10, effective_k + 8)
    lo = t + effective_k + 4
    power = 1 << (lo - 1).bit_length()
    assert lo <= power < 3 * t + effective_k
    d = power - effective_k - t
    q = (d - 1) // 3
    r = d - 3 * q
    a0 = t - q - r
    assert a0 >= 1 and q >= 1 and 1 <= r <= 3
    suffix = (a0 - 1, r - 1, q - 1) + (0,) * (length - 3)
    assert len(suffix) == length and mass(suffix) == m
    assert weight(suffix) + k == power
    return suffix


def main() -> None:
    state = ROOT
    for _ in range(5457):
        state = p_step(state)
        assert state is not None
    assert state == STATE_5457

    count = 0
    lens: Counter[int] = Counter()
    smallest_margin = 10**30
    first_witness: tuple[int, tuple[int, ...]] | None = None
    for phase in range(81920):
        assert state is not None and len(state) >= 9
        prefix = state[:9]
        if (weight(prefix) + 509) % 512 == 0:
            length = len(state) - 9
            original_suffix_mass = mass(state[9:])
            synthetic_suffix = same_shape_suffix(prefix, length, original_suffix_mass)
            synthetic = prefix + synthetic_suffix
            assert len(synthetic) == len(state)
            assert mass(synthetic) == mass(state)
            assert synthetic[:9] == state[:9]
            assert g(509, synthetic) is None
            assert g(509, state) is not None
            count += 1
            lens[length] += 1
            k = (weight(prefix) + 509) // 512
            smallest_margin = min(smallest_margin, original_suffix_mass - k)
            if first_witness is None:
                first_witness = (phase, synthetic_suffix)
        state = p_step(state)
        assert state is not None

    assert count == 118
    assert lens == Counter({9: 38, 13: 80})
    assert smallest_margin == 5770295
    print("Original S4 root through 5457+81920 successful returns: model-simulated")
    print("First-G(509) candidate phases with same-mass, same-length synthetic halt:", count)
    print("Original suffix lengths:", dict(lens))
    print("Minimum remaining-mass minus k:", smallest_margin)
    print("First synthetic suffix witness (relative phase, digits):", first_witness)
    print("These are synthetic completions, not authentic-root halts.")


if __name__ == "__main__":
    main()
