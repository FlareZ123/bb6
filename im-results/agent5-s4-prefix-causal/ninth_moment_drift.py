"""Source-prefix lower bound for the S4 positional moment D.

The nine-digit projected cycle is the source-aligned 81,920-return cycle from
ninth_gate_census.py. For a gate whose prefix carry stops before digit 9, its
D-increment is exact from that prefix. If it passes all nine digits, the
carry-moment identity gives a lower bound using t_0,...,t_8 and r >= 9.

This computes a conditional-on-survival lower bound for every P-return state
rooted at the source-certified return-5457 state. It does not simulate the
unknown suffix and is not a BB(6) proof.
"""

from ninth_digit_candidate import gp, pp
from ninth_gate_census import CYCLE_NINE, OFFSETS, PERIOD, weight

ROOT_5457 = (
    283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050,
    366446, 435688, 443554, 1702180, 1770018, 211301, 281569,
    35137, 35134,
)
PREFIX_LEN = len(CYCLE_NINE)


def v2(n: int) -> int:
    assert n > 0
    r = 0
    while n % 2 == 0:
        n //= 2
        r += 1
    return r


def gate_d_lower(prefix: tuple[int, ...], offset: int) -> int:
    """Lower bound for D(G(offset,S))-D(S), from the first nine digits only."""
    assert len(prefix) == PREFIX_LEN
    x = [digit + 1 for digit in prefix]
    r0 = min(v2(weight(prefix) + offset), PREFIX_LEN)
    t = x[0] + offset
    carries = [t]

    if r0 < PREFIX_LEN:
        for i in range(r0):
            assert t % 2 == 0
            t = x[i + 1] + t // 2
            carries.append(t)
        assert t % 2 == 1
        # Here the true carry depth is exactly r0.
        numerator = sum(carries) + 4 * r0 - 1
    else:
        # The true carry depth r is at least 9. We know t_0,...,t_8,
        # all even. The unknown t_9,...,t_r are positive, so
        # 2*DeltaD >= sum(t_0,...,t_8) + (r-8) + 4r - 1
        # >= sum(t_0,...,t_8) + 36.
        for i in range(PREFIX_LEN - 1):
            assert t % 2 == 0
            t = x[i + 1] + t // 2
            carries.append(t)
        assert len(carries) == PREFIX_LEN
        assert all(v % 2 == 0 for v in carries)
        numerator = sum(carries) + 36

    assert numerator % 2 == 0
    return numerator // 2


def positional_moment(stack: tuple[int, ...]) -> int:
    return sum(i * (digit + 1) for i, digit in enumerate(stack))


def mass(stack: tuple[int, ...]) -> int:
    return sum(digit + 1 for digit in stack)


def main() -> None:
    prefix = CYCLE_NINE
    partial = [0]
    for _ in range(PERIOD):
        stages = (
            prefix,
            gp(509, prefix),
            gp(290, gp(509, prefix)),
        )
        assert all(len(stage) == PREFIX_LEN for stage in stages)
        increment = sum(
            gate_d_lower(stage, offset)
            for stage, offset in zip(stages, OFFSETS)
        )
        partial.append(partial[-1] + increment)
        prefix = pp(prefix)

    assert prefix == CYCLE_NINE
    period_total = partial[-1]
    assert period_total == 754_974_720
    assert period_total == 9_216 * PERIOD

    residuals = [partial[j] - 9_216 * j for j in range(PERIOD + 1)]
    min_residual = min(residuals)
    max_residual = max(residuals)
    min_phase = residuals.index(min_residual)
    max_phase = residuals.index(max_residual)
    assert (min_residual, min_phase) == (-237_910, 20_629)
    assert (max_residual, max_phase) == (385_701, 26_422)

    d0 = positional_moment(ROOT_5457)
    m0 = mass(ROOT_5457)
    assert d0 == 66_584_055
    assert m0 == 5_590_215
    constant = d0 - 9 * m0 + min_residual
    assert constant == 16_034_210

    def lower_at(returns: int) -> int:
        cycles, phase = divmod(returns, PERIOD)
        return d0 + cycles * period_total + partial[phase]

    assert lower_at(317) == 69_747_896
    assert lower_at(25_685) == 303_196_944
    assert lower_at(929_375) == 8_631_857_984

    print("nine-prefix period:", PERIOD)
    print("lower D drift per period:", period_total)
    print("mean lower D drift per P-return:", period_total // PERIOD)
    print("partial residual min/max:", min_residual, max_residual)
    print("residual extremal phases:", min_phase, max_phase)
    print("root D0, M0:", d0, m0)
    print("uniform affine bound: D >= 9*M +", constant)
    print("D lower at returns 317, 25685, 929375:",
          lower_at(317), lower_at(25_685), lower_at(929_375))


if __name__ == "__main__":
    main()
