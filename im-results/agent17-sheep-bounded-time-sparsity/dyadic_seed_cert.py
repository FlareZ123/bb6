"""Fail-closed low-bits certificate for finite genuine Sheep even-return survival.

Requires Python 3.10+ standard library. No external files, network, or writes.
An accepted certificate implies the positive source avoids both u=1 (halt) and
u=3 (exception) through every inspected state. It makes no infinite claim.

Mathematical justification is in README.md, 'Deterministic seed certificate'.
"""
from dataclasses import dataclass
from random import Random


@dataclass(frozen=True)
class Certificate:
    accepted: bool
    returns: int
    precision_left: int
    cost: int
    reason: str


def trailing_zeros(value: int) -> int:
    return (value & -value).bit_length() - 1


def generic_residue_step(low: int, precision: int) -> tuple[int, int, int]:
    """Return (next low bits, remaining precision, branch cost).

    Requires low to be a nonzero even residue mod 2^precision. Missing branch
    bits raise ValueError; no guessed branch is ever accepted.
    """
    if low == 0 or (low & 1):
        raise ValueError("source valuation unavailable or parity wrong")
    a = trailing_zeros(low)
    qprecision = precision - a - 1
    if qprecision < 1:
        raise ValueError("insufficient bits for odd-block valuation")

    u = low >> a
    d = (1 << (a + 1)) + 1
    numerator = d * u + 2 * a - 3
    assert numerator % 2 == 0
    f_minus_one = (numerator // 2) & ((1 << qprecision) - 1)
    if f_minus_one == 0:
        raise ValueError("odd-block valuation exceeds known bits")

    h = trailing_zeros(f_minus_one)
    cost = a + h + 1
    remaining = precision - cost
    if remaining < 1:
        raise ValueError("no output precision remains")
    modulus = 1 << remaining
    next_low = (1 + pow(3, h, modulus) * (f_minus_one >> h)) % modulus
    return next_low, remaining, cost


def certify_prefix(x: int, r: int, precision: int, returns: int) -> Certificate:
    """Prove no genuine halt or exceptional cofactor for returns+1 source states.

    x is an exact positive even initial counter-section value. A certificate
    accepts only when x>=2^r and every generic output remains nonzero mod
    2^(r-1) using the specified initial binary precision.
    """
    if x < 10 or x % 2 or r < 2 or precision < r or returns < 0:
        raise ValueError("need even x>=10, r>=2, precision>=r, returns>=0")
    if x < (1 << r):
        raise ValueError("initial size floor not satisfied")

    low = x & ((1 << precision) - 1)
    total_cost = 0
    guard = (1 << (r - 1)) - 1
    for i in range(returns + 1):
        if precision < r - 1:
            return Certificate(False, i, precision, total_cost, "precision exhausted")
        if (low & guard) == 0:
            return Certificate(False, i, precision, total_cost, "possible u=1 or u=3 state")
        if i == returns:
            return Certificate(True, i, precision, total_cost, "generic and nonterminal through this state")
        try:
            low, precision, cost = generic_residue_step(low, precision)
        except ValueError as exc:
            return Certificate(False, i, precision, total_cost, str(exc))
        total_cost += cost
    raise AssertionError("unreachable")


def actual_even_step(x: int) -> int:
    """Independent full-integer authentic section step for the self-test only."""
    a = trailing_zeros(x)
    u = x >> a
    if u == 1:
        raise ValueError("terminal")
    f = x + a + (3 if u == 3 else (u - 1) // 2)
    z = f - 1
    h = trailing_zeros(z)
    return 1 + 3**h * (z >> h)


def self_test() -> None:
    random = Random(20261109)
    for case in range(8):
        x = (random.getrandbits(512) | (1 << 511)) & ~1
        certificate = certify_prefix(x, r=16, precision=512, returns=40)
        assert certificate.accepted, certificate
        precision = 512
        low = x
        real = x
        for _ in range(40):
            low, precision, _ = generic_residue_step(low, precision)
            real = actual_even_step(real)
            assert low == real % (1 << precision)
        print(f"case={case} PASS cost={certificate.cost} remaining={certificate.precision_left}")
    assert not certify_prefix(1 << 20, 16, 512, 2).accepted
    assert not certify_prefix(3 << 20, 16, 512, 2).accepted
    print("PASS 8 exact full-source trajectories and 2 fail-closed exceptional inputs")


if __name__ == "__main__":
    self_test()
