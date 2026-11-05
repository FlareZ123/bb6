"""Deterministic single-file tester of uniform synthetic BB429 3-adic coverage.

Only modular arithmetic is used for astronomically large halting seed formulas.
Their full twelve-branch finite samples are checked by ResidueThreeTwoBurstSFT.cjs.
"""


def f_mod(kind: str, n: int, e: int) -> int:
    if e == 0:
        return 0
    modulus = 3**e
    if kind == 'G2':
        return (4 * pow(2, n, modulus) - n) % modulus
    if kind == 'G1':
        return (pow(16, n, modulus) - n) % modulus
    if kind == 'H0':
        period = 2 * 3 ** (e - 1)
        exponent = (4 * pow(2, n, period) + n - 10) % period
        return (4 * pow(2, exponent, modulus) - 8 * pow(2, n, modulus) + 13 - n) % modulus
    raise ValueError('Unknown family')


def lift(kind: str, e: int, target: int) -> int:
    n = 2 if kind == 'H0' else 1
    for exponent in range(e):
        period = 2 * 3**exponent
        modulus = 3 ** (exponent + 1)
        choices = [n + t * period for t in range(3)]
        matches = [q for q in choices if f_mod(kind, q, exponent + 1) == target % modulus]
        assert len(matches) == 1, (kind, e, target, exponent, choices, matches)
        n = matches[0]
    assert f_mod(kind, n, e) == target % (3**e)
    minimum = 2 if kind == 'H0' else 1
    assert minimum <= n <= minimum + 2 * (3**e - 1)
    return n


def synthetic_start_mod(e: int, residue: int) -> tuple[str, int, int]:
    assert e >= 1
    modulus = 3**e
    r = residue % modulus
    lower = 3 ** (e - 1)
    if r % 3 == 2:
        family = 'G2'
        parameter = lift(family, e - 1, (r + 13) // 3)
        w_mod = (3 * f_mod(family, parameter, e - 1) - 13) % modulus
    elif r % 3 == 1:
        family = 'G1'
        target = (((r + 29) // 3) * pow(8, -1, lower)) % lower if lower > 1 else 0
        parameter = lift(family, e - 1, target)
        w_mod = (24 * f_mod(family, parameter, e - 1) - 29) % modulus
    else:
        family = 'H0'
        parameter = lift(family, e - 1, r // 3)
        w_mod = (3 * f_mod(family, parameter, e - 1)) % modulus
    assert w_mod == r, (e, r, family, parameter, w_mod)
    return family, parameter, w_mod


def main() -> None:
    for e in range(1, 8):
        modulus = 3**e
        families = {'G1': 0, 'G2': 0, 'H0': 0}
        for r in range(modulus):
            family, _, _ = synthetic_start_mod(e, r)
            families[family] += 1
        assert sum(families.values()) == modulus
        print('PASS complete 3-adic modulus', modulus, families)
    for e in range(8, 13):
        modulus = 3**e
        for t in range(100):
            synthetic_start_mod(e, (201326585 + 1087 * e + 17011 * t) % modulus)
        print('PASS high-power sample modulus', modulus, '100 deterministic target residues')
    print('All finite modular checks passed. The published induction is the universal proof.')


if __name__ == '__main__':
    main()
