"""Exact bounded-valuation inverse grammar for Sheep even halting powers.

The all-h valuation cutoff is proved in UniformValuationGap.lean, with
published signed-power residue gap in Agent40/ResidueGap.lean.
"""


def two_power_ge(exponent: int, lower_bound: int) -> bool:
    """Compare 2**exponent >= lower_bound without constructing 2**exponent."""
    return (lower_bound <= 0 or exponent >= lower_bound.bit_length()
            or (exponent == lower_bound.bit_length() - 1
                and (lower_bound & (lower_bound - 1)) == 0))


def h_max(exponent: int) -> int:
    """v3(2**exponent-1), by elementary lifting-the-exponent."""
    assert exponent >= 1
    if exponent % 2:
        return 0
    h, j = 1, exponent
    while j % 3 == 0:
        j //= 3
        h += 1
    return h


def parent_signatures(exponent: int) -> list[tuple[int, int]]:
    """All (odd-run length, source 2-valuation) for true even E parents."""
    assert exponent >= 1
    matches = []
    for h in range(h_max(exponent) + 1):
        for a in range(1, (2*h+2 if h else 1) + 1):
            denominator = 3**h * (2**(a+1) + 1)
            adjustment = 3**h*(2*a-3) + 2**(h+1)
            e = exponent+h+1
            if (pow(2, e, denominator) == adjustment % denominator
                    and two_power_ge(e, 5*denominator + adjustment)):
                matches.append((h, a))
    return matches


def exact_parents(exponent: int) -> dict[int, tuple[int, int]]:
    """Compute full legal even source set, for tractable integer exponents."""
    result = {}
    for h, a in parent_signatures(exponent):
        denominator = 3**h * (2**(a+1) + 1)
        adjustment = 3**h*(2*a-3) + 2**(h+1)
        v, remainder = divmod((1 << (exponent+h+1)) - adjustment, denominator)
        assert remainder == 0 and v >= 5 and v % 2 == 1
        x = (1 << a) * v
        assert x not in result
        result[x] = (h, a)
    return result


def even_return(x: int) -> int:
    a = (x & -x).bit_length() - 1
    v = x >> a
    assert a >= 1 and v >= 3 and v % 2 == 1
    f = x+a+(3 if v == 3 else (v-1)//2)
    h = ((f-1)&-(f-1)).bit_length()-1
    return 1+3**h*((f-1)>>h)


def slow_incoming(exponent: int) -> dict[int, tuple[int, int]]:
    y = 1 << exponent
    ans = {}
    for h in range(h_max(exponent)+1):
        assert (y-1) % (3**h) == 0
        f = 1 + (1<<h) * ((y-1)//3**h)
        for a in range(1, exponent+3):
            m = (1 << (a+1)) + 1
            v, rem = divmod(2*f-2*a+1,m)
            if rem == 0 and v >= 5 and v%2 == 1:
                x = (1<<a)*v
                assert even_return(x)==y
                ans[x]=(h,a)
            x = 3 << a
            if x>0 and x not in ans and even_return(x)==y:
                ans[x]=(h,a)
    return ans


def test() -> None:
    cases = 0
    for j in range(1,1001):
        fast = exact_parents(j)
        slow = slow_incoming(j)
        assert fast == slow, (j,fast,slow)
        cases += 1
    print(f"Complete inverse equality PASS for {cases} power exponents")
    for j in (18,36,54,72,108,126,162,486,10**8,10**100):
        sig = parent_signatures(j)
        print(f"j={str(j)[:35]} {'...' if j>=10**36 else ''}: hmax={h_max(j)}, signatures={sig}")

if __name__ == "__main__":
    test()
