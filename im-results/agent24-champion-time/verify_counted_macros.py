"""Finite source-authentic raw-step trials for BusyCoq TM63's candidate counted macros.

Source: ccz181078/busycoq@3f302b87f5fb933c46e97672ffbb6907f373fb6e
verify/SOBCv5.v:10750-11283. Numerical formulas here are CONJECTURES.
"""
from random import Random

RULES = (
    ((1, 1, 1), None),
    ((1, -1, 2), (0, 1, 5)),
    ((1, 1, 4), (0, -1, 3)),
    ((0, -1, 2), (1, 1, 1)),
    ((1, 1, 0), (1, 1, 4)),
    ((1, 1, 4), (0, 1, 3)),
)


def lc(length, num):
    assert 0 <= num < 2**length
    return "".join("100" if (num >> bit) & 1 else "111"
                   for bit in range(length - 1, -1, -1))


def s1(length, n, marker, a, a1, b):
    """Exact published S1 finite support, modulo an overall tape shift.

    Crucial BusyCoq notation: l <{{D}} r reads hd(l) UNDER the head;
    the first digit of r is the right neighbor, not the current cell.
    """
    markerword = ("10", "101", "1011")[marker]
    left = "111011" + lc(length, n) + "100" + markerword + lc(a, a1)
    right = "0" + "11100" + "111" * (1 + b)
    head = len(left) - 1
    ones = {i - head for i, v in enumerate(left + right) if v == "1"}
    return (3, 0, ones)


def raw_run(conf, count):
    state, head, ones = conf
    ones = set(ones)
    for t in range(count):
        action = RULES[state][int(head in ones)]
        assert action is not None, f"premature halt at {t} / {count}"
        ink, direction, state = action
        if ink:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    return (state, 0, {p - head for p in ones})


def assert_reaches(start, steps, target):
    actual = raw_run(start, steps)
    assert actual == target, (
        start[:2], steps, actual[:2], target[:2],
        len(actual[2] ^ target[2])
    )


def val2(n):
    assert n >= 1
    z = 0
    while n % 2 == 0:
        z += 1
        n //= 2
    return z


def inc_cost(m, n, a, b):
    return 6*4**b + 42*2**b - 9*b + 15 + 4*m + 12*(a+val2(n))


def reset_core_cost(L, a, b):
    return 97 + 12*(L+a) + 3*b


def drain_cost(b):
    return 6*(4**b-1) + 42*(2**b-1) - 12*b


def reset_cost(L, a, b):
    return reset_core_cost(L, a, b) + drain_cost(b)


def assert_incs(L, n, m, a, b):
    outmarker = (m+2) % 3
    outa = a+b+(1 if m == 0 else 2)
    assert_reaches(
        s1(L, n, m, a, 0, b),
        inc_cost(m, n, a, b),
        s1(L, n-1, outmarker, outa, 0, 2**b-1),
    )


def assert_reset(L, a, b):
    n = (4*2**L-1)*2**a-1
    new_length = L+a+2
    start = s1(L, 0, 1, a, 0, b)
    middle = s1(new_length, n, 2, b, 2**b-1, 0)
    end = s1(new_length, n, 2, b, 0, 2**b-1)
    assert_reaches(start, reset_core_cost(L, a, b), middle)
    assert_reaches(middle, drain_cost(b), end)
    assert_reaches(start, reset_cost(L, a, b), end)


def assert_halting(L, a, b):
    state, head, ones = raw_run(s1(L, 0, 0, a, 0, b), 59+12*(L+a))
    assert RULES[state][int(head in ones)] is None


def main():
    assert_reaches((0, 0, set()), 27959, s1(3, 7, 2, 6, 0, 63))
    print("INIT: 27,959 exact nonhalting blank-root moves to published S1")

    rng = Random(20261103)
    ninc = 0
    for m in range(3):
        for L in range(1, 7):
            for n in range(1, min(2**L, 18)):
                for a in (0, 1, 3):
                    for b in range(5):
                        assert_incs(L, n, m, a, b)
                        ninc += 1
    for _ in range(160):
        m = rng.randrange(3)
        L = rng.randrange(1, 10)
        n = rng.randrange(1, 2**L)
        a = rng.randrange(8)
        b = rng.randrange(6)
        assert_incs(L, n, m, a, b)
        ninc += 1
    print(f"INC: {ninc} finite original-step trials")

    nreset = 0
    for L in range(6):
        for a in range(6):
            for b in range(7):
                assert_reset(L, a, b)
                nreset += 1
    print(f"RESET: {nreset} exact finite core/drain/composition trials")

    nhalt = 0
    for L in range(10):
        for a in range(10):
            for b in (0, 1, 7):
                assert_halting(L, a, b)
                nhalt += 1
    print(f"TERMINAL: {nhalt} finite halt-query trials")
    print("ALL FINITE TESTS PASS; these do not establish quantified formulas.")


if __name__ == "__main__":
    main()
