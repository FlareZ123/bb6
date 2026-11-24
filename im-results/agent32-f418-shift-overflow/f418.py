"""F418 exact arithmetic event evaluator; see README for its paper derivation.
Raw verification uses the literal transition table, blank-padded integer tapes.
"""
from random import Random
import argparse

TABLE = (
    ((1, 1, 1), (1, -1, 3)),
    ((1, 1, 2), (0, 1, 1)),
    ((1, -1, 0), (1, 1, 2)),
    ((1, -1, 4), (0, -1, 0)),
    ((1, -1, 5), None),
    ((1, -1, 2), None),
)
SEED = (3, 0, 1, 39464)


def ctz(n):
    assert n > 0
    return (n & -n).bit_length() - 1


def pack(d, N, a, n):
    L = sum(1 << (d + 5*i) for i in range(N.bit_length()) if (N >> i) & 1)
    R = 5 + 8*a + sum((1 + 2*((n >> i)&1)) << (4 + 2*i) for i in range(n.bit_length()))
    return (3, 0, L, R)


def raw_step(c):
    q, b, L, R = c
    t = TABLE[q][b]
    if t is None:
        return None
    v, move, q = t
    if move == 1:
        return q, R & 1, (L << 1) | v, R >> 1
    return q, L & 1, L >> 1, (R << 1) | v


def raw_run(c, k):
    for _ in range(k):
        c = raw_step(c)
        if c is None:
            return None
    return c


def increments_cost(x, n, z):
    return 40*z + 10*(x.bit_count()-(x+z).bit_count()) + 4*(n.bit_count()-(n+z).bit_count())


def event(d, N, a, n):
    """Return (next checkpoint or None, successful primitive steps).
    None denotes the live F/1 terminal query, not a successful halt step.
    """
    w = n.bit_length()
    t = (1 << w) - n
    assert n > 0 and 1 <= d <= 4 and a in (0, 1)
    if d == 3 or N == 0:
        assert N < n and (a == 0 or N == 0)
        assert a == 0 or t != (1 << (w-1))
        new = (2 if a == 0 else 4, N+t, 1-a, 1 << (w if a == 0 else w-1))
        return new, increments_cost(N, n, t) + (5 if a == 0 else -9)
    j = ctz(N)
    z = (1 << (j+1 if d == 4 else j)) - 1
    assert z < t
    cost = increments_cost(0, n, z)
    if d == 1:
        return None, cost + 5*j + 2
    Q = N >> (j+1)
    m = n+z
    if d == 2:
        e = (5*j+1)//2
        new = (3 if j % 2 == 0 else 2, Q, j % 2, (4*m+1+2*a) << e)
        return new, cost + 15*j + (14 if j % 2 == 0 else 21)
    assert d == 4
    e = (5*j+4)//2
    new = (1 if j % 2 == 0 else 2, Q, 1-j % 2, (4*m+1+2*a) << e)
    return new, cost + 15*j + (30 if j % 2 == 0 else 23)


def invariant(d, N, a, n):
    if n <= 0 or not (N < n):
        return False
    w = n.bit_length()
    t = (1 << w) - n
    if d == 3 or N == 0:
        return a == 0 or (N == 0 and t & (t-1) != 0)
    if d == 4:
        return a == 0 and n == t and N < t and N & (N-1) != 0
    return d in (1, 2) and N < t and t & (t-1) != 0 if d == 1 else d == 2 and N < t


def test():
    assert raw_run((0, 0, 0, 0), 670) == pack(*SEED)
    rng = Random(418)
    checked = 0
    for _ in range(5000):
        w = rng.randint(1, 9)
        n = rng.randrange(1 << (w-1), 1 << w)
        N = rng.randrange(0, 1 << w)
        d = rng.randint(1, 4)
        a = rng.randrange(2)
        try:
            nxt, cost = event(d, N, a, n)
        except AssertionError:
            continue
        c = raw_run(pack(d, N, a, n), cost)
        if nxt is None:
            assert c is not None and raw_step(c) is None
        else:
            assert c == pack(*nxt), (d, N, a, n, nxt, cost, c)
        checked += 1
    print(f"raw seed and {checked} synthetic event/cost comparisons passed")


def orbit(count):
    s = SEED
    steps = 670
    even4 = 0
    for i in range(count):
        assert invariant(*s), (i, s)
        if s[0] == 4 and ctz(s[1]) % 2 == 0:
            even4 += 1
        nxt, cost = event(*s)
        steps += cost
        if nxt is None:
            print(f"F/1 query at event {i+1}; successful steps={steps}; halt attempt={steps+1}")
            return
        s = nxt
    print(f"live after {count} events; d={s[0]}, a={s[2]}, N_bits={s[1].bit_length()}, n_bits={s[3].bit_length()}, successful_step_count_bits={steps.bit_length()}, even4={even4}")


def normal_return(N, W):
    """D2(N,1,2**W) -> next D2 phase-1 pure-power checkpoint.
    If no even-position bit occurs, return None and use the general event map.
    """
    assert 0 < N < (1 << W)
    C = E = 0
    while N:
        j = ctz(N)
        e = (5*j+1)//2
        C = (4*C + (1 << (j+2)) - 1) << e
        E += e+2
        N >>= j+1
        if j % 2 == 0:
            return (1 << (W+E)) + N-C, W+E+1
    return None


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--events", type=int, default=10000)
    args = p.parse_args()
    test()
    orbit(args.events)
