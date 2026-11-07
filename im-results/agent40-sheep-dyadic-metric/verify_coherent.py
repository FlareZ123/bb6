"""Exact finite coherent-witness audit for the dyadic Sheep metric theorem.

Constructs one arbitrarily large positive integer for each exact-k quotient
endpoint via a lifted inverse word. Verifies every actual consecutive
first-even return and the prescribed (a,h) valuations. Finite test only.
"""
from verify_eccentricity import word, quotient_graph, v2


def inverse_parent(precision: int, a: int, h: int, target: int) -> int:
    modulus = 1 << (precision - a)
    return ((1 << a) * pow(1 + (1 << (a + 1)), -1, modulus) *
            (3 - 2*a + (1 << (h + 1)) *
             pow(3**h, -1, modulus)*(target-1))) % (1 << precision)


def coherent_start(p: int, prefix: list[tuple[int, int]], s: int) -> tuple[int, int]:
    precision = p
    x = s
    for a, h in reversed(prefix):
        precision += a+h+1
        x = inverse_parent(precision, a, h, x)
    return x + (1 << precision)*10000, precision


def first_even(x: int) -> tuple[int, int, int]:
    a = v2(x)
    u = x >> a
    assert u >= 5 and u%2 == 1
    f = x+a+(u-1)//2
    h = v2(f-1)
    v = (f-1) >> h
    assert v >= 5 and v%2 == 1
    nxt = 1 + 3**h*v
    assert nxt%2 == 0 and nxt > x
    return a, h, nxt


def test(max_p: int = 8) -> None:
    total = 0
    for p in range(1, max_p+1):
        graph = quotient_graph(p)
        tested = 0
        for r in graph:
            letters = word(p,r)
            cost = 0
            for k in range(1, len(letters)+1):
                a,h = letters[k-1]
                cost += a+h+1
                t = p-cost
                tail = 0
                for aa,hh in reversed(letters[k:]):
                    tail = inverse_parent(t, aa, hh, tail)
                for s in graph:
                    if s%(1 << t) != tail:
                        continue
                    x, precision = coherent_start(p, letters[:k], s)
                    assert x%(1 << p) == r
                    big_shift = 1 << precision
                    shifted_x = x+big_shift
                    alpha = 1
                    for aa,hh in letters[:k]:
                        a1,h1,x = first_even(x)
                        a2,h2,shifted_x = first_even(shifted_x)
                        assert (a1,h1) == (a2,h2) == (aa,hh)
                        alpha *= (3**hh)*(1+(1 << (aa+1)))
                    assert x%(1 << p) == shifted_x%(1 << p) == s
                    assert shifted_x-x == alpha*(1 << p)
                    tested += 1
        total += tested
        print(f"PASS coherent p={p}: {tested} exact-prefix trajectories",flush=True)
    print(f"PASS {total} full single-integer trajectories",flush=True)


if __name__ == "__main__":
    test()
