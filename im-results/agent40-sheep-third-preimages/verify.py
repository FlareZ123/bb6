"""Finite checks for the Sheep Machine's depth-three inverse theorem.

Finite testing supports the independently proved uniform modular argument.
"""
RESIDUES = (24, 48, 96, 120, 168)

def F(t: int) -> int | None:
    assert t >= 3
    a = (t & -t).bit_length() - 1
    u = t >> a
    if u == 1:
        return None
    if u == 3:
        return t + a + 3
    return t + a + (u - 1) // 2

def inverse(y: int) -> tuple[int, ...]:
    parents = set()
    for a in range(y.bit_length() + 1):
        special = 3 << a
        if F(special) == y:
            parents.add(special)
        n = 2 * y - 2 * a + 1
        mod = (1 << (a + 1)) + 1
        u, remainder = divmod(n, mod)
        if remainder == 0 and u >= 5 and u & 1:
            t = u << a
            assert F(t) == y
            parents.add(t)
    return tuple(sorted(parents))

def run() -> None:
    count = 0
    for j in range(24, 1201):
        if j % 216 not in RESIDUES:
            continue
        p = ((1 << (j + 1)) + 1) // 3
        x = ((1 << (j + 2)) + 5) // 9
        assert inverse(1 << j) == (p,)
        assert inverse(p) == (x,)
        assert inverse(x) == ()
        assert F(p) == (1 << j)
        assert F(x) == p
        count += 1
    print("PASS", count, "exponents through 1200, exact complete inverse enumeration")

    for q in range(100):
        for r in RESIDUES:
            j = r + 216 * q
            assert pow(2, j + 1, 5) != 1
            assert pow(2, j + 2, 5) != 1
            assert pow(2, j + 2, 27) != 7
            assert pow(2, j + 2, 17) != 13
            assert pow(2, j + 3, 27) != 8
            assert pow(2, j + 3, 5) not in (1, 4)
            assert pow(2, j + 3, 81) != 17
            assert pow(2, j + 3, 17) != 1
    assert all(pow(2, e, 11) != 8 for e in range(0, 100, 2))
    assert all(pow(2, e, 11) != 9 for e in range(1, 100, 2))
    print("PASS 500 modular instances and parity gates")

if __name__ == "__main__":
    run()
