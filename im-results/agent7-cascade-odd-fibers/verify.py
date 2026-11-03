"""Independent exact-symbolic verifier of the #746 cascade odd-fiber theorem.

The first transition layer directly transcribes DeepMind's C/P accelerated next.
The second layer eliminates the P sweeps algebraically and is independently
cross-checked against the first for bounded synthetic configurations.
Neither layer assumes that the chosen inverse source is blank reachable.
"""
from __future__ import annotations


def source_next(s: tuple[str, int, int, int]):
    typ, a, b, c = s
    if typ == "C":
        if b == 0:
            return ("C", 2, 2*a+1, 0)
        if b == 1:
            return None
        return ("P", a, 0, b)
    if a == 0:
        if c == 0:
            return ("C", b+1, 2, 0)
        if c == 1:
            return ("C", b+1, 0, 0)
        return ("C", b+2, c-2, 0)
    if c == 0:
        return ("P", a-1, b+1, 2)
    if c == 1:
        return ("P", a-1, b+1, 0)
    return ("P", a-1, b+2, c-2)


def c_episode(a: int, b: int):
    state = ("C", a, b, 0)
    for _ in range(100000):
        state = source_next(state)
        if state is None:
            return None
        if state[0] == "C":
            return (state[1], state[2])
    raise AssertionError("C-episode exceeded conservative source bound")


def c_step(a: int, b: int):
    if b == 0:
        return (2, 2*a+1)
    if b == 1:
        return None
    d = b-2
    if d >= 2*a:
        return (2*a+2, d-2*a)
    z = 6*a+d+(8 if d % 2 == 0 else 5)
    return (z//4, z%4)


def first_reset(h: int):
    a, b = h, 0
    for count in range(20000):
        s = c_step(a, b)
        if s is None:
            return None, count+1
        a, b = s
        if b == 0:
            return a, count+1
    raise AssertionError("C reset exceeded conservative source bound")


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length()-1


def target(n: int) -> int:
    return (4 << n) - n - 4


def depth(n: int) -> int:
    return {4:0, 5:0, 10:4, 11:2, 16:2, 17:4}[n%18]


def witnesses(n: int):
    j = depth(n)
    p = 1 << (n-1)
    t = lambda i: 8*p+n-1-(2*n+3)*(1<<i)
    q = 2*t(j)+5
    assert q % 9 == 0, (n,j)
    a = 2*(q//9)-3
    assert v2(a+3) == 1
    assert 3*p-2 <= a <= 4*p-4
    h = 2*a-4*p-n+3
    assert h >= 0
    return j, h, t


def test() -> None:
    source_pairs = 0
    for a in range(100):
        for b in range(200):
            assert c_episode(a,b) == c_step(a,b), (a,b)
            source_pairs += 1
    assert first_reset(2)[0] == 5
    checks = 0
    for n in range(4, 301):
        if n%6 not in (4,5):
            continue
        j,h,t = witnesses(n)
        assert t(0) == target(n)
        assert first_reset(h)[0] == t(j), (n,h,j)
        for i in range(j):
            assert 6*(1 << (n-1))-1 <= t(i) <= 8*(1 << (n-1))-3
            assert first_reset(t(i+1))[0] == t(i), (n,i)
        checks += 1
    print(f"PASS: {source_pairs} direct original-C/P episode checks; "
          f"{checks} source-C reset ancestry checks n<=300; max depth 4; "
          "every surviving residue class covered")
    for n in (4,5,10,11,16,17):
        j,h,t = witnesses(n)
        print(f"n={n}, n%18={n%18}, j={j}, odd-parent={h}, "
              f"entry={t(j)}, fatal={t(0)}")


if __name__ == "__main__":
    test()
