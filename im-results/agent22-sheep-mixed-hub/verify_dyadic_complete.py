"""Exact witness construction for Sheep's dyadic first-even quotient.

All paths are in the synthetic residue graph. Distinct edges may need different
integer representatives; no statement about the blank-origin orbit follows.
"""
from math import comb
from collections import Counter, deque


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def even_return(t: int) -> int | None:
    a = v2(t)
    u = t >> a
    if u == 1:
        return None
    z = t + a + (3 if u == 3 else (u - 1) // 2)
    h = v2(z - 1)
    return 1 + 3**h * ((z - 1) >> h)


def parent(p: int, a: int, h: int, y: int) -> int:
    assert 1 <= a < p and 0 <= h < p - a and y % 2 == 0
    m = 1 << (p - a)
    d = (1 << (a + 1)) + 1
    w = (y - 1) * pow(3**h, -1, m)
    u = (3 - 2*a + (1 << (h + 1))*w)*pow(d, -1, m) % m
    assert u % 2 == 1
    return (1 << a)*u % (1 << p)


def encode(p: int, word: tuple[tuple[int, int], ...]) -> int:
    result = 0
    for a, h in reversed(word):
        result = parent(p, a, h, result)
    return result


def decode(p: int, r: int) -> tuple[tuple[int, int], ...]:
    assert 0 <= r < (1 << p) and r % 2 == 0
    if r == 0:
        return ()
    a = v2(r)
    u = r >> a
    c = ((1 << (a+1)) + 1)*u + 2*a - 3
    assert c > 0 and c % 2 == 0
    h = min(v2(c)-1, p-a-1)
    t = p-a-h-1
    assert c % (1 << (h+1)) == 0 and t <= p-2
    y = (1+3**h*(c >> (h+1))) % (1 << t)
    assert y % 2 == 0
    word = ((a, h),) + decode(t, y)
    assert encode(p, word) == r
    return word


def legal_edge_witness(p: int, r: int, y: int, a: int, h: int) -> tuple[int, int]:
    assert parent(p, a, h, y) == r
    d = (1 << (a+1)) + 1
    u = r >> a
    c = d*u + 2*a - 3
    t = p-a-h-1
    assert c % (1 << (h+1)) == 0
    w = c >> (h+1)
    z0 = 1+3**h*w
    assert (y-z0) % (1 << t) == 0
    modulus = 1 << (p-t)
    coeff = 3**h*d
    k = (((y-z0)//(1 << t))*pow(coeff, -1, modulus)) % modulus
    while u+(1 << (p-a))*k < 5 or w+d*(1 << t)*k < 5:
        k += modulus
    u1 = u+(1 << (p-a))*k
    w1 = w+d*(1 << t)*k
    x = (1 << a)*u1
    z = 1+3**h*w1
    assert u1 % 2 == 1 and w1 % 2 == 1
    assert x % (1 << p) == r and z % (1 << p) == y
    assert even_return(x) == z
    return x, z


def verify() -> None:
    total_residues = 0
    total_edges = 0
    max_bits = 0
    for p in range(1, 15):
        m = 1 << p
        for r in range(0, m, 2):
            word = decode(p, r)
            assert sum(a+h+1 for a, h in word) <= p
            assert len(word) <= p//2
            for i, (a, h) in enumerate(word):
                src = encode(p, word[i:])
                dst = encode(p, word[i+1:])
                x, _ = legal_edge_witness(p, src, dst, a, h)
                max_bits = max(max_bits, x.bit_length())
                total_edges += 1
            total_residues += 1
        print(f"p={p}: all {m//2} even residues have an exact path to zero")
    print(f"PASS: {total_residues} residues, {total_edges} legal edges; max bits {max_bits}")

    for p in range(1, 13):
        n = 1 << p
        distances = {0: 0}
        todo = deque([0])
        while todo:
            target = todo.popleft()
            for a in range(1, p):
                for h in range(p-a):
                    source = parent(p, a, h, target)
                    if source not in distances:
                        distances[source] = distances[target]+1
                        todo.append(source)
        assert len(distances) == n//2
        assert all(distances[r] == len(decode(p, r)) for r in distances)
        assert Counter(distances.values()) == Counter(
            {j: comb(p, 2*j) for j in range(p//2+1)}
        )
    print("PASS: exact modular reverse-BFS layer counts C(p,2j), p=1..12")


if __name__ == "__main__":
    verify()
