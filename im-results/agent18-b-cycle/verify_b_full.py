"""Deterministic exact checks for BB6 Agent18 B parity coding and growth."""
from random import Random


def F(p: int, d: int) -> tuple[int, int]:
    return (d % 2, 3 * (d // 2) + 2 + 4 * p)


def G(z: int) -> int:
    return 3 * (z // 2) + 4 + 5 * (z % 2)


def iterate_F(n: int, p: int, d: int) -> tuple[int, int]:
    for _ in range(n):
        p, d = F(p, d)
    return p, d


def iterate_G(n: int, z: int) -> int:
    for _ in range(n):
        z = G(z)
    return z


def bits(n: int, p: int, d: int) -> tuple[int, ...]:
    result = []
    for _ in range(n):
        result.append(d % 2)
        p, d = F(p, d)
    return tuple(result)


def main() -> None:
    count = 0
    rng = Random(180362)
    for n in range(13):
        M = 2**n
        for p in (0, 1):
            seen = set()
            for d in range(M):
                word = bits(n, p, d)
                assert all(b in (0, 1) for b in word)
                assert word not in seen
                seen.add(word)
                p0, d0 = iterate_F(n, p, d)
                for k in (1, 2, 3):
                    assert bits(n, p, d + M*k) == word
                    assert iterate_F(n, p, d + M*k) == (p0, d0 + 3**n*k)
                    count += 1
            assert len(seen) == M
        print(f'coding n={n} 2*{M} unique words verified')

    for _ in range(3000):
        n = rng.randrange(60)
        z = rng.randrange(1_000_000)
        zn = iterate_G(n, z)
        assert 3**n*(z + 8) <= 2**n*(zn + 8)
        assert 2**n*(zn + 15) <= 3**n*(z + 15)
        count += 1

    a0 = 6
    z = iterate_G(a0, 0)
    a1 = z + 9 - 3*(z % 2)
    z1 = iterate_G(a1, 0)
    assert (z, z % 2, a1, z1 % 2) == (91, 1, 97, 0)
    print(f'synthetic counterexample: a0=6, G^6(0)={z}, a1={a1}, G^97(0)%2={z1%2}')
    print(f'PASS: {count} exact lift/growth checks')


if __name__ == '__main__':
    main()
