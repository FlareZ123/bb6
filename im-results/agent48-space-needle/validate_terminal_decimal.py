"""Exact modular audit for symbolic Space Needle decimal-exponent witnesses."""
import hashlib
import random


def geom(base: int, exponent: int) -> int:
    return (pow(base, exponent) - 1) // (base - 1)


def witness(e: int, r: int, bound: int) -> tuple[int, int, int]:
    m = pow(10, e)
    assert 0 <= r < m
    if r % 2 == 0:
        n = geom(10, e) * (6 + m - r // 2) + m * bound
        k = 12 + 18 * n
        return k, 3, 19
    n = geom(2050, e) * (1834 + m - r // 2) + m * bound
    k = 3669 + 4098 * n
    return k, 11, 4099


def check(e: int, r: int, bound: int) -> str:
    k, v, den = witness(e, r, bound)
    assert k >= bound and k % pow(10, e) == r
    assert pow(2, k + 1, den) == (2 * v - 3) % den
    assert k >= 12
    return f"{e},{r},{bound},{k},{v}\n"


def main() -> None:
    rng = random.Random(20261103)
    chunks: list[str] = []
    for e in range(4):
        for r in range(pow(10, e)):
            for bound in (0, 1, 100):
                chunks.append(check(e, r, bound))
    for e in range(4, 11):
        m = pow(10, e)
        sample = {0, 1, 2, 3, m // 2, m // 2 + 1, m - 2, m - 1}
        sample.update(rng.randrange(m) for _ in range(50))
        for r in sorted(sample):
            for bound in (0, 1, 1000000):
                chunks.append(check(e, r, bound))
    digest = hashlib.sha256("".join(chunks).encode()).hexdigest()
    assert digest == "8963397546b9510ef067c8a455b78fdd240e9cd1f065440269b30c6b6b8f14ad"
    print("Verified decimal suffix witnesses:", len(chunks))
    print("K residues and modular power equations exact without huge exponent materialization")
    print("SHA-256 CSV parameter digest:", digest)


if __name__ == "__main__":
    main()
