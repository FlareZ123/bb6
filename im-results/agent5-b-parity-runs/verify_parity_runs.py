"""Reproduce the Lean parity-block acceleration for Machine B (Python 3)."""
import hashlib
import random
import time


def G(z: int) -> int:
    return 3 * (z // 2) + 4 + 5 * (z % 2)


def maximal_run(z: int) -> tuple[int, int]:
    delta = 8 if z % 2 == 0 else 15
    q = z + delta
    k = (q & -q).bit_length() - 1
    return k, pow(3, k) * (q >> k) - delta


def accelerated_iterate(z: int, n: int) -> int:
    while n:
        k, endpoint = maximal_run(z)
        if k <= n:
            z, n = endpoint, n - k
        else:
            delta = 8 if z % 2 == 0 else 15
            z = pow(3, n) * ((z + delta) >> n) - delta
            n = 0
    return z


def main() -> None:
    rng = random.Random(0xBB6005)
    t0 = time.perf_counter()
    for _ in range(5000):
        z = rng.randint(0, 10**12)
        n = rng.randint(0, 80)
        actual = z
        for _ in range(n):
            actual = G(actual)
        assert accelerated_iterate(z, n) == actual, (z, n)
    print("PASS: 5,000 fixed-seed randomized exact iteration tests")

    for z in range(10000):
        k, endpoint = maximal_run(z)
        actual = z
        for _ in range(k):
            assert actual % 2 == z % 2
            actual = G(actual)
        assert actual == endpoint and actual % 2 != z % 2
    print("PASS: 10,000 exhaustive maximal parity-run tests")

    z = accelerated_iterate(0, 227097)
    checksum = hashlib.sha256(z.to_bytes((z.bit_length() + 7) // 8, "big")).hexdigest()
    assert z % 2 == 1
    assert z.bit_length() == 132847
    assert checksum == "15d1bf0d327f41d76b4a47e6d5293cab98143a69ae12c70487be42a23f3593cc"
    print(f"PASS: third sampled parity=1, bits={z.bit_length()}, SHA256={checksum}")
    print(f"Total time: {time.perf_counter()-t0:.2f}s")


if __name__ == "__main__":
    main()
