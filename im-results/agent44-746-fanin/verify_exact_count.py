"""Exact first-return odd-parent count formula, with independent finite audit.

The mathematical derivation is in ExactCount.md; this executable audit is
not a replacement for an all-input Lean proof or blank-root reachability.
"""
from hashlib import sha256
from random import Random


def odd_count_by_bands(u: int) -> int:
    z = 2*u + 5
    t = 0
    count = 0
    while z % 3 == 0:
        z //= 3
        q = z << t
        if q == 7:
            count += 1
        elif q >= 13:
            k = ((q-1)//6).bit_length() - 1
            p = 1 << k
            if k >= 1 and 6*p+1 <= q <= 8*p-1:
                count += 1
        t += 1
    return count


def odd_count_closed(u: int) -> int:
    z = 2*u + 5
    valuation = 0
    while z % 3 == 0:
        z //= 3
        valuation += 1
    if valuation == 0:
        return 0
    d = z
    first = pow(3, valuation-1)*d
    last = (1 << (valuation-1))*d
    prefix_count = (valuation-1) - (first.bit_length()-last.bit_length())
    if d == 1 and valuation >= 2:
        prefix_count -= 1
    assert prefix_count >= 0
    final_hit = last == 7
    if last >= 13:
        k = ((last-1)//6).bit_length() - 1
        p = 1 << k
        final_hit |= k >= 1 and 6*p+1 <= last <= 8*p-1
    return prefix_count + int(final_hit)


def audit() -> None:
    digest = sha256()
    bound = 2_000_000
    for u in range(bound):
        a = odd_count_by_bands(u)
        b = odd_count_closed(u)
        assert a == b, (u, a, b)
        digest.update(bytes([b]))
    print(f'PASS all u<{bound}; SHA256(count bytes)={digest.hexdigest()}')
    rng = Random(746_20261105)
    total = 0
    for bits in (64, 128, 512, 2048, 8192):
        for _ in range(1000):
            u = rng.getrandbits(bits)
            a = odd_count_by_bands(u)
            b = odd_count_closed(u)
            assert a == b, (u, a, b)
            total += 1
    print(f'PASS {total} seeded randomized large targets')
    # 3-adic lift samples, seeded by the two surviving #746 fatal classes.
    for residue in (4, 5):
        n = residue
        for level in range(10):
            modulus = 3**(level+2)
            candidates = [n + 6*j*3**level for j in range(3)
                if (pow(2, n+6*j*3**level+3, modulus)
                    - 2*(n+6*j*3**level) - 3) % modulus == 0]
            assert len(candidates) == 1, (residue, level, candidates)
            n = candidates[0]
            u = (4 << n)-n-4
            assert odd_count_by_bands(u) == odd_count_closed(u)
        print(f'PASS high-valuation fatal sector n%6={residue}, last n={n}')


if __name__ == '__main__':
    audit()
