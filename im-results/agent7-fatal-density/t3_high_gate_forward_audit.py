#!/usr/bin/env python3
"""Exact forward-orbit audit of the t=3 high-q gate through MAX_N.

The candidate arithmetic is exact. The reset map is the closed first-reset
formula proved in agent10-cascade/FirstOutcome.lean and characterized by
FirstInverseComplete.lean. The binary-search implementation below finds the
same least sweep index as the original linear scan; the two are cross-checked
for all heights 2..10000 before the audit.

This is finite computational evidence, not an all-n theorem.
"""
from __future__ import annotations

import hashlib
import json
from collections import Counter

MAX_N = 100_000
MODULUS = 3**8
PERIOD = 2 * 3**7


def hash_nat(hasher, value: int) -> None:
    data = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    hasher.update(len(data).to_bytes(4, "big"))
    hasher.update(data)


def reset_return_slow(h: int) -> int | None:
    p, k = 1, 0
    while h + k + 5 >= 8 * p:
        p, k = 2 * p, k + 1
    if h + k + 4 == 4 * p:
        return None
    a = 4 * p + (h + k) // 2
    if (h + k) % 2 == 0:
        return a
    q = a + 3
    while q % 2 == 0:
        q = 3 * q // 2
    return (3 * q - 5) // 2


def reset_return(h: int) -> int | None:
    """Closed first-reset map, with the least sweep index found by binary search."""
    lo, hi = 0, h.bit_length() + 2
    while lo < hi:
        mid = (lo + hi) // 2
        if h + mid + 5 < 8 * (1 << mid):
            hi = mid
        else:
            lo = mid + 1
    k = lo
    p = 1 << k
    if h + k + 4 == 4 * p:
        return None
    a = 4 * p + (h + k) // 2
    if (h + k) % 2 == 0:
        return a
    q = a + 3
    while q % 2 == 0:
        q = 3 * q // 2
    return (3 * q - 5) // 2


def max_j_slow(n: int) -> int:
    lo, hi = 0, n + 1
    while lo < hi:
        j = (lo + hi) // 2
        deficit = (2 * n + 3) * (1 << j) - (n - 1)
        margin = 2048 * deficit + 16384 * n + 16384
        if margin <= (1 << n):
            lo = j + 1
        else:
            hi = j
    return lo - 1


def max_j(n: int) -> int:
    # Algebraically rearranged form of the exact margin inequality.
    numerator = (1 << n) - 14336 * n - 18432
    denominator = 2048 * (2 * n + 3)
    if numerator < denominator:
        return -1
    return (numerator // denominator).bit_length() - 1


def build_power_index() -> dict[int, int]:
    # 2 has order 4374 modulo 6561.
    out: dict[int, int] = {}
    power = 2
    for j in range(PERIOD):
        if power in out:
            raise AssertionError("unexpected short order modulo 6561")
        out[power] = j
        power = 2 * power % MODULUS
    if len(out) != PERIOD or power != 2:
        raise AssertionError("unexpected order modulo 6561")
    return out


POWER_INDEX = build_power_index()


def high_q_candidates(n: int) -> list[tuple[int, int]]:
    """All (j,q) satisfying the precision-eight gate and source margin at n."""
    if n % 6 not in (4, 5):
        return []
    c = 38 * (pow(2, n + 1, 81) + 2 * n - 1) % 81
    numerator = (8 * pow(2, n, MODULUS) + 2 * n + 3 - 81 * c) % MODULUS
    coefficient = (2 * n + 3) % MODULUS
    if coefficient % 3 == 0:
        raise AssertionError("ray coefficient is not a unit modulo 6561")
    rhs = numerator * pow(coefficient, -1, MODULUS) % MODULUS
    first_j = POWER_INDEX[rhs]
    last_j = max_j(n)
    out = []
    for j in range(first_j, last_j + 1, PERIOD):
        z = 8 * (1 << n) + 2 * n + 3 - (2 * n + 3) * (1 << (j + 1))
        if z % MODULUS != (81 * c) % MODULUS or z % 81 != 0:
            raise AssertionError("precision-eight translated gate mismatch")
        d = z // 81
        q = 16 * d - (1 << n) - n - 2
        if (2 * q + 5) % 81 != 0:
            raise AssertionError("source t=3 high-q gate mismatch")
        if not 9 * (1 << (n - 4)) <= q <= 10 * (1 << (n - 4)):
            raise AssertionError("candidate escaped the high-q band")
        out.append((j, q))
    return out


def audit(max_n: int = MAX_N) -> dict[str, object]:
    for h in range(2, 10_001):
        if reset_return(h) != reset_return_slow(h):
            raise AssertionError(f"reset-map mismatch at h={h}")
    for n in range(20, 10_001):
        if max_j(n) != max_j_slow(n):
            raise AssertionError(f"margin-cutoff mismatch at n={n}")

    root = 2
    root_hash = hashlib.sha256()
    candidate_hash = hashlib.sha256()
    reset_edges = 0
    candidate_count = 0
    hits = []
    r_mod_3_counts: Counter[int] = Counter()
    largest_j = -1

    for n in range(20, max_n + 1):
        # Exact first-reset heights are strictly increasing.
        while root.bit_length() < n:
            nxt = reset_return(root)
            if nxt is None or nxt <= root:
                raise AssertionError("unexpected halt or non-increasing reset")
            root = nxt
            reset_edges += 1
            hash_nat(root_hash, root)

        if root.bit_length() > n:
            continue

        candidates = high_q_candidates(n)
        candidate_count += len(candidates)
        if candidates:
            largest_j = max(largest_j, candidates[-1][0])
        candidate_set = {q for _, q in candidates}
        if len(candidate_set) != len(candidates):
            raise AssertionError(f"duplicate candidate at n={n}")

        for j, q in candidates:
            hash_nat(candidate_hash, n)
            hash_nat(candidate_hash, j)
            hash_nat(candidate_hash, q)

            z = 8 * (1 << n) + 2 * n + 3 - (2 * n + 3) * (1 << (j + 1))
            c = 38 * (pow(2, n + 1, 81) + 2 * n - 1) % 81
            x = (1 << (n + 1)) + 2 * n - 1
            kappa = (32 * c - x) // 81
            d = z // 81
            e = (2 * q + 5) // 81
            r = 16 * e - (1 << (n - 3)) - n + 1
            residue = r % 3
            r_zero_offset = 81 * c + 6561 * (kappa + 1)
            if ((z - r_zero_offset) % (3**9) == 0) != (residue == 0):
                raise AssertionError("precision-nine second-parent selector mismatch")
            r_mod_3_counts[residue] += 1

        # Scan every root-orbit height with bit length n.
        while root.bit_length() == n:
            if root in candidate_set:
                hits.append((n, root, reset_edges))
            nxt = reset_return(root)
            if nxt is None or nxt <= root:
                raise AssertionError("unexpected halt or non-increasing reset")
            root = nxt
            reset_edges += 1
            hash_nat(root_hash, root)

    return {
        "max_n": max_n,
        "candidate_count": candidate_count,
        "root_reset_edges_to_first_height_above_max_n": reset_edges,
        "last_root_height_bit_length": root.bit_length(),
        "matches": hits,
        "r_mod_3_counts": dict(sorted(r_mod_3_counts.items())),
        "candidate_stream_sha256": candidate_hash.hexdigest(),
        "root_orbit_prefix_sha256": root_hash.hexdigest(),
        "largest_candidate_j": largest_j,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
