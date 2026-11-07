#!/usr/bin/env python3
"""Reproduce Agent 22's exact 283,345-return Sheep prefix statistics.

This is an exploratory finite-prefix audit, not a proof about the infinite
blank-rooted orbit. Uses only Python's standard library.
"""
from array import array
from collections import Counter
from hashlib import sha256

N = 283_345
P = 15
RESIDUES = 1 << (P - 1)
SENTINEL = 0xFFFFFFFF


def even_return(x: int) -> tuple[int, int, int, int, int]:
    """Return (E(x), a, u, h, v), including the authentic u=3 branch."""
    if x <= 0 or x & 1:
        raise ValueError("expected a positive even state")
    a = (x & -x).bit_length() - 1
    u = x >> a
    if u == 1:
        raise ValueError("terminal power-of-two state reached")
    f = x + a + (3 if u == 3 else (u - 1) // 2)
    z = f - 1
    if z <= 0:
        raise ValueError("invalid odd-block endpoint")
    h = (z & -z).bit_length() - 1
    v = z >> h
    return 1 + pow(3, h) * v, a, u, h, v


def main() -> None:
    first = array("I", [SENTINEL]) * RESIDUES
    a_counts: Counter[int] = Counter()
    h_counts: Counter[int] = Counter()
    branch_counts: Counter[tuple[int, int]] = Counter()
    small_v: Counter[int] = Counter()
    exceptional_u3 = 0
    total_cost = 0
    max_a = 0
    max_h = 0
    x = 10

    for index in range(N):
        residue = (x & ((1 << P) - 1)) >> 1
        if first[residue] == SENTINEL:
            first[residue] = index

        y, a, u, h, v = even_return(x)
        a_counts[a] += 1
        h_counts[h] += 1
        branch_counts[(a, h)] += 1
        if v < 5:
            small_v[v] += 1
        exceptional_u3 += (u == 3)
        total_cost += a + h + 1
        max_a = max(max_a, a)
        max_h = max(max_h, h)
        x = y

    missing = sum(index == SENTINEL for index in first)
    first_hash = sha256(
        b"".join(index.to_bytes(4, "little") for index in first)
    ).hexdigest()
    max_first_index = max(first)

    assert missing == 0, f"missing {missing} residues modulo 2^{P}"
    assert first_hash == (
        "62e4c30f24fcf82bf42734abaaa9bccd73f99b9e5ecfd3724b12af27d9d91e95"
    )
    assert total_cost == 1_132_967
    assert max_first_index == 157_868
    assert max_a == 17
    assert max_h == 20
    assert exceptional_u3 == 0
    assert small_v == Counter({1: 1, 3: 1})
    assert branch_counts[(1, 0)] == 71_215

    print(f"transitions: {N}")
    print(f"final state bit length: {x.bit_length()}")
    print(f"total branch cost: {total_cost}")
    print(f"mean branch cost: {total_cost / N:.15f}")
    print(f"max a: {max_a}; max h: {max_h}")
    print(f"exceptional source u=3 count: {exceptional_u3}")
    print(f"odd cofactor v<5 counts: {dict(sorted(small_v.items()))}")
    print(f"(a,h)=(1,0) count: {branch_counts[(1, 0)]}")
    print(f"(a,h)=(1,0) frequency: {branch_counts[(1, 0)] / N:.12f}")
    print(f"p=15 residue coverage: {RESIDUES - missing}/{RESIDUES}")
    print(f"last first-occurrence index: {max_first_index}")
    print(f"first-occurrence digest (LE uint32): {first_hash}")
    print(f"a histogram: {dict(sorted(a_counts.items()))}")
    print(f"h histogram: {dict(sorted(h_counts.items()))}")


if __name__ == "__main__":
    main()
