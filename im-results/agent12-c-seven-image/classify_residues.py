#!/usr/bin/env python3
"""Exact finite-depth inverse explorer for Machine C section states.

Implements the source criterion from SectionAllInverse.lean algebraically.
The intended use is discovery: formal claims still belong in Lean.
"""

from functools import lru_cache


def v2(n: int) -> int:
    if n == 0:
        return 10**9
    out = 0
    while n % 2 == 0:
        out += 1
        n //= 2
    return out


def _pow2_exp(q: int):
    if q <= 0 or q & (q - 1):
        return None
    return q.bit_length() - 1


def parents(x: int, y: int):
    """All (a,k) with secNext(a,k)=(x,y), with branch labels."""
    out = []

    # Exceptional exactSection branches.
    if (x, y) == (0, 4):
        out.append((0, 1, "a0-k1"))
    for k, target in [(0, (5, 1)), (1, (2, 3)), (2, (2, 5)), (3, (0, 7))]:
        if (x, y) == target:
            out.append((1, k, f"a1-k{k}"))
    if y == 2:
        a = x + 2
        if a >= 2:
            out.append((a, 0, "k0"))

    s = x + y
    s1 = s + 1

    # a=0, k>=2.
    if s % 8 == 0:
        n = _pow2_exp(s // 8)
        if n is not None:
            rhs = x + 2 * y - 9 - 3 * n
            if rhs >= 0 and rhs % 2 == 0:
                k = rhs // 2
                if k >= 2:
                    out.append((0, k, f"a0-bounce-{n}"))

    # a=1, k>=4.
    if y == 3 and (x + 6) % 16 == 0:
        n = _pow2_exp((x + 6) // 16)
        if n is not None:
            rhs = x - 3 - 3 * n
            if rhs >= 0 and rhs % 2 == 0:
                k = rhs // 2
                if k >= 4:
                    out.append((1, k, f"a1-y3-{n}"))
    if y >= 5 and s1 % 16 == 0:
        n = _pow2_exp(s1 // 16)
        if n is not None:
            rhs = x + 2 * y - 11 - 3 * n
            if rhs >= 0 and rhs % 2 == 0:
                k = rhs // 2
                if k >= 4:
                    out.append((1, k, f"a1-large-{n}"))

    # Direct low branch, a>=2, k>=1.
    if y >= 4 and (y - 2) % 2 == 0:
        k = (y - 2) // 2
        a = x + y - 2
        if a >= 2 and k >= 1 and 2 * k <= a:
            out.append((a, k, "direct-low"))

    # Even-a high bounce.
    if y >= 4:
        for n in range(v2(s)):
            den = 1 << (n + 1)
            a = s // den - 2
            if a < 2 or a % 2:
                continue
            rhs = x + 2 * y - a - 7 - 3 * n
            if rhs >= 0 and rhs % 2 == 0:
                k = rhs // 2
                if k >= 1 and 2 * k > a:
                    out.append((a, k, f"even-high-{n}"))

    # Odd-a high bounce.
    if y == 3:
        for n in range(v2(x + 6)):
            den = 1 << (n + 1)
            if (x + 6) % den:
                continue
            a = (x + 6) // den - 3
            if a < 2 or a % 2 == 0:
                continue
            rhs = x + 1 - a - 3 * n
            if rhs >= 0 and rhs % 2 == 0:
                k = rhs // 2
                if k >= 1 and 2 * k > a:
                    out.append((a, k, f"odd-y3-{n}"))
    if y >= 5:
        for n in range(v2(s1)):
            den = 1 << (n + 1)
            a = s1 // den - 3
            if a < 2 or a % 2 == 0:
                continue
            rhs = x + 2 * y - a - 7 - 3 * n
            if rhs >= 0 and rhs % 2 == 0:
                k = rhs // 2
                if k >= 1 and 2 * k > a:
                    out.append((a, k, f"odd-high-{n}"))

    # The source criterion is functional in each branch; duplicate pairs can
    # only arise from coincident descriptions, so canonicalize them.
    seen = set()
    dedup = []
    for row in out:
        key = row[:2]
        if key not in seen:
            seen.add(key)
            dedup.append(row)
    return dedup


@lru_cache(maxsize=None)
def has_incoming(x: int, y: int, depth: int) -> bool:
    if depth == 0:
        return True
    return any(has_incoming(a, k, depth - 1) for a, k, _ in parents(x, y))


def target(u: int, v: int):
    return 641 + 1024 * u, 574 + 1024 * v


def p_state(u: int, v: int):
    return 1113 + 650 * u + 1298 * v, 321 + 187 * u + 375 * v


def proved_residue26(r: int) -> bool:
    return (
        r % 4 == 0
        or r % 16 == 15
        or r % 64 in (13, 38)
        or r % 32 in (21, 25)
    )


def main():
    uniform_no7 = []
    finer = {}
    for r in range(64):
        vals = []
        for u in range(64):
            v = (r - 29 * u) % 64
            vals.append(not has_incoming(*target(u, v), 7))
        if all(vals):
            uniform_no7.append(r)
        elif any(vals):
            finer[r] = [u for u, good in enumerate(vals) if good]

    proved = [r for r in range(64) if proved_residue26(r)]
    print("uniform no-Incoming7 residues:", uniform_no7)
    print("proved residue26:", proved)
    print("uniform match:", uniform_no7 == proved)
    print("count:", len(uniform_no7), "/ 64")
    print("finer nonuniform residues:")
    for r, us in finer.items():
        print(f"  r={r}: u mod64 samples {us}")

    # H1-grandparent depth-3 classification used for the class-1 sectors.
    p_no3 = []
    for r in range(64):
        if r % 4 != 1:
            continue
        ok = True
        for u in range(128):
            v = (r - 29 * u) % 64
            if has_incoming(*p_state(u, v), 3):
                ok = False
                break
        if ok:
            p_no3.append(r)
    print("class-1 P uniformly no-Incoming3 mod64:", p_no3)


if __name__ == "__main__":
    main()
