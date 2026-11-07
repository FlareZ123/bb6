#!/usr/bin/env python3
"""Exact inverse search experiment for Machine C's low parameter family.

Source transcriptions:
- section map: BounceCalc.lean / FastSectionDef.lean
- complete y>=5 inverse grammar: SectionFastInverseOriginal.lean /
  SectionPreimageCriterion.lean
- normalizers: OddForcedNormalize.lean, MixedFourNormalize.lean,
  EvenRightSixOrbit.lean, ValSixMixedNormalize.lean

For y<5, predecessors are brute-forced under the strict section-mass
decrease theorem. This script is computational evidence, not an all-m proof.
"""
import argparse
import csv
import sys
sys.setrecursionlimit(20000)


def bounce(k, c):
    if c < 4:
        return 0, None
    if k % 2:
        if c <= 2*k + 6:
            return c, (2*k + 6 - c, c)
        t, p = bounce(2*k + 3, c - (2*k + 3))
        return 2*k + 4 + t, p
    if c == 4:
        return 2, (2*k + 2, 3)
    if c == 5:
        return 2, None
    if c <= 2*k + 8:
        return c - 3, (2*k + 8 - c, c - 1)
    t, p = bounce(2*k + 4, c - (2*k + 5))
    return 2*k + 3 + t, p


def sec_next(a, k):
    if a == 0:
        if k == 0: return None
        if k == 1: return (0, 4)
        return bounce(1, 2*k + 1)[1]
    if a == 1:
        if k == 0: return (5, 1)
        if k == 1: return (2, 3)
        if k == 2: return (2, 5)
        if k == 3: return (0, 7)
        return bounce(4, 2*k - 3)[1]
    if k == 0: return (a - 2, 2)
    if 2*k <= a: return (a - 2*k, 2*k + 2)
    return bounce(a - 1, 2*k - a + 3)[1]


def v2(n):
    return 10**9 if n == 0 else (n & -n).bit_length() - 1


def small_y_candidates(x, y):
    mass = x + 2*y
    return {
        (a, k)
        for a in range(mass)
        for k in range((mass-a-1)//2 + 1)
        if sec_next(a, k) == (x, y)
    }


def fast_candidates(x, y):
    e, s = x + 2*y, x + y
    s1, out = s + 1, set()

    if s >= 8 and s & (s-1) == 0:
        n = s.bit_length() - 4
        q = e - 9 - 3*n
        if q >= 0 and q % 2 == 0 and q//2 >= 2:
            out.add((0, q//2))
    if s1 >= 16 and s1 & (s1-1) == 0:
        n = s1.bit_length() - 5
        q = e - 11 - 3*n
        if q >= 0 and q % 2 == 0 and q//2 >= 4:
            out.add((1, q//2))

    for n in range(max(0, v2(s)-1)):
        a = (s >> (n+1)) - 2
        q = e - a - 7 - 3*n
        if a >= 2 and a % 2 == 0 and q >= 0 and q % 2 == 0 and q//2*2 > a:
            out.add((a, q//2))
    for n in range(max(0, v2(s1)-1)):
        a = (s1 >> (n+1)) - 3
        q = e - a - 7 - 3*n
        if a >= 3 and a % 2 == 1 and q >= 0 and q % 2 == 0 and q//2*2 > a:
            out.add((a, q//2))

    if y >= 4 and y % 2 == 0:
        a, k = x + y - 2, (y - 2)//2
        if a >= 2 and k > 0:
            out.add((a, k))
    if (x, y) == (2, 5): out.add((1, 2))
    if (x, y) == (0, 7): out.add((1, 3))
    return out


def normalize(x, y):
    steps = 0
    while True:
        if (x%2 == 1 and y%2 == 1 and y >= 5 and (x+y)%4 == 0
                and (x+y)%16 != 0 and x+y >= 24):
            x, y = (x+y-4)//2, (x+3*y-10)//4
        elif (x%2 == 0 and y%2 == 1 and y >= 5
                and (x+y+1)%16 == 8 and x+y >= 23):
            x, y = (x+y-5)//2, (x+3*y-9)//4
        elif y >= 4 and y%2 == 0 and (x+y)%4 == 1:
            x, y = x+y-2, (y-2)//2
        elif y >= 6 and y%2 == 0 and (x+y)%8 not in (0, 7):
            x, y = x+y-2, (y-2)//2
        elif x%16 == 5 and y%16 == 10 and (x+y+1)%256 == 192:
            x, y = x+y-2, (y-2)//2
        else:
            return (x, y), steps
        steps += 1


def low_allowed(m):
    return all((
        m%1024 != 424, m%4096 != 4008, m%32768 != 30632,
        m%16 != 14, m%64 != 38, m%16384 != 5032, m%8 != 4,
        m%4 != 1, m%16 != 7, m%128 != 0, m%64 != 58, m%256 != 150,
    ))


def low_tower_witness(m):
    for n in range(2, m-3, 2):
        d = 1 << (n+4)
        q = 9*m + 13 + 5*(1 << (n+2))
        if q % d == 0 and q//d <= m:
            return n, q//d
    return None


class NodeLimit(Exception):
    pass


def root_search(x, y, limit):
    memo = {}
    stats = {"nodes": 0, "depth": 0, "max_candidates": 0,
             "small_y_nodes": 0, "max_small_y_mass": 0}

    def visit(x, y, depth):
        (x, y), _ = normalize(x, y)
        stats["depth"] = max(stats["depth"], depth)
        if (x, y) == (5, 1): return True
        if (x, y) in memo: return memo[(x, y)]
        stats["nodes"] += 1
        if stats["nodes"] > limit: raise NodeLimit
        if y < 5:
            stats["small_y_nodes"] += 1
            stats["max_small_y_mass"] = max(stats["max_small_y_mass"], x+2*y)
            candidates = small_y_candidates(x, y)
        else:
            candidates = fast_candidates(x, y)
        stats["max_candidates"] = max(stats["max_candidates"], len(candidates))
        answer = any(visit(a, k, depth+1)
                     for a, k in sorted(candidates, key=lambda p: p[0]+2*p[1]))
        memo[(x, y)] = answer
        return answer

    try:
        return visit(x, y, 0), stats
    except NodeLimit:
        return None, stats


def verify_fast_candidates():
    for x in range(30):
        for y in range(5, 20):
            assert fast_candidates(x, y) == small_y_candidates(x, y), (x, y)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-m", type=int, default=200)
    ap.add_argument("--node-limit", type=int, default=1000000)
    ap.add_argument("--include-tower-excluded", action="store_true")
    args = ap.parse_args()
    verify_fast_candidates()
    w = csv.writer(sys.stdout)
    w.writerow(["m", "tower_n", "tower_r", "root_reachable", "nodes",
                "max_depth", "max_candidates", "small_y_nodes", "max_small_y_mass"])
    for m in range(args.max_m + 1):
        if not low_allowed(m):
            continue
        tower = low_tower_witness(m)
        if tower and not args.include_tower_excluded:
            continue
        y = (1 << (2*m+3)) - (3*m+4)
        ans, st = root_search(1, y, args.node_limit)
        w.writerow([m, "" if tower is None else tower[0],
                    "" if tower is None else tower[1],
                    "unknown" if ans is None else str(ans).lower(),
                    st["nodes"], st["depth"], st["max_candidates"],
                    st["small_y_nodes"], st["max_small_y_mass"]])


if __name__ == "__main__":
    main()
