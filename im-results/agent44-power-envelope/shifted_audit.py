"""Independent computational coefficient census for the P1 GAncestor c=1 obstruction.

This checks every interior node in Agent 4's deterministic scanner. The
source-compiled GOneCertificate.lean proves the two rectangles imply no pure
power of two. The original trees themselves remain unformalized candidates.
"""
from collections import Counter
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "agent4-p1-cone2398"))
from uniform_scan import Aff, all_positive_g_ancestors, check_residue


def main():
    counts = Counter()
    ext = {"lower": [10**10, 0, 10**10, -10**10],
           "upper": [10**10, 0, 10**10, -10**10]}
    for sector, first in ((2, 34), (14, 30)):
        for r in range(first, 65536, 16):
            closed, *_ = check_residue(r)
            if not closed:
                continue
            stack = [(Aff(131072, 131056-2*r), Aff(0, 3))]
            counts["closed"] += 1
            while stack:
                b, d = stack.pop()
                D = d + b.divide_exact(2) + 3
                a, c = D.a, D.c
                side = "lower" if a <= 74888 else "upper"
                if side == "lower":
                    assert 65536 <= a <= 74888 and 12 <= c <= 74562, (r, D)
                    low, high = 262144, 524288
                else:
                    assert 74928 <= a <= 130720 and 10 <= c <= 130036, (r, D)
                    low, high = 524288, 1048576
                # Exact coefficientwise sufficient conditions with X>=16384(q+1).
                assert 7*a > low and 7*a < high
                assert 16384*(7*a-low)-a+c > 0
                assert 16384*(high-7*a)+a-c > 0
                rec = ext[side]
                rec[0],rec[1] = min(rec[0],a),max(rec[1],a)
                rec[2],rec[3] = min(rec[2],c),max(rec[3],c)
                counts[side] += 1
                for k, u in all_positive_g_ancestors(b, d):
                    x, y = k*2-4, u+4
                    if y.residue(2) == 1 and x.residue(4) == 0:
                        stack.append((x, y))
    assert counts == Counter(closed=5264, lower=14827, upper=61337), counts
    assert ext["lower"] == [65536,74888,12,74562]
    assert ext["upper"] == [74928,130720,10,130036]
    print("candidate closed trees:", counts["closed"])
    print("total candidate interior nodes:", counts["lower"]+counts["upper"])
    print("low-band coefficient extent:", ext["lower"])
    print("high-band coefficient extent:", ext["upper"])
    print("all nodes pass Lean-proved gap premises; generated trees remain unverified")


if __name__ == "__main__":
    main()
