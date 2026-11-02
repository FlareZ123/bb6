"""Exact integer exploration of P1 n=16q+2 two-feeder inverse cones.

This is a *finite sample* and is not a nonhalting theorem. For each q, the
search expands at most max_nodes distinct positive-odd G-output hubs. Every
checked terminal positive-even-right predecessor tests the candidate strict
band 4*u < left+12 < 8*u. Exits outside the admissible odd sector are terminal
for this screen only. Source model: Agent47 inverseAt + Agent45 feeder iff.
"""
from collections import deque
import argparse


def ancestors(b, d):
    if b < 8 or b % 4 or d % 2 != 1:
        raise ValueError((b, d))
    k = b // 4 - 1
    c = d + b // 2
    while True:
        yield 2 * k - 4, c + 4
        if c < 3 or c % 2 == 0:
            return
        v = (c - 3) // 2
        k += v // 2 + 1
        c = v


def scan(q, max_nodes):
    u = 7 * 2 ** (16 * q) - 4 * q - 3
    pending = [(4 * u - 4, 4 * u + 9), (6 * u - 2, 2 * u + 5)]
    visited = set()
    leaves = 0
    exceptional = 0
    while pending and len(visited) < max_nodes:
        b, d = pending.pop()
        if (b, d) in visited:
            continue
        visited.add((b, d))
        if b < 8 or b % 4 != 0 or d % 2 != 1:
            return {"q": q, "failure": "unexpected hub", "hub": (b, d)}
        shifted = d + b // 2 + 3
        if shifted & (shifted - 1) == 0 and shifted >= 4:
            exceptional += 1
        for left, right in ancestors(b, d):
            if left % 4 == 0 and right % 2 == 0:
                leaves += 1
                if not (4 * u < left + 12 < 8 * u):
                    return {"q": q, "failure": "outside band", "left": left}
            elif left % 4 == 0 and right % 2 == 1 and left > 2:
                pending.append((left, right))
            elif left % 4 != 2:
                return {"q": q, "failure": "unexpected terminal", "left": left, "right": right}
    return {"q": q, "expanded": len(visited), "pending": len(pending),
            "checked_even_leaves": leaves, "exceptional_power2_outputs": exceptional}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-q", type=int, default=500)
    ap.add_argument("--max-nodes", type=int, default=10000)
    args = ap.parse_args()
    closed = capped = bad = 0
    for q in range(1, args.max_q + 1):
        x = scan(q, args.max_nodes)
        if "failure" in x or x["exceptional_power2_outputs"]:
            print("COUNTEREXAMPLE_CANDIDATE", x, flush=True)
            bad += 1
        elif x["pending"]:
            print("INCOMPLETE", x, flush=True)
            capped += 1
        else:
            closed += 1
    print("SUMMARY", {"q_checked": args.max_q, "fully_exhausted": closed,
                      "capped": capped, "potential_counterexamples": bad})


if __name__ == "__main__":
    main()
