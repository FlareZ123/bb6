"""Exact finite ancestor search for the #688 collapsed arithmetic map."""
from time import monotonic
import sys
K = (5, 3, 9, 7, 12, 10)
def step(b, c):
    k = min(b, c // 2)
    l, r = b - k, c - 2*k
    if l == 0:
        if r == 6:
            return None
        if r < 6:
            return 0, 4*k + K[r]
        return 2*k + 4, r - 6
    if l == 1:
        return 2, 4*k + 3 - 2*r
    return l - 2, 4*k + 7 - 2*r

def parents(B, C):
    if B == 0:
        for r, v in enumerate(K):
            if C >= v and (C-v) % 4 == 0:
                k = (C-v)//4
                yield k, 2*k+r
    if B >= 4 and B % 2 == 0 and C >= 1:
        k = (B-4)//2
        yield k, 2*k+C+6
    if B == 2:
        for r in (0, 1):
            v = 3-2*r
            if C >= v and (C-v) % 4 == 0:
                k = (C-v)//4
                yield k+1, 2*k+r
    for r in (0, 1):
        v = 7-2*r
        if C >= v and (C-v) % 4 == 0:
            k = (C-v)//4
            yield k+B+2, 2*k+r

def search(j, cap=2_000_000):
    X = (1 << (2*j+2))-j-1
    target = (X-4, 2*X-3)
    todo = [target]
    seen = {target}
    t = monotonic()
    while todo:
        if len(seen) > cap:
            return "open", len(seen), len(todo), monotonic()-t
        q = todo.pop()
        if q == (0, 2):
            return "reachable", len(seen), len(todo), monotonic()-t
        for p in parents(*q):
            assert step(*p) == q
            if p not in seen:
                seen.add(p)
                todo.append(p)
    return "excluded", len(seen), 0, monotonic()-t
if __name__ == "__main__":
    for j in map(int, sys.argv[1:]):
        print(j, search(j), flush=True)
