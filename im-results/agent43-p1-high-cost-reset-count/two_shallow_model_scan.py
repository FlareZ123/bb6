"""Finite exact-integer scalar-model scan for two shallow P1 inverse edges.

Only uses the same affine transition equations as OneShallowModelBridge.lean,
so it is an exploratory necessary-condition screen, not original-source
CountCone certification. It tests 2^s (0|1) 2^u (0|1) 2^r words, with finite
n range and sufficient depth-two length to cover all *integral* scalar
successors until no further integral successor exists (or n+20 steps).
"""
from collections import Counter


def succ(P: int, W: int, B: int, t: int):
    if t == 2:
        num, den, B1 = W + 84 * P + 16 * B, 8, B + 3
    elif t == 1:
        num, den, B1 = W + 28 * P + 8 * B - 8, 4, B + 2
    else:
        num, den, B1 = W + 4 * B - 8, 2, B + 1
    if num % den:
        return None
    return num // den, B1


def scan(n: int):
    P = 1 << n
    root = (14 * P + 2 * n + 4, n + 6)
    pref = [root]
    while (v := succ(P, *pref[-1], 2)) is not None and len(pref) < n + 20:
        pref.append(v)
    found = []
    count = 0
    max_u = 0
    for s, (Ws, Bs) in enumerate(pref):
        for a in (0, 1):
            t = succ(P, Ws, Bs, a)
            if t is None:
                continue
            mid = [t]
            while (v := succ(P, *mid[-1], 2)) is not None and len(mid) < n + 20:
                mid.append(v)
            max_u = max(max_u, len(mid) - 1)
            for u, (Wu, Bu) in enumerate(mid):
                for b in (0, 1):
                    v = succ(P, Wu, Bu, b)
                    if v is None:
                        continue
                    for r in range(n + 20):
                        count += 1
                        if v[0] == 12 * P:
                            found.append((s, a, u, b, r, v[1]))
                        v = succ(P, *v, 2)
                        if v is None:
                            break
    return found, count, len(pref) - 1, max_u


if __name__ == "__main__":
    failures, total, max_s, max_u, active = [], 0, 0, 0, 0
    for n in range(14, 4001):
        found, count, s, u = scan(n)
        total += count
        max_s = max(max_s, s)
        max_u = max(max_u, u)
        active += count > 0
        if found:
            failures.append((n, found))
            print("FOUND", failures[-1], flush=True)
            break
    print(dict(tested=(14, n), found=failures, scalar_paths=total,
               max_s=max_s, max_u=max_u, active=active))
