"""Bounded differential check for the exact dyadic defect coordinate update.

The graph is the source-derived necessary odd-cone grammar. It intentionally
ignores the blank-reachability condition and stops after two positive resets.
No raw Turing-machine halting or global reachability result follows.
"""
from collections import deque

for n in [30, 46, 62, 78, 94, 110, 126, 142, 158]:
    P = 1 << n
    K = 7 * P - n - 3
    q = deque([(1, 0, 1, n + 2, 0)])
    seen = set()
    count = [0, 0, 0, 0]
    near = 0
    max_cost = 0
    while q:
        D, m, C, N, resets = q.popleft()
        key = (D, m, C, N, resets)
        if key in seen:
            continue
        seen.add(key)
        count[min(resets, 3)] += 1
        max_cost = max(max_cost, m)
        assert 0 < N <= n + m + 2
        assert C > 0 and (C & 1)
        if m > n:
            continue
        F = K - D - m + 2
        assert F + N == 7 * (1 << (n - m)) * C
        E = K - D - m
        b = 2 * E - 8
        if b < 8 or b % 4:
            continue
        S = K + D - m
        if S <= 0:
            continue
        valuation = (S & -S).bit_length() - 1
        for l in range(1, valuation + 1):
            mm = m + l
            if mm > n:
                continue
            DD = S >> l
            if DD < 2:
                continue
            bnew = 2 * (K - DD - mm) - 8
            if bnew < 0:
                continue
            rr = resets + (l >= 2)
            if rr > 2:
                continue
            if l == 1:
                assert N % 2 == 0
                CC, NN = C, N // 2
            else:
                M = 2 * (n + m + 2) - N
                V = (1 << (m + 1)) - C
                assert M > 0 and V > 0
                if M >= 1 << (n - m):
                    near += 1
                    continue
                assert M % (1 << l) == 0
                h = M >> l
                CC = (1 << mm) - V
                NN = n + mm + 1 - h
            assert CC > 0 and (CC & 1)
            assert 0 < NN <= n + mm + 2
            FF = K - DD - mm + 2
            assert FF + NN == 7 * (1 << (n - mm)) * CC
            q.append((DD, mm, CC, NN, rr))
    print(n, "nodes", len(seen), "reset partition", count,
          "high-defect branches omitted", near, "max cost", max_cost)
