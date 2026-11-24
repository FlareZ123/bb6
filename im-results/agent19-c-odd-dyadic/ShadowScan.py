"""Integer-only exploratory all-parent root32 shadow scan (not a Lean proof)."""
import argparse

C = 22155
RESIDUALS = (
    (1469153280, 393975148, 2788638720, 747814654),
    (5065196640, 1358307257, 990617040, 265648583),
    (1376399640, 369101882, 2835015540, 760251268),
)

def shadow(z, j):
    a, b, c, d = z
    return a * (C * j + 17300) - C * b, c * (C * j + 17300) - C * d

def leaf(u, v):
    return v % 2 == 1 and (u + v) % 4 in (1, 2)

def valuation(q):
    assert q > 0
    return (q & -q).bit_length() - 1

def children(u, v):
    o = (u + v) % 2
    q = u + v - C * o
    w = valuation(q)
    if v % 2 == 0:
        yield 1, u + v + 2 * C, (v + 2 * C) // 2
    for n in range((u + 1 + o) % 2, w - 1, 2):
        a = q // (1 << (n + 1)) + C * (2 + o)
        twice_k = u + 2 * v - a + C * (7 + 3 * n)
        assert (1 << (n + 1)) * a == q + (1 << (n + 1)) * C * (2 + o)
        assert twice_k >= 0 and twice_k % 2 == 0
        yield n + 2, a, twice_k // 2

def required_iter(fuel, u, v):
    """Postorder DFS; returns sufficient p, node count, maximum depth.

    Mirrors the branch/leaf guards in Root32ShadowArithmetic.lean.
    A fuel failure is not a counterexample to mortality.
    """
    stack = [(0, u, v, 0, None, 0)]
    result = None
    count = maxdepth = 0
    while stack:
        dep, a, k, shift, cs, p = stack[-1]
        if cs is None:
            count += 1
            maxdepth = max(maxdepth, dep)
            assert a > 0 and k > 0
            if leaf(a, k):
                result = max(2, (k + 5 * C).bit_length())
                stack.pop()
            elif dep == fuel:
                return None, count, maxdepth
            else:
                w = valuation(a + k - C * ((a + k) % 2))
                p = max(2, w + 1, (a + k + C * ((1 << w) + 16)).bit_length())
                stack[-1] = (dep, a, k, shift, iter(children(a, k)), p)
                continue
        else:
            if result is not None:
                p = max(p, result + shift)
                result = None
            try:
                d, x, y = next(cs)
            except StopIteration:
                result = p
                stack.pop()
            else:
                stack[-1] = (dep, a, k, d, cs, p)
                stack.append((dep + 1, x, y, 0, None, 0))
                continue
    return result, count, maxdepth

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=1000)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--fuel", type=int, default=10000)
    ap.add_argument("--precision", type=int, default=20000)
    args = ap.parse_args()
    failures = []
    hardest = None
    for j in range(args.start, args.start + args.count):
        for name, z in zip(("D", "L", "P"), RESIDUALS):
            p, nodes, depth = required_iter(args.fuel, *shadow(z, j))
            if p is None or p > args.precision:
                failures.append((j, name, p, nodes, depth))
            if hardest is None or nodes > hardest[0]:
                hardest = (nodes, j, name, p, depth)
        if (j - args.start + 1) % 100 == 0:
            print("through", j, "failures", len(failures), "hardest", hardest, flush=True)
    print("failures:", failures)
    print("hardest (nodes,j,residual,p,depth):", hardest)

if __name__ == "__main__":
    main()
