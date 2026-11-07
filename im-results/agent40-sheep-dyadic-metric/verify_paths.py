"""Finite-path lifting for the genuine generic Sheep first-even return.

For randomly sampled paths of any length up to 12 in each exact finite
generic quotient graph G_p (p=1..9), this checker reverses the WHOLE path
at increasing dyadic precision, constructs ONE sufficiently large genuine
source, and replays the full integer return trajectory. Seed is fixed.
"""
from random import Random
from verify_eccentricity import quotient_graph, v2


def inverse_parent(precision: int, a: int, h: int, target: int) -> int:
    q = 1 << (precision-a)
    return ((1 << a) * pow(1+(1 << (a+1)), -1, q) *
            (3-2*a+(1 << (h+1))*pow(3**h, -1, q)*(target-1))) % (
                1 << precision)


def lift_and_verify(p: int, walk: list[int]) -> tuple[int,int]:
    letters = []
    for r, s in zip(walk, walk[1:]):
        if r == 0:
            letters.append((p,0))  # Explicit high-valuation zero hub.
        else:
            a = v2(r)
            h = next(h for h in range(p-a)
                     if inverse_parent(p,a,h,s)==r)
            letters.append((a,h))

    precision = p
    x = walk[-1]
    for a,h in reversed(letters):
        precision += a+h+1
        x = inverse_parent(precision,a,h,x)
    x += (1 << precision)*10000
    assert x%(1 << p) == walk[0]

    y = x + (1 << precision)
    alpha = 1
    for i,(a,h) in enumerate(letters):
        for_value = []
        for z in (x,y):
            A = v2(z)
            u = z >> A
            assert A == a and u >= 5 and u%2==1
            f = z+A+(u-1)//2
            H = v2(f-1)
            v = (f-1) >> H
            assert H == h and v >= 5 and v%2==1
            nxt = 1 + 3**H*v
            assert nxt > z and nxt%2==0
            assert nxt%(1 << p) == walk[i+1]
            for_value.append(nxt)
        x,y = for_value
        alpha *= 3**h*(1+(1 << (a+1)))
    assert y-x == alpha*(1 << p)
    return precision,alpha


def check() -> None:
    rng = Random(622026)
    total = 0
    for p in range(1,10):
        graph = quotient_graph(p)
        nodes = list(graph)
        tested = 0
        for length in range(1,13):
            for sample in range(150):
                path = [rng.choice(nodes)]
                for i in range(length):
                    candidates = sorted(graph[path[-1]])
                    if (sample+i)%3 == 0 and 0 in graph[path[-1]]:
                        path.append(0)
                    else:
                        path.append(rng.choice(candidates))
                lift_and_verify(p,path)
                tested += 1
        total += tested
        print(f"PASS p={p}: {tested} walks of length 1..12",flush=True)
    print(f"PASS {total} genuine coherent finite-path witnesses",flush=True)


if __name__ == "__main__":
    check()
