"""Independent mixed-modulus finite-path lifting audit for Sheep generic E.

Builds many real generic quotient edges from exact section integer formulas
and inverse-engineered high-h transitions. Chooses random finite walks,
reverses each entire walk at increasing dyadic precision, applies CRT for the
initial odd residue, then checks every consecutive physical integer return.
Only Python standard library. Fixed seed; finite evidence only.
"""
from collections import defaultdict
from random import Random


def v2(n: int) -> int:
    return (n & -n).bit_length()-1


def inverse_parent(p: int, a: int, h: int, y: int) -> int:
    q = 1 << (p-a)
    return ((1 << a) * pow(1+(1 << (a+1)), -1, q) *
            (3-2*a+(1 << (h+1))*pow(3**h,-1,q)*(y-1)))%(1 << p)


def even_return(x: int) -> tuple[int,int,int] | None:
    a = v2(x)
    u = x >> a
    if u < 5:
        return None
    f = x+a+(u-1)//2
    h = v2(f-1)
    v = (f-1) >> h
    if v < 5:
        return None
    nxt = 1+3**h*v
    assert nxt>x and nxt%2==0
    return a,h,nxt


def sampled_edges(p: int, q: int) -> dict[int,dict[int,tuple[int,int]]]:
    mod = (1 << p)*q
    edges = defaultdict(dict)
    for a in range(1,p+9):
        for u in range(5,1101,2):
            x = (1 << a)*u
            e = even_return(x)
            if e is not None:
                edges[x%mod][e[2]%mod] = e[:2]
        for h in range(18):
            for s in (0,2,10,22,36,84,130):
                precision = a+h+7
                x = inverse_parent(precision,a,h,s)+(1 << precision)*200
                e = even_return(x)
                assert e is not None and e[:2]==(a,h)
                edges[x%mod][e[2]%mod] = (a,h)
    return edges


def lift_and_check(
    p: int, q: int, walk: list[int], letters: list[tuple[int,int]]
) -> None:
    mod = (1 << p)*q
    precision = p
    x = walk[-1] % (1 << p)
    for a,h in reversed(letters):
        precision += a+h+1
        x = inverse_parent(precision,a,h,x)
    dyadic_period = 1 << precision
    if q > 1:
        t = ((walk[0]-x)*pow(dyadic_period,-1,q))%q
        x += dyadic_period*t
    full_period = dyadic_period*q
    x += full_period*1000
    y = x+full_period
    assert x%mod==walk[0]
    alpha = 1
    for i,(a,h) in enumerate(letters):
        e = even_return(x)
        shifted = even_return(y)
        assert e is not None and shifted is not None
        assert e[:2]==shifted[:2]==(a,h)
        x,y = e[2],shifted[2]
        assert x%mod==y%mod==walk[i+1]
        alpha *= 3**h*(1+(1 << (a+1)))
    assert y-x==alpha*(1 << p)*q


def check() -> None:
    rng = Random(602026)
    total = 0
    for p in (1,2,3,4,5,6):
        for q in (1,3,5,7,9,11,15,21,25,35):
            edges = sampled_edges(p,q)
            choices = {r: [(s,ah) for s,ah in out.items() if s in edges]
                       for r,out in edges.items()}
            seeds = [r for r in choices if choices[r]]
            assert seeds
            count = 0
            for _ in range(200):
                walk = [rng.choice(seeds)]
                labels = []
                for _ in range(12):
                    possibilities = choices[walk[-1]]
                    if not possibilities:
                        break
                    s,ah = rng.choice(possibilities)
                    walk.append(s)
                    labels.append(ah)
                    lift_and_check(p,q,walk,labels)
                    count += 1
            total += count
            print(f"PASS p={p}, q={q}: {count} mixed walks",flush=True)
    assert total==143984, total
    print(f"PASS {total} real integer mixed finite-path lifts",flush=True)


if __name__=="__main__":
    check()
