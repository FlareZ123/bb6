"""Standalone exact-integer regression for universal coherent Sheep dyadic diameter.

A coherent itinerary consists of consecutive *genuine* generic even-return
steps from ONE chosen integer. This checker makes no claim about the unique
blank-tape origin (even section 10). No external modules or network needed.
"""
from math import comb


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def decode(p: int, source: int) -> list[tuple[int, int]]:
    word = []
    while source:
        a = v2(source)
        u = source >> a
        C = (1+2**(a+1))*u+2*a-3
        h = min(v2(C)-1, p-a-1)
        assert a >= 1 and h >= 0
        word.append((a,h))
        p -= a+h+1
        source = (1+3**h*(C >> (h+1))) % (2**p) if p else 0
        assert source%2 == 0
    return word


def inverse(p: int, a: int, h: int, target: int) -> int:
    mod = 2**(p-a)
    D = 1+2**(a+1)
    return 2**a*((3-2*a+2**(h+1)*pow(3**h,-1,mod)*(target-1))
                 *pow(D,-1,mod)%mod)


def apply_word(p: int, word: list[tuple[int,int]], target: int) -> int:
    for a,h in reversed(word):
        target = inverse(p,a,h,target)
    return target


def generic(x: int) -> tuple[int,int,int]:
    """One positive authentic generic Sheep first-even return."""
    a = v2(x)
    u = x >> a
    assert a >= 1 and u >= 5 and u%2 == 1
    z = x+a+(u-1)//2
    h = v2(z-1)
    v = (z-1) >> h
    assert v >= 5 and v%2 == 1
    return a,h,1+3**h*v


def follow(x: int, word: list[tuple[int,int]]) -> int:
    for a,h in word:
        actual_a,actual_h,x = generic(x)
        assert (a,h) == (actual_a,actual_h)
    return x


def construct(p: int, source: int, target: int) -> tuple[int,int]:
    word = decode(p,source)
    k = p//2
    j = len(word)
    C = sum(a+h+1 for a,h in word)
    P = p+C
    L = 2**P
    M = 2**p

    if j == k:
        # Target-saturated inverse word; lift with p+C bits to retain every h.
        x = apply_word(P,word,target)+100*L
        assert x%M == source
        y = follow(x,word)
        assert y%M == target
        return x,j

    # Short canonical path to zero, then a single genuine even-outgoing hub.
    x0 = apply_word(P,word,0)+100*L
    assert x0%M == source
    y0 = follow(x0,word)
    assert y0%M == 0
    alpha = 1
    for a,h in word:
        alpha *= 3**h*(1+2**(a+1))
    assert follow(x0+L,word)-y0 == alpha*M

    desired_u = (1+2*(target-p)) % (2**(p+1))
    shift = ((desired_u-y0//M)*pow(alpha,-1,2**(p+1))) % (2**(p+1))
    x = x0+L*shift
    y = follow(x,word)
    if y >> p < 5:
        x += L*2**(p+1)
        y = follow(x,word)
    assert y%M == 0 and v2(y) == p and y>>p >= 5
    actual_a,actual_h,z = generic(y)
    assert actual_a == p and actual_h == 0 and z%M == target
    return x,j+1


def run() -> None:
    maximal_pairs = 0
    shorter_pairs = 0
    for p in range(1,16):
        M = 2**p
        k = p//2
        words = [(r,decode(p,r)) for r in range(0,M,2)]
        maximal = [r for r,w in words if len(w) == k]
        assert len(maximal) == comb(p,2*k)
        for source in maximal:
            for target in range(0,M,2):
                x,length = construct(p,source,target)
                assert x%M == source and length <= k
                maximal_pairs += 1
        if p <= 9:
            for source,word in words:
                if len(word) == k:
                    continue
                for target in range(0,M,2):
                    x,length = construct(p,source,target)
                    assert x%M == source and length <= k
                    shorter_pairs += 1
        print(f"PASS p={p}: {len(maximal)} maximal-code sources, coherent distance <= {k}",flush=True)
    print(
        f"PASS {maximal_pairs} maximal-shell and {shorter_pairs} shorter-shell "
        "single-source genuine generic trajectories",
        flush=True,
    )


if __name__ == "__main__":
    run()
