"""Exact two-coordinate necessary search for periodic #746 reset itineraries.

D is the total sweep-level increase of a nonempty period. All arithmetic is
integer or Fraction; the search includes every possible primitive period of
increment D, without enumerating the slope denominator graph of size 4**D.
"""
from fractions import Fraction as F
from math import gcd
from time import perf_counter
import argparse


def remove23(x):
    assert x > 0
    while x % 2 == 0:
        x //= 2
    while x % 3 == 0:
        x //= 3
    return x


def valuation_bound(D):
    a = D
    while 3**(a+1) < 2**(a+1+D):
        a += 1
    return a


def small_bound(P, R, L):
    """Integer B bounding the minimum |beta/2| of a cycle."""
    hi0, lo0 = max(P, R), min(P, R)
    assert hi0 > lo0
    def ok(m):
        return (m+1)**L*lo0 <= m**L*hi0
    lo, hi = 0, 1
    while not ok(hi):
        lo, hi = hi, 2*hi
    while hi-lo > 1:
        mid = (hi+lo)//2
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi + (P < R)


def denominator_caps(D):
    """Return (odd lifted denominator, sign, magnitude bound) triples.

    For any hypothetical valid periodic solution, the common reduced
    denominator r of beta/2 divides at least one cap of the right sign,
    and some phase lies in the corresponding bounded scan interval.
    """
    G = 2**D
    H = remove23((G-1)**2)
    J = remove23(D)
    am = valuation_bound(D)
    caps = {}
    pair_count = 0
    if H == 1:
        return [], pair_count
    for A in range(D, am+1):
        lo, hi = max(1, am+1-A), A*(2*D-2)
        p = pow(2, A+D+lo, H)
        R = 3**A
        r = R % H
        pos_cut = R.bit_length()-A
        for L in range(lo, hi+1):
            g = gcd(p-r, H)
            if g > 1:
                pair_count += 1
                s = g//gcd(g, G-1)
                modulus = J*s
                cap = gcd(pow(2,A+L,modulus)-R%modulus, modulus)
                sign = 1 if L >= pos_cut else -1
                key = cap, sign
                old = caps.get(key, 1)
                if L >= 2*A:
                    # 3**(A+L) <= 2**(A+2*L) since 27<32 and 3<4.
                    caps[key] = max(old, 2)
                else:
                    P = 2**(A+L)
                    m = old-(sign<0)
                    if m < 1 or (m+1)**L*min(P,R) > m**L*max(P,R):
                        caps[key] = small_bound(P,R,L)
            p = 2*p % H
    # Multiplying an odd numerator and denominator by the same odd number
    # preserves the recurrence and its exact binary valuation. Thus one
    # larger cap covers every divisor with an equal or smaller bound.
    keep = []
    for (cap, sign), B in sorted(caps.items(), key=lambda kv: kv[0][0], reverse=True):
        if not any(s == sign and R % cap == 0 and U >= B for R,s,U in keep):
            keep.append((cap, sign, B))
    return keep, pair_count


def beta_cycles(D, caps):
    """All relevant rational beta cycles, deduplicated by minimal phase."""
    am = valuation_bound(D)
    lm = am*(2*D-2)
    powers3 = [3**a for a in range(am+1)]
    cycles = {}
    starts = 0
    for cap, sign, B in caps:
        for p_abs in range(cap+2, B*cap+1, 2):
            starts += 1
            start = sign*p_abs
            p = start
            word = []
            A = 0
            visited = {p}
            for _ in range(lm):
                s = p+cap
                if not s:
                    break
                u = abs(s)
                a = (u & -u).bit_length()-2
                assert a >= 0
                A += a
                if A > am:
                    break
                p = (s >> (a+1))*powers3[a]
                word.append(a)
                if abs(p) < p_abs:
                    break
                if p == start:
                    if A:
                        g = gcd(p_abs,cap)
                        cycles[(start//g,cap//g)] = tuple(word)
                    break
                if p in visited:
                    break
                visited.add(p)
    return cycles, starts


def normalized_branches(a):
    """Possible (delta, c) for z' = c*(z+1), 1/2<z,z'<1."""
    r = F(3**a,2**(a+1))
    return [(d,r/2**d) for d in range(a+1)
            if F(3,2)*r/2**d < 1 and 2*r/2**d > F(1,2)]


def slope_fixed_points(valuations, D):
    """Every strict-band fixed point with the specified valuation word.

    Each live interval is open. Its slope is represented as m*z+b, where
    z is the initial normalized slope. There are at most L+1 pieces before
    pruning, since each one-step map is injective with at most one seam.
    """
    pieces = [(F(1,2),F(1),F(1),F(0),0)]
    remaining = sum(valuations)
    branches = {a:normalized_branches(a) for a in set(valuations)}
    for a in valuations:
        remaining -= a
        next_pieces = []
        for lo,hi,m,b,d0 in pieces:
            for d,c in branches[a]:
                dd = d0+d
                if dd > D or dd+remaining < D:
                    continue
                mm,bb = c*m,c*(b+1)
                l = max(lo,(F(1,2)-bb)/mm)
                h = min(hi,(1-bb)/mm)
                if l < h:
                    next_pieces.append((l,h,mm,bb,dd))
        pieces = next_pieces
        if not pieces:
            return []
    out = []
    for lo,hi,m,b,dd in pieces:
        assert dd == D
        if m < 1:
            z = b/(1-m)
            if lo < z < hi:
                out.append(z)
    return out


def recover_tokens(valuations,z):
    word = []
    initial = z
    for a in valuations:
        choices = [(d,c*(z+1)) for d,c in normalized_branches(a) if F(1,2)<c*(z+1)<1]
        assert len(choices)==1
        d,z = choices[0]
        word.append((a,d))
    assert z==initial
    return tuple(word)


def primitive(word):
    for l in range(1,len(word)+1):
        if len(word)%l==0 and word==word[:l]*(len(word)//l):
            return word[:l]
    raise AssertionError


def search(D):
    am = valuation_bound(D)
    G = 2**D
    H = remove23((G-1)**2)
    caps,pairs = denominator_caps(D)
    cycles,starts = beta_cycles(D,caps)
    checked = fixed = 0
    survivors = set()
    for (p,r),aword in cycles.items():
        A0,L0 = sum(aword),len(aword)
        for reps in range((D+A0-1)//A0,am//A0+1):
            A,L=A0*reps,L0*reps
            if not max(1,am+1-A)<=L<=A*(2*D-2):
                continue
            g = gcd(pow(2,A+L+D,H)-pow(3,A,H),H)
            if g==1 or (g//gcd(g,G-1))%(r//gcd(r,D)):
                continue
            vals=aword*reps
            checked += 1
            for z in slope_fixed_points(vals,D):
                fixed += 1
                q=z.denominator
                if q<=1 or gcd(q,6)!=1 or z.numerator%2!=1 or H%q:
                    continue
                if q//gcd(q,G-1)!=r//gcd(r,D):
                    continue
                word=primitive(recover_tokens(vals,z))
                d=sum(dd for _,dd in word)
                if (2**d-1)**2%q or q//gcd(q,2**d-1)!=r//gcd(r,d):
                    continue
                # Canonical word rotation for reporting.
                word=min(word[i:]+word[:i] for i in range(len(word)))
                survivors.add((q,r,word))
    return pairs,len(caps),starts,len(cycles),checked,fixed,sorted(survivors)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('maxD',type=int)
    ap.add_argument('--minD',type=int,default=1)
    args=ap.parse_args()
    total=0
    for D in range(args.minD,args.maxD+1):
        t=perf_counter()
        pairs,caps,starts,cycles,checked,fixed,survivors=search(D)
        total+=len(survivors)
        print(f'D={D} pairs={pairs} caps={caps} beta_starts={starts} beta_cycles={cycles} slope_words={checked} slope_fixed={fixed} survivors={len(survivors)} seconds={perf_counter()-t:.3f}',flush=True)
        for q,r,word in survivors:
            print(f'  SURVIVOR q={q} r={r} word={word}',flush=True)
    print(f'total survivors={total}',flush=True)


if __name__=='__main__':
    main()
