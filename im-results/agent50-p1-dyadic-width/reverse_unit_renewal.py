"""Exact n-bit renewal certificates for the two P1 restart families.

No float decisions. A block is returned only when the proven separation
inequalities hold. It certifies the whole unit word and both margins at every
intermediate state, rather than merely sampling an endpoint.
"""
from fractions import Fraction as F
from math import gcd
import argparse

FAMILIES = {
    'I': (5362, 595056, 17, 1058, 636),
    'II': (9538, 703248, 87, 1198, 712),
}
Q1 = 71613580229214242991980556803097867963140694204416
PHASE = {
    'I': (F(20013775836248574773416784117434897071012058217091, Q1), F(71731, 100352)),
    'II': (F(29332545262092636321770706426635052127421016820935, Q1//2), F(78165, 100352)),
}

def frac(x):
    return x - x.numerator // x.denominator

def vprime(x, p):
    assert x != 0
    k = 0
    while x % p == 0:
        k += 1
        x //= p
    return k

def ceil_log2(x):
    assert x > 0
    k = x.numerator.bit_length() - x.denominator.bit_length()
    scale = F(1 << k) if k >= 0 else F(1, 1 << -k)
    return k + (scale < x)

def weighted_word(w, n):
    """sum_{i=1}^n i * bit_i(w) * 2^(n-i), O(log^2 n) shifts/masks."""
    assert n >= 0 and 0 <= w < 1 << n
    s = 0
    p = 1
    while p < n:
        mask = ((1 << p) - 1) << p
        width = 2*p
        while width < n:
            mask |= mask << width
            width *= 2
        s += p * (w & mask)
        p *= 2
    return n*w - s

def binary_moment(r, period):
    """sum i*x_i*2^-i for canonical expansion, given an exact period multiple."""
    assert 0 <= r < 1
    e = vprime(r.denominator, 2)
    odd = r.denominator >> e
    prefix, tail = divmod(r.numerator, odd)
    tail = F(tail, odd)
    v = F(weighted_word(prefix, e), 1 << e)
    if not tail:
        return v
    m = (1 << period) - 1
    assert m % odd == 0
    w = tail.numerator * (m//tail.denominator)
    return v + F(1,1 << e) * (e*tail + (weighted_word(w, period)+period*tail)/m)

def initial(family, h):
    n0, dn, au, bu, cu = FAMILIES[family]
    n = n0 + dn*h
    P = 1 << n
    u, rem = divmod(au*P-cu, bu)
    assert rem == 0
    q = 7*P-14*u+n
    d, rem = divmod(18*P-196*u+14*n+48, 98)
    assert rem == 0
    m = 14*u-2*n-3
    A = F(7) - F(14*au, bu)
    r = (F(18)-F(196*au,bu))/(98*A)
    assert 0 < d < q and (q-d)%2 == 0
    assert q+m == 7*P-n-3
    return n, q, d, m, A, r

def block(q,d,n,A,r,period):
    """Return exact endpoint, word and next rational phase if all checks pass.

    Let a=q-A*P, b=d-A*P*r, B bound P*abs(U_n/P-r).
    The integer K chosen here guarantees K matching leading digits, and a
    separation check forces U_n=floor(T). See the accompanying proof.
    """
    P = 1 << n
    AP = A*P
    a = q-AP
    b = d-AP*r
    mu = binary_moment(r,period)
    T = (d-a*r-mu)/A
    U = T.numerator//T.denominator
    rho = frac(T)
    assert 0 < rho < 1
    Q, R = r.denominator, rho.denominator
    B = (abs(b)+abs(a)+2+F(q+n,P))/A
    K = n - ceil_log2(4*Q*B)
    if not (0 < K <= n):
        return None
    E = F(P,1<<K)*(abs(a)+K+2)
    if not AP/R > E+abs(a+n):
        return None
    early = AP/Q-(1<<K)*(abs(b)+abs(a)+2)
    late = AP/(R*(1<<(n-K)))-E
    if min(early,late) <= abs(a)+n+8:
        return None
    assert 0 <= U < P
    V = weighted_word(U,n)
    dnew = P*d-q*U-V
    assert 2 <= dnew <= q+n-8
    assert abs(dnew-AP*rho) <= E
    return dnew, U, rho, K, E

def direct(q,d,n):
    w = 0
    min_low, min_high = d,q-d
    for j in range(1,n+1):
        d *= 2
        q += 1
        x = int(d >= q)
        d -= x*q
        w = 2*w+x
        min_low = min(min_low,d)
        min_high = min(min_high,q-d)
    return d,w,min_low,min_high

def phase_tables():
    assert Q1.bit_length() == 166
    assert vprime(Q1,127) == 1
    assert pow(2,7203,Q1 >> vprime(Q1,2)) == 1
    for f,(base,step) in PHASE.items():
        assert base.denominator % 127 == 0 and gcd(base.denominator,127**2) == 127
        assert step.denominator == 100352 and step.denominator % 127 != 0
        n,q,d,m,A,r = initial(f,0)
        P=1<<n
        mu=binary_moment(r,147)
        assert frac((d-(q-A*P)*r-mu)/A)==base
        # Derive phase increment symbolically, without building the next P.
        _,dn,au,bu,cu=FAMILIES[f]
        assert frac(F(1,7)-r) == F(1,7)-r
        assert frac((F(1,7)-r)*dn/A)==step
        assert pow(2,dn,r.denominator >> vprime(r.denominator,2)) == 1
        print(f, 'phase period =',step.denominator,'v127(denom)=1; common odd period divides 7203')

def test(f,h,blocks,compare=False):
    n,q,d,m,A,r=initial(f,h)
    print(f'h={h} family={f}, n={n}', flush=True)
    for i in range(blocks):
        period = (147,7203)[i] if i<2 else None
        if period is None:
            raise ValueError('The third period is not a practical numerical constant; use the theorem.')
        ans=block(q,d,n,A,r,period)
        if ans is None:
            print(' block',i+1,'separation test not certified',flush=True)
            return
        dn,U,rho,K,E=ans
        if i==0:
            a,b=PHASE[f]
            assert rho==frac(a+h*b)
        assert vprime(rho.denominator,127)==i+1
        if compare:
            de,we,lo,hi=direct(q,d,n)
            assert (de,we)==(dn,U)
            assert lo>=2 and hi>=8
        print(' block',i+1,'exact, shared digits',K,'phase denominator bits',rho.denominator.bit_length(),
              'v127',vprime(rho.denominator,127),'crossings',U.bit_count(),
              'last crossing offset',n-(U&-U).bit_length()+1 if U else 0,flush=True)
        q+=n;d=dn;r=rho
    assert m>n*blocks

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--family',choices=FAMILIES)
    ap.add_argument('--h',type=int,default=0)
    ap.add_argument('--blocks',type=int,default=1,choices=(1,2))
    ap.add_argument('--compare',action='store_true')
    args=ap.parse_args()
    phase_tables()
    if args.family:
        test(args.family,args.h,args.blocks,args.compare)
    else:
        for family in FAMILIES:
            test(family,0,1,True)
            test(family,1,2)
