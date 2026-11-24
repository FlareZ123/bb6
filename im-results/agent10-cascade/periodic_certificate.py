"""Exact infinite-period certificate test for the #746 reset grammar.

A word is a nonempty tuple of (valuation a, sweep increment delta).
No floating point, simulation cutoff, or external package is used.
See PresburgerPeriodicity.md for the proof of the finite criterion.
"""
from fractions import Fraction as F
from math import gcd, lcm


def advance(coeff, token):
    """Map X(k)=alpha*2**k+beta*k+gamma through one token."""
    alpha, beta, gamma = coeff
    a, delta = token
    r = F(3**a, 2**(a+1))
    beta_next = r*(beta+2)
    return r*(alpha+16)/2**delta, beta_next, r*(gamma+5)-beta_next*delta


def coefficients(word):
    """Unique periodic phase coefficients; returns (D, phases)."""
    if not word or any(a < 0 or d < 0 for a, d in word):
        raise ValueError('word must be nonempty with nonnegative tokens')
    D = sum(d for _, d in word)
    if not D:
        raise ValueError('an infinite valid itinerary must increase the sweep level')
    const = (F(0), F(0), F(0))
    R_over_P = F(1)
    for token in word:
        const = advance(const, token)
        a, _ = token
        R_over_P *= F(3**a, 2**(a+1))
    c0, c1, c2 = const
    alpha = c0/(1-R_over_P/2**D)
    beta = c1/(1-R_over_P)
    gamma = (c2-R_over_P*beta*D)/(1-R_over_P)
    start = (alpha, beta, gamma)
    phases = []
    d0 = 0
    coeff = start
    for token in word:
        phases.append((d0, coeff))
        coeff = advance(coeff, token)
        d0 += token[1]
    assert coeff == start
    return D, phases


def value(coeff, k):
    alpha, beta, gamma = coeff
    return alpha*2**k+beta*k+gamma


def positive_for_all(A, B, C, k, D):
    """Check A*2**(k+jD)+B*(k+jD)+C > 0 for all j>=0."""
    if A < 0 or (A == 0 and B < 0):
        return False
    if A == 0:
        return B*k+C > 0
    G = 2**D
    if A*(G-1)*2**k+B*D >= 0:
        j = 0
    else:
        lo, hi = 0, 1
        while A*(G-1)*2**(k+hi*D)+B*D < 0:
            lo, hi = hi, 2*hi
        while hi-lo > 1:
            mid = (lo+hi)//2
            if A*(G-1)*2**(k+mid*D)+B*D < 0:
                lo = mid
            else:
                hi = mid
        j = hi
    kk = k+j*D
    return A*2**kk+B*kk+C > 0


def eventually_positive(A, B, C):
    return A > 0 or (A == 0 and (B > 0 or (B == 0 and C > 0)))


def band_gaps(coeff):
    alpha, beta, gamma = coeff
    return ((alpha-8,beta+2,gamma+3), (16-alpha,-beta-2,-gamma-5))


def odd_integral(x):
    return x.denominator == 1 and x.numerator % 2 == 1


def certify(word, h, k):
    """Return exact iff: the prepared (h,k) follows word forever."""
    if h < 0 or k < 0:
        return False
    D, phases = coefficients(word)
    if value(phases[0][1], k) != 2*h+5:
        return False
    if not all(odd_integral(value(phases[0][1],k+j*D)) for j in range(3)):
        return False
    for offset, coeff in phases:
        kk = k+offset
        if not all(positive_for_all(*gap,kk,D) for gap in band_gaps(coeff)):
            return False
        A,B,C = coeff
        if not positive_for_all(A,B,C-4,kk,D):
            return False
    return True


def possible_prepared_period(word):
    """Exact existence test for an arbitrarily late prepared period.

    Returns a residue/period of suitable sufficiently large starting
    levels or None. The order scan can be expensive for large words.
    """
    D, phases = coefficients(word)
    if any(not eventually_positive(*g) for _, c in phases for g in band_gaps(c)):
        return None
    c = phases[0][1]
    Q = lcm(*(v.denominator for v in c))
    assert Q % 2 == 1
    A, B, C = (int(v*Q) for v in c)
    G = 2**D
    if A*(G-1)**2 % Q:
        return None
    modulus = 2*Q
    order, z = 1, 2 % Q
    if Q != 1:
        while z != 1:
            z = 2*z % Q
            order += 1
    g = gcd(B,modulus)
    H = modulus//g
    cgh = gcd(order,H)
    for s in range(1,order+1):
        p = pow(2,s,modulus)
        if (A*(G-1)*p+B*D) % modulus:
            continue
        rhs = Q-C-A*p
        if rhs % g:
            continue
        t = (rhs//g*pow(B//g,-1,H)) % H if H != 1 else 0
        if (t-s) % cgh:
            continue
        h = H//cgh
        j = ((t-s)//cgh*pow(order//cgh,-1,h)) % h if h != 1 else 0
        period = lcm(order,H)
        return (s+order*j)%period, period
    return None


if __name__ == '__main__':
    from itertools import product
    tokens = [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)]
    tested = feasible = 0
    for length in range(1,5):
        for word in product(tokens,repeat=length):
            if not any(d for _,d in word):
                continue
            D, phases = coefficients(word)
            for k in (0,11):
                for i,(offset,c) in enumerate(phases):
                    a,d = word[i]
                    next_offset,next_c = phases[(i+1)%length]
                    if i==length-1:
                        next_offset += D
                    assert next_offset == offset+d
                    assert 2**(a+1)*value(next_c,k+next_offset) == 3**a*(value(c,k+offset)+16*2**(k+offset)+2*(k+offset)+5)
            tested += 1
            alpha = phases[0][1][0]
            if (alpha*(2**D-1)**2).denominator != 1:
                continue
            if possible_prepared_period(word) is not None:
                feasible += 1
                print('prepared period candidate',word)
    assert positive_for_all(F(1),F(-10),F(50),0,1)
    assert not positive_for_all(F(1),F(-10),F(10),0,1)
    assert not positive_for_all(F(-1),F(0),F(100),0,1)
    assert positive_for_all(F(0),F(1),F(1),0,1)
    print(f'exact phase algebra: {tested} words; feasible prepared periods: {feasible}')
