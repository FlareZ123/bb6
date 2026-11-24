"""Exact constants and endpoint regressions for the P1 4n+2 obstruction.

The universal argument is in RenewalCost.md. Regressions are not a proof
of the universal statement. All arithmetic is integer or Fraction.
"""
from fractions import Fraction


def v7(x):
    assert x != 0
    v = 0
    while x % 7 == 0:
        x //= 7
        v += 1
    return v


def weighted_word(u):
    l = u.bit_length()
    return sum((l-i) << i for i in range(l) if u >> i & 1), l


def left_weight(u, length):
    w, l = weighted_word(u)
    return w + (length-l)*u


def moment(r, period):
    M = (1 << period)-1
    u = M*r
    assert u.denominator == 1
    return (left_weight(u.numerator, period)+period*r)/M


def denominators():
    D = [7]
    L = [3,147,7203]
    for i, l in enumerate(L):
        d = D[-1]
        e = 2*i+1
        assert v7(d) == e and v7(l) == e-1
        assert pow(2,l,d) == 1
        assert v7((1 << l)-1) == e
        D.append(7*d*((1 << l)-1)//7**(e-1))
        assert v7(D[-1]) == e+2
    assert D[1] == 343
    assert D[2] < 1 << 153
    assert D[3] < 1 << 7359
    return D, L


def constants(n):
    D,L = denominators()
    P = 1 << n
    assert n >= 8000
    assert 2*16**7 > 17**7
    assert 1 << 8000 > (1 << 7729)*8000**7
    assert P > (1 << 7729)*n**7
    A = 5*n
    B = [5*n, (1 << 12)*n**2, (1 << 27)*n**3, (1 << 186)*n**4]
    assert A+n <= P
    for i in range(3):
        H = A+B[i]+10
        S = 1 << (2*D[i]*H-1).bit_length()
        E = (A+n+2)*S
        assert S <= P and E <= B[i+1]
        assert 7*P > D[i+1]*S*(E+A+n+8)
    return D,L,B


def run_block(q, d, n, r, period, D_next):
    P = 1 << n
    a = q-7*P
    T = (d-a*r-moment(r,period))/7
    U = T.numerator//T.denominator
    rho = T-U
    assert 0 < rho < 1 and D_next % rho.denominator == 0
    assert v7(rho.denominator) == v7(r.denominator)+2
    assert 0 <= U < P
    expected = P*d-q*U-left_weight(U,n)
    u = 0
    for j in range(1,n+1):
        x,d = divmod(2*d,q+j)
        assert x in (0,1)
        u = 2*u+x
        assert 2 <= d <= q+j-8
    assert u == U and d == expected
    return q+n,d,rho


def regression(n,k):
    D,L,B = constants(n)
    P = 1 << n
    q = 7*P-n-3-k
    d = 1
    for j in range(1,n+4):
        d = 2*d%(q+j)
        assert d != 1
    q += n+3
    assert q == 7*P-k and d == P+k
    r = Fraction(1,7)
    for i in range(3):
        assert abs(d-7*P*r) <= B[i]
        q,d,r = run_block(q,d,n,r,L[i],D[i+1])
    assert abs(d-7*P*r) <= B[3]
    print(f'n={n}, k={k}: all three exact block endpoints and guards agree')


if __name__ == '__main__':
    D,L = denominators()
    print('denominator bit lengths:', [d.bit_length() for d in D])
    for n,k in [(8000,8003),(8000,32003),(10002,40011)]:
        regression(n,k)
