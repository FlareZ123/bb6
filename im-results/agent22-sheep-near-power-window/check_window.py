"""Exact offset-driven safe windows for Sheep; no physical high state needed."""
from math import isqrt


def generic(x):
    b = (x & -x).bit_length() - 1
    u = x >> b
    return x + b + (u - 1)//2, b + 1


def bound(a, b):
    L = b.bit_length()
    # maximal r >= 0 with (r+1)*L + r*(r+1)//2 <= a
    if a < L:
        return -1
    r = (isqrt((2*L-1)**2 + 8*a) - (2*L+1))//2
    assert r >= 0 and (r+1)*L + r*(r+1)//2 <= a
    assert (r+2)*L + (r+1)*(r+2)//2 > a
    return r


def adaptive(a, b):
    """Return max r with c + bit_length(B_r) <= a, or -1 if none."""
    c = r = 0
    if b.bit_length() > a:
        return -1
    while True:
        z, q = generic(b)
        if c + q + z.bit_length() > a:
            return r
        c += q
        r += 1
        b = z


def literal_special(a, r):
    """Validate the entire claimed prefix with actual source arithmetic."""
    x = (3 << a) + a + 3
    b = a + 3
    c, C = 0, 3
    for i in range(r+1):
        assert b.bit_length() + c <= a
        assert x == (C << (a-c)) + b
        assert x >> ((x & -x).bit_length()-1) >= 5
        if i < r:
            x, q = generic(x)
            b, p = generic(b)
            assert p == q
            c += q
            C *= (1 << q) + 1


if __name__ == '__main__':
    print('a\tworst r\tadaptive r (following the first special return)')
    for a in [100, 1201, 2659, 10000, 100000]:
        w = bound(a, a+3)
        r = adaptive(a, a+3)
        assert r >= w
        if a <= 10000:
            literal_special(a, r)
        print(f'{a}\t{w}\t{r}')
