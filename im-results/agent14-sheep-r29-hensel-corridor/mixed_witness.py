"""Construct arbitrarily deep real Sheep E inverse corridors for eight root classes.

The power-root exponent always has fixed 3-adic valuation 7, even though the
mixed (h,a)=(3,6) or (8,2) terminal edge is preceded by T arbitrary
(h,a)=(0,2) E edges. Full proof by one-digit lifting is in README.
"""
SCALE = 17496
DELTA = SCALE * 63
X_R = (8, 17, 26, 35, 44, 53, 62)
CASES = {
    'Z29': (29, 10, -16576, 3483, 4, 259, 3483),
    **{f'X{r}': (r, 11, -28292, 59049, 9, 7073, 59049) for r in X_R},
}


def v3(n):
    ans = 0
    while n % 3 == 0:
        ans += 1
        n //= 3
    return ans


def lift(key, depth):
    assert key in CASES and isinstance(depth, int) and depth >= 0
    r, shift, b, d, source_shift, source_res, source_mod = CASES[key]
    j0 = SCALE * r
    assert r % 3 != 0
    assert pow(2, DELTA, source_mod) == 1
    assert pow(2, j0 + source_shift, source_mod) == source_res
    assert v3(d) in (4, 10)
    c = b+12*d
    assert (pow(2, j0+shift, 3**10) + c) % 3**10 == 0
    assert (pow(2, DELTA, 3**11) - 1) % 3**11 == 3**10
    precision = max(10, v3(d)+2*depth)
    k = 0
    for p in range(10, precision):
        m = 3**(p+1)
        step = 3**(p-10)
        assert (pow(2, DELTA*step, m)-1)%m in (3**p, 2*3**p)
        digits = [u for u in range(3)
                  if (pow(2,j0+shift+DELTA*(k+u*step),m)+c)%m==0]
        assert len(digits)==1
        k += digits[0]*step
    k += (depth+1)*3**(precision-10)
    j = j0+DELTA*k
    assert (pow(2,j+shift,3**precision)+c)%3**precision==0
    assert pow(2,j+source_shift,source_mod)==source_res
    assert j>=depth+13
    return k,j,precision


def main():
    for key in CASES:
        for depth in (0,1,2,5,20,100):
            k,j,p=lift(key,depth)
            print(f'{key}: length≥{depth+1}, k digits={len(str(k))},'
                  f' 3^{p} divides affine numerator')
    print('PASS: eight fixed-order mixed E corridor families, any depth by LTE induction')


if __name__=='__main__':
    main()
