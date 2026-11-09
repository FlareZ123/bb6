"""Exact regression for all-depth Sheep first-even power-parent formulas.

The unbounded theorem is proved algebraically and by induction in README.md.
This executable certificate tests independent modular and literal witnesses.
Python 3.10+ standard library only.
"""

def first_even(x: int) -> tuple[int, int, int]:
    a = (x & -x).bit_length() - 1
    v = x >> a
    assert a >= 1 and v >= 5 and v % 2 == 1
    z = x + a + (v - 1)//2
    h = ((z - 1) & -(z - 1)).bit_length() - 1
    return 1 + 3**h * ((z - 1) >> h), a, h

def verify() -> None:
    assert pow(2, 24, 81) == 10
    seen_a2 = seen_a6 = 0
    for n in range(1, 65):
        d = 3**(n+1)
        assert pow(2, 8*3**n, 9*d) == 1 + d
        for t in range(1, 23):
            if t % 3 == 0:
                continue
            j = 8*3**n*t
            u9 = (pow(2, j, 9*d) - 1)//d
            assert u9 == t%9
            good = (pow(2, n+2, 9)*t-1) % 9 == 0
            assert (((pow(2, j+n+2, 9*d)-2**(n+2)-d)%(9*d)==0) == good)
            if n <= 5 and t <= 12 and good:
                u = (2**j-1)//d
                v = (2**(n+2)*u-1)//9
                x = 4*v
                assert v >= 5 and v%2 == 1
                assert first_even(x) == (2**j, 2, n+1)
                seen_a2 += 1

        if n >= 3:
            assert pow(2,8*3**n,81) == 1
            for t in range(1,23):
                j = 8*3**n*t
                good = (4*3**n*t-5) % 7 == 0
                assert (((pow(2,j+4,3483)-259)%3483)==0) == good
                if n <= 5 and t <= 12 and good:
                    v = (2**(j+4)-259)//3483
                    x = 64*v
                    assert v >= 5 and v%2 == 1
                    assert first_even(x) == (2**j, 6, 3)
                    seen_a6 += 1
    assert seen_a2 > 0 and seen_a6 > 0
    print('PASS: 64 parameter depths, 22 t values, and all tested congruence gates')
    print('PASS: literal original-source section return witnesses: a2', seen_a2,
          'a6,h3', seen_a6)
    print('Note: universal claims depend on the mathematical induction in README.md')

if __name__ == '__main__':
    verify()
