"""Hensel-lift arbitrarily deep genuine Sheep E inverse corridors at fixed v3(j)=7.

For every requested depth T, construct k>=T and a complete exact modular
certificate that the 3^4-normalized Z+12 is divisible by 9^T. The proof in
README converts this to T repeated h0,a2 actual E predecessors and the final
h3,a6 actual E predecessor into 2^(17496*(29+63*k)).
"""
SCALE = 17496
BASE_R = 29
DELTA_J = SCALE * 63
BASE_J = SCALE * BASE_R
DENOM = 3483
OFFSET = 25220


def witness(depth):
    assert isinstance(depth, int) and depth >= 0
    exponent = max(10, 4 + 2 * depth)
    assert pow(2, BASE_J + 10, 3**10) == (-OFFSET) % 3**10
    assert (pow(2, DELTA_J, 3**11) - 1) % 3**11 == 3**10
    assert pow(2, DELTA_J, DENOM) == 1
    assert pow(2, BASE_J + 4, DENOM) == 259
    k = 0
    for q in range(10, exponent):
        modulus = 3 ** (q+1)
        step = 3 ** (q-10)
        # v3(2^(DELTA_J*step)-1) = q: exactly one 3-adic digit lifts.
        assert (pow(2, DELTA_J*step, modulus) - 1) % modulus in (
            3**q, 2*3**q)
        digits = [u for u in (0, 1, 2)
                  if (pow(2, BASE_J+10+DELTA_J*(k+u*step), modulus)
                      + OFFSET) % modulus == 0]
        assert len(digits) == 1, (q,digits)
        k += digits[0]*step
        assert (pow(2, BASE_J+10+DELTA_J*k, modulus)+OFFSET)%modulus == 0
    # Move to a large positive representative in the same 3-adic cylinder.
    period = 3**(exponent-10)
    k += (depth+1)*period
    j = BASE_J + DELTA_J*k
    assert j>=depth+10
    assert (pow(2, j+10, 3**exponent)+OFFSET)%3**exponent==0
    assert pow(2, j+4, DENOM)==259
    # (Z+12)=(2^(j+10)+25220)/3483;
    # 3483 has exactly v3=4, so v3(Z+12)>=2*depth.
    assert DENOM%3**4==0 and DENOM%3**5!=0
    return k, j, exponent


def main():
    for depth in (0, 1, 2, 3, 4, 5, 6, 10, 20, 40, 100):
        k,j,q = witness(depth)
        print(f"T={depth:3d}: k has {len(str(k))} digits,"
              f" j has {len(str(j))} digits;"
              f" 3^{q} divides 2^(j+10)+25220; root source period valid")
    print('PASS: all T accepted by constructive 3-adic one-digit lifting')


if __name__ == '__main__':
    main()
