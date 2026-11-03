"""Coherent finite Sheep even-orbit congruence hitting theorem, exact witnesses.

Unlike quotient paths whose edges may use separate inputs, each reported
path here is obtained by iterating E from ONE starting positive even integer.
This starting state is an arbitrary large residue representative, not the
original blank-tape section entry 10.
"""
from verify_dyadic_complete import decode, encode, even_return, v2
from verify_mixed_complete import crt2, direct_even
from verify_mixed_any_target import choose_target_exponent


def coherent_orbit(p: int, q: int, r: int, s: int) -> tuple[int, tuple[int, ...]]:
    assert p >= 1 and q >= 1 and q % 2 == 1
    m2 = 1 << p
    modulus = m2*q
    assert 0 <= r < modulus and r % 2 == 0
    assert 0 <= s < modulus and s % 2 == 0
    word = decode(p, r % m2)
    cost = sum(a+h+1 for a, h in word)
    precision = p+cost
    dyadic_start = encode(precision, word)
    period = (1 << precision)*q
    start = crt2(dyadic_start, 1 << precision, r % q, q) + 10*period
    assert start % modulus == r

    def iterate(x: int) -> tuple[int, tuple[int, ...]]:
        states = [x]
        for required_a, required_h in word:
            a = v2(x)
            u = x >> a
            assert a == required_a and u >= 5
            f = x+a+(u-1)//2
            h = v2(f-1)
            assert h == required_h
            y = even_return(x)
            assert y is not None and y == direct_even(x)
            states.append(y)
            x = y
        return x, tuple(states)

    intermediate, _ = iterate(start)
    assert intermediate % m2 == 0
    slope_numerator = 1
    for a, h in word:
        slope_numerator *= 3**h * ((1 << (a+1))+1)
    shifted, _ = iterate(start+period)
    assert shifted-intermediate == slope_numerator*m2*q

    a_final = choose_target_exponent(q, intermediate % q, s, p)
    precision_final = a_final+p+1
    high_mod = 1 << precision_final
    required = ((1 << a_final)*(1+2*(s-a_final))) % high_mod
    assert (required-intermediate) % m2 == 0
    k = (((required-intermediate)//m2) *
         pow(slope_numerator*q, -1, 1 << (a_final+1))) % (1 << (a_final+1))
    x = start+k*period
    last, trajectory = iterate(x)
    while last >> a_final < 5:
        k += 1 << (a_final+1)
        x = start+k*period
        last, trajectory = iterate(x)
    assert last % high_mod == required
    assert v2(last) == a_final and last >> a_final >= 5
    target = even_return(last)
    assert target is not None and target == direct_even(last)
    assert target == last+a_final+((last >> a_final)-1)//2
    assert target % modulus == s
    assert trajectory[0] % modulus == r
    assert len(trajectory) <= p//2+1
    return x, trajectory+(target,)


def verify() -> None:
    count = 0
    max_bits = 0
    max_len = 0
    for p in range(1, 8):
        for q in (1, 3, 5, 7, 9, 11, 13, 15, 21, 25, 27, 31, 45):
            modulus = (1 << p)*q
            for source in range(0, modulus, 2):
                targets = {
                    0, modulus-2,
                    2*((source//2+1) % (modulus//2)),
                    2*((source//2+7) % (modulus//2)),
                }
                for target in targets:
                    start, orbit = coherent_orbit(p, q, source, target)
                    assert orbit[0] == start and orbit[-1] % modulus == target
                    assert len(orbit)-1 <= p//2+1
                    max_bits = max(max_bits, start.bit_length())
                    max_len = max(max_len, len(orbit)-1)
                    count += 1
            print(f"p={p}, q={q}: coherent orbit source/target witnesses pass")
    print(f"PASS: {count} exact single-source coherent orbits, maximum initial bits {max_bits}, maximum E returns {max_len}")


if __name__ == "__main__":
    verify()
