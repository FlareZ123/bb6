"""Finite smoke tests for Agent43's P1 wall lemmas.

These checks are not an infinite proof or a blank-root machine decider.
The all-parameter mathematical derivation is in WallAboveNPlusZ.md.
"""


def verify_numeric_lemma() -> None:
    for n in range(256, 4096):
        z = 0
        while (1 << z) <= 4 * n:
            assert 24**z * (n + 2)**(2 * z + 2) < (1 << n), (n, z)
            z += 1

    # q(u)=2u²+15u+22, q(9)=319<512, q(u+1)=q(u)+4u+17.
    q9 = 2 * 9**2 + 15 * 9 + 22
    assert q9 == 319 and q9 < 2**9
    for u in range(9, 100):
        assert 4 * u + 17 <= 2**u
        assert 2 * u**2 + 15 * u + 22 < 2**u


def verify_source_shaped_words() -> None:
    for n in (14, 30, 62):
        K = 7 * (1 << n) - n - 3
        states = {(1, 0, 0)}
        visited = set(states)
        for _depth in range(14):
            next_states = set()
            for D, m, z in states:
                F = K + 2 - D - m
                assert F >= 6 and D >= 1
                assert (1 << m) * F <= 1 << (n + 3 + z * (2 * n + 3))
                x = K + D - m
                for l in range(1, x.bit_length()):
                    if x % (1 << l):
                        continue
                    Dp = x >> l
                    mp = m + l
                    Fp = K + 2 - Dp - mp
                    if Dp < 2 or Fp < 6:
                        continue
                    zp = z + (l >= 2)
                    assert (1 << mp) * Fp <= 1 << (n + 3 + zp * (2 * n + 3))
                    if l == 1:
                        assert 2 * Fp == F
                    else:
                        assert (1 << l) * Fp <= (1 << (2 * n + 3)) * F
                    next_states.add((Dp, mp, zp))
            states = next_states - visited
            visited |= states
        print(f"n={n}, source-shaped nodes checked={len(visited)}")


if __name__ == "__main__":
    verify_numeric_lemma()
    verify_source_shaped_words()
    print("All finite smoke tests passed; the uniform paper proof is separate.")
