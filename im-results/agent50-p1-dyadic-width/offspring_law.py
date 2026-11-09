"""Exact finite-residue checks of the P1 shadow offspring distributions.

For each parity, every valuation cylinder of level < K has exact 2-adic
measure 2^(-v-1). The test enumerates a full dyadic period, not samples.
"""
from collections import Counter
from fractions import Fraction


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def root_count_from_valuation(v: int) -> int:
    return v // 2 + (2 if v % 2 == 0 else 1)


def generic_count_from_valuation(v: int, p: int) -> int:
    if p == 0:
        return v // 2 + (1 if v % 2 == 0 else 0)
    return v // 2 + (2 if v % 2 else 0)


def actual_count(z: int, p: int) -> int:
    return sum(1 for t in range(v2(z) + 1)
               if (p + t + z // (1 << t)) % 2 == 1)


def direct_checks(K: int = 13) -> None:
    for side, coeff, add in ((8, 3, 1), (9, 5, 2)):
        per_v = Counter()
        per_count = Counter()
        for q in range(1 << K):
            u = coeff * q + add
            v = v2(u)
            z = (12 if side == 8 else 10) * q + 4
            roots = actual_count(z, side % 2)
            assert roots == root_count_from_valuation(v), (side,q,v,roots)
            per_v[v] += 1
            per_count[roots] += 1
        for v in range(K):
            assert per_v[v] == (1 << (K-v-1)), (side,v,per_v[v])
        assert sum(per_v[v] for v in range(K, K+100)) == 1
        print('root', side, 'max_v', max(per_v),
              'first offspring', dict(sorted(per_count.items())[:5]))

    for p in (0,1):
        per_v=Counter()
        for q in range(1<<K):
            z=q+1
            v=v2(z)
            assert actual_count(z,p)==generic_count_from_valuation(v,p)
            per_v[v]+=1
        for v in range(K):
            assert per_v[v] == 1 << (K-v-1)
        assert per_v[K] == 1
        print('odd slope', p, 'first valuations',
              {v:per_v[v] for v in range(5)})


def law_moments() -> None:
    n=200
    for name, count, e_mean, e_square in (
        ('root', root_count_from_valuation, Fraction(2), Fraction(14,3)),
        ('generic-even', lambda v: generic_count_from_valuation(v,0),
         Fraction(1), Fraction(5,3)),
        ('generic-odd', lambda v: generic_count_from_valuation(v,1),
         Fraction(1), Fraction(7,3)),
    ):
        # Exact geometric tail is < 2^-200 after a bounded quadratic factor.
        approx_mean=sum((Fraction(count(v),1<<(v+1)) for v in range(n)),
                        Fraction())
        approx_square=sum((Fraction(count(v)**2,1<<(v+1)) for v in range(n)),
                          Fraction())
        assert 0 <= e_mean-approx_mean < Fraction(1,1<<180)
        assert 0 <= e_square-approx_square < Fraction(1,1<<180)
        print(name,'mean',e_mean,'second-moment',e_square,
              'variance',e_square-e_mean*e_mean)


if __name__ == '__main__':
    direct_checks()
    law_moments()
