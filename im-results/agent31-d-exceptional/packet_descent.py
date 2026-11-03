"""Source-derived packet family M(a,q,p)=I_a((01)^q 0 1^p 0 1^6).

For p>=3 B and E preserve M with q+p decreasing exactly one. A returns
to the canonical regular L family. Checks use independent literal raw steps.
"""
from __future__ import annotations
from collections import Counter
from check_second_escape import physical_return, one, pairs


def word(q: int, p: int) -> list[int]:
    return pairs(q) + [0] + one(p) + [0] + one(6)


def triple_cost(m: int, r: int) -> int:
    return r * (6*m+41) + 12*r*(r-1)


def predict(a: int, q: int, p: int) -> tuple[int, list[int], str]:
    assert a >= 2 and q >= 0 and p >= 3
    residue = a % 3
    if residue == 2:
        k = (a-2)//3
        T = 12*k*k+49*k+40
        if q == 0:
            return T, one(8*k+9+p)+[0]+one(6), 'B_exit'
        return T, one(8*k+10)+word(q-1,p), 'B_descent'
    if residue == 1:
        k = (a-4)//3
        T = 12*k*k+49*k+58+6*q
        return T, one(8*k+9)+word(q+2,p-3), 'E_descent'
    k = (a-3)//3
    m = 4*k+3
    base = 12*k*k+41*k+32
    r,s = divmod(p,3)
    d = q+4*r
    T0 = base+2*q+triple_cost(m+q,r)
    if s == 0:
        return T0+2*(m+d)+6, one(8*k+17+2*d), 'A_exit_0'
    if s == 1:
        extra = 2+6*(m+d+1)+41+6*(m+d+5)+41+2*(m+d+9)+6
        return T0+extra, one(8*k+11+2*(d+9)), 'A_exit_1'
    return T0+2*(m+d)+24,one(8*k+11+2*d)+pairs(3)+one(2), 'A_exit_2'


def main() -> None:
    count = 0
    tags = Counter()
    for a in range(2,32):
        for q in range(6):
            for p in range(3,14):
                T, expected, tag = predict(a,q,p)
                elapsed,raw = physical_return(one(a)+word(q,p), max_steps=120000)
                assert (elapsed,raw) == (T,expected), (a,q,p,tag,elapsed,T)
                tags[tag] += 1
                count += 1
    print(f'PASS {count} exact first raw physical F0 returns for a=2..31, q=0..5, p=3..13')
    print(dict(tags))


if __name__ == '__main__':
    main()
