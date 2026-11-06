"""Exact source-semantic modular certificates for Sheep first-even fan-in.

Power target exponent j=2*3**k. All tests use modular exponentiation
and never construct 2**j for large k.
"""
from hashlib import sha256


def qmod(j: int, h: int, m: int) -> int:
    factor = 3**h
    residue = (pow(2, j, m*factor) - 1) % (m*factor)
    assert residue % factor == 0
    return residue // factor


def predicted_h(k: int, a: int) -> set[int]:
    H = k + 1
    if a == 1:
        return set(range(1, H+1, 2))
    if a == 3:
        return {h for h in range(1, H+1) if h % 16 == (10 if k % 2 == 0 else 14)}
    if a == 6:
        return {h for h in range(1, k) if k % 6 == 0 and h % 21 == 20}
    if a == 7:
        return {h for h in range(1, H+1) if h % 256 == (221 if k % 2 == 0 else 83)}
    raise ValueError(a)


def assert_mod_parent(k: int, a: int, h: int) -> None:
    j = 2 * 3**k
    M = 2**(a+1)+1
    K = 2*a-3
    q = qmod(j,h,M)
    assert (pow(2,h+1,M)*q-K) % M == 0, (k,a,h,q)
    assert (pow(2,j,3**(h+1))-1) % 3**h == 0
    assert qmod(j,h,2) == 1
    if a == 6:
        assert k % 6 == 0 and h <= k-1
        assert q % 3 == 0
    assert h <= k+1


def full_source(k: int, a: int, h: int) -> bytes:
    j = 2 * 3**k
    target = 1 << j
    q, r = divmod(target - 1,3**h)
    assert r == 0 and q>=7 and q%2==1
    M=2**(a+1)+1
    K=2*a-3
    v,rem=divmod((1 << (h+1))*q-K,M)
    assert rem==0 and v>=5 and v%2==1
    x=(1 << a)*v
    F=x+a+(v-1)//2
    z=F-1
    r2=(z & -z).bit_length()-1
    assert r2==h
    E=1+3**h*(z >> h)
    assert E==target
    return sha256(x.to_bytes((x.bit_length()+7)//8,'big')).digest()


def main() -> None:
    hsh = sha256()
    counts={a:0 for a in (1,3,6,7)}
    tested=0
    full=0
    examples={}
    for k in range(1,257):
        for a in (3,6,7):
            hs=predicted_h(k,a)
            counts[a]+=len(hs)
            for h in hs:
                assert_mod_parent(k,a,h)
                tested+=1
                if a==3 and k<=13:
                    hsh.update(full_source(k,a,h))
                    full+=1
            if k in (13,24,100,101,300,301,512) and hs:
                examples[(k,a)]=(len(hs),min(hs),max(hs))
        if k%6==0:
            assert len(predicted_h(k,6))==k//21
    print('PASS: all k=1..256, constructive a=3,6,7 source families')
    print('PASS: exact modular source certificates',tested,'by valuation',counts)
    print('PASS: a=3 literal full F/E parents',full)
    print('Examples (k,a): count, earliest h, latest h:',examples)
    print('Full-source digest',hsh.hexdigest())


if __name__ == '__main__':
    main()
