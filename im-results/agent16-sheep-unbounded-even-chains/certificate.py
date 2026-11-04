#!/usr/bin/env python3
"""Exact samples for the all-n Sheep first-even ancestry corridor theorem."""

def section_step(t):
    a=(t&-t).bit_length()-1
    v=t>>a
    assert a==1 and v>=5 and v%2==1
    return t+a+(v-1)//2


def verify(n):
    assert n>=1
    j=1+6*5**(n-1)
    value=(1<<j)+2
    assert value % 5**n==0
    ancestors=[]
    for m in range(n+1):
        assert value % 5**m==0
        y=4**m*(value//5**m)-2
        assert y>=10 and y%2==0
        if m>0:
            assert y%8==6
            assert section_step(y)==ancestors[-1]
        ancestors.append(y)
    assert len(set(ancestors))==n+1
    return j, ancestors[-1].bit_length(),ancestors[-1] if n<=2 else None

if __name__=='__main__':
    for n in range(1,9):
        j,bits,terminal=verify(n)
        print(f'PASS n={n} exponent={j} last-ancestor-bits={bits} '
              f'last-ancestor-small={terminal}')
