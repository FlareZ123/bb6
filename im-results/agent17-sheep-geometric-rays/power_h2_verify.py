"""Exact complete h=2 low-source periods for Sheep power targets.

Python 3.10+ standard library. See POWER-PARENTS-H2.md for the all-k proof.
"""
expected={1:(12,()),2:(54,(33,)),3:(24,()),4:(90,()),5:(12,()),6:(126,())}

def order(m):
    x=1
    for n in range(1,2*m+1):
        x=(2*x)%m
        if x==1:
            return n
    raise AssertionError(m)

for a,(period,hits) in expected.items():
    m=9*(2**(a+1)+1)
    k=18*a-19
    o=order(m)
    actual=tuple(n for n in range(o) if pow(2,n,m)==k%m)
    assert o==period and actual==hits,(a,o,actual)
    assert pow(2,o,m)==1
    print('PASS valuation',a,'modulus',m,'period',o,'solutions',actual)
print('PASS every h=2 low-source modular exponent; unbounded j via full periods')
