"""Exact finite cross-check of Sheep E predecessor parent formulas."""

from math import prod

def F(x):
    a=(x & -x).bit_length()-1
    v=x>>a
    assert a>=1 and v>=3 and v%2==1
    return x+a+(3 if v==3 else (v-1)//2)

def E(x):
    z=F(x)
    h=((z-1)&(1-z)).bit_length()-1
    return 1+3**h*((z-1)>>h)

def predicted(j):
    result=set()
    if j%4==2:
        result.add(2*((2**(j+2)-1)//15))
    if j%18==14:
        result.add(4*((2**(j+2)-7)//27))
    if j%8==4:
        result.add(8*((2**(j+2)-13)//51))
    for x in result:
        assert E(x)==2**j
    return result

def actual(j):
    y=2**j
    result=set()
    d=y-1
    h=0
    while True:
        z=1+2**h*d
        for a in range(1,z.bit_length()+1):
            m=2**(a+1)+1
            v,r=divmod(2*z-2*a+1,m)
            if r==0 and v>=5 and v%2==1:
                x=2**a*v
                if F(x)==z and E(x)==y:
                    result.add(x)
            x=3*2**a
            if F(x)==z and E(x)==y:
                result.add(x)
        if d%3:break
        d//=3
        h+=1
    return result

for j in range(8,1001,2):
    if j%3==0:continue
    assert actual(j)==predicted(j),j
print("PASS 332 complete finite full-inverse tests through j=1000")
