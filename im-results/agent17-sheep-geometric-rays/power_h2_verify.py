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

def section(x):
    a=(x&-x).bit_length()-1
    v=x>>a
    assert a>=1 and v>=3 and v%2
    return x+a+(3 if v==3 else (v-1)//2)

def successor(x):
    z=section(x)
    w=z-1
    h=(w&-w).bit_length()-1
    return 1+3**h*(w>>h)

def literal_parents(y):
    out={}
    d=y-1
    h=0
    while True:
        z=1+(1<<h)*d
        for a in range(1,z.bit_length()+1):
            m=(1<<(a+1))+1
            v,r=divmod(2*z-2*a+1,m)
            if r==0 and v>=5 and v%2:
                x=(1<<a)*v
                if x<z and section(x)==z and successor(x)==y:
                    out[(h,a)]=x
            x=3*(1<<a)
            if x<z and section(x)==z and successor(x)==y:
                out[(h,a)]=x
        if d%3: break
        d//=3
        h+=1
    return out

count=0
for j in range(6,1001,6):
    if j%18==0: continue
    parents={}
    if j%4==2:
        parents[(1,1)]=2*((2**(j+2)-1)//15)
    if j%8==4:
        parents[(1,3)]=8*((2**(j+2)-13)//51)
    if j%54==30:
        parents[(2,2)]=4*((2**(j+3)-17)//81)
    assert literal_parents(2**j)==parents,j
    count+=1
assert count==111
print('PASS',count,'independent exhaustive literal E inverse checks through exponent 1000')
