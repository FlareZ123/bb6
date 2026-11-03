"""Independent arithmetic audit of Sheep's coherent first-even-return theorem.

Rebuilds the dyadic inverse-word decoder, odd exponent lifting and a single
positive integer forward trajectory from the published equations alone.
Every forward step is genuine on the generic Sheep section branch, but the
starting integer is freely chosen, NOT the blank-origin section value 10.
"""
from random import Random


def v2(x):
    assert x > 0
    return (x & -x).bit_length()-1


def generic_step(x):
    a = v2(x)
    u = x >> a
    assert a>=1 and u>=5 and u%2==1
    z = x+a+(u-1)//2
    h = v2(z-1)
    v = (z-1)>>h
    assert v>=5 and v%2==1
    return (a,h,1+3**h*v)


def decode(p,r):
    word=[]
    while r:
        a=v2(r)
        u=r>>a
        C=(1+(1<<(a+1)))*u+2*a-3
        h=min(v2(C)-1,p-a-1)
        assert h>=0
        word.append((a,h))
        p-=a+h+1
        r=(1+3**h*(C>>(h+1)))%(1<<p) if p else 0
        assert r%2==0
    return word


def inverse(p,a,h,s):
    M=1<<(p-a)
    D=1+(1<<(a+1))
    u=((3-2*a+(1<<(h+1))*pow(3**h,-1,M)*(s-1))*pow(D,-1,M))%M
    return (1<<a)*u


def prime_powers(q):
    ans=[];n=q;d=3
    while d*d<=n:
        if n%d==0:
            k=0
            while n%d==0:
                n//=d;k+=1
            ans.append((d,k))
        d+=2
    if n>1:ans.append((n,1))
    return ans


def euler_phi(q):
    z=q
    for ell,_ in prime_powers(q):
        z=z//ell*(ell-1)
    return z


def odd_output(a,r,q):
    if q==1:return 0
    return (r+a+(r*pow(2,-a,q)-1)*pow(2,-1,q))%q


def choose_exponent(q,r,s,p):
    a=0;Q=1
    for ell,k in prime_powers(q):
        B=Q*euler_phi(Q)*(ell-1)
        assert B%ell!=0 and pow(2,B,ell)==1
        t=0
        for j in range(k):
            d=ell**j
            choices=[z for z in range(ell)
                     if odd_output(a+B*(t+d*z),r,ell**(j+1))==s%ell**(j+1)]
            assert len(choices)==1
            t+=d*choices[0]
        a+=B*t
        Q*=ell**k
        assert odd_output(a,r,Q)==s%Q
    period=q*euler_phi(q)
    a+=max(0,(p-a+period-1)//period)*period
    assert a>=p and odd_output(a,r,q)==s%q
    return a


def coherent(p,q,r,s):
    """Return a single real generic trajectory witnessing E^k(x) == s (mod 2^p*q)."""
    m=1<<p
    modulus=m*q
    word=decode(p,r%m)
    cost=sum(a+h+1 for a,h in word)
    assert cost<=p and len(word)<=p//2
    P=p+cost
    dyadic=0
    for a,h in reversed(word):
        dyadic=inverse(P,a,h,dyadic)
    assert dyadic%m==r%m
    period=(1<<P)*q
    x0=dyadic+(1<<P)*(((r-dyadic)*pow(1<<P,-1,q))%q if q>1 else 0)+100*period

    def forward(x):
        trajectory=[x]
        for a,h in word:
            actual_a,actual_h,y=generic_step(x)
            assert (a,h)==(actual_a,actual_h)
            trajectory.append(y)
            x=y
        return trajectory

    before=forward(x0)
    y0=before[-1]
    assert y0%m==0 and x0%modulus==r
    alpha=1
    for a,h in word:alpha*=3**h*(1+(1<<(a+1)))
    assert forward(x0+period)[-1]-y0==alpha*m*q
    a=choose_exponent(q,y0%q,s%q,p)
    fullprec=1<<(a+p+1)
    desired=((1<<a)*(1+2*(s-a)))%fullprec
    assert (desired-y0)%m==0
    k=((desired-y0)//m*pow(alpha*q,-1,1<<(a+1)))%(1<<(a+1))
    start=x0+period*k
    trajectory=forward(start)
    y=trajectory[-1]
    if y>>(a)<5:
        start+=period*(1<<(a+1))
        trajectory=forward(start)
        y=trajectory[-1]
    assert y%fullprec==desired and v2(y)==a and y>>a>=5
    aa,hh,target=generic_step(y)
    assert aa==a and hh==0 and target%modulus==s
    assert start%modulus==r and len(trajectory)<=p//2+1
    return start,trajectory+[target]


def verify():
    rng=Random(0xA40)
    count=0;maxbits=0;longest=0
    for p in range(1,10):
        for q in (1,3,5,7,9,11,15,21,25,27,35,45,63,75,81,99,105,143,165,255,315):
            modulus=(1<<p)*q
            for _ in range(min(100,modulus//2)):
                source=2*rng.randrange(modulus//2)
                target=2*rng.randrange(modulus//2)
                start,orbit=coherent(p,q,source,target)
                count+=1
                maxbits=max(maxbits,start.bit_length())
                longest=max(longest,len(orbit)-1)
            print('PASS',p,q,flush=True)
    print(f'PASS: {count} coherent actual generic E-orbits; max start {maxbits} bits, max {longest} returns')


if __name__=='__main__':
    verify()
