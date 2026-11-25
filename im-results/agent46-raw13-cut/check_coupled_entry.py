"""Finite entry certificate for the raw13 E0=0RD cylinder.
Words are little-endian, closest cell first. Only the base table is executed.
Frame and jump rules are proved in Raw13CoupledCounters.md.
"""
from hashlib import sha256

TABLE = (7,14,11,5,2,19,22,0,13,13,10,24)
# code = 4*nextState + 2*writeBit + rightBit

def primitive(z):
    q,l,r=z
    c=TABLE[2*q+(l&1)]
    assert c != 24, 'unassigned transition reached'
    q,b,d=c//4,(c//2)&1,c&1
    if d: return q,(r&1)+2*b+4*(l//2),r//2
    return q,l//2,b+2*r

def raw(z,n):
    for _ in range(n): z=primitive(z)
    return z

def enc(x):
    return sum(((x>>i)&1)<<(4*i) for i in range(x.bit_length()))

def pack(w):
    return sum((1+2*b)<<(2*i) for i,b in enumerate(w))

def unpack(r):
    w=[]
    while r:
        assert r&1
        w.append((r>>1)&1);r>>=2
    return tuple(w)

def config(l,w): return 0,l,26+32*pack(w)

def scan(w):
    a=0
    while w:
        if not w[0]: return a,w[1:]
        if len(w)<3: return a+3,()
        a+=6;w=w[3:]
    return a,()

def frame(l,w):
    """Return one certified macro, or None if its prefix is not matched."""
    k=0;n=0;u=l
    while u&3==3: k+=1;u>>=2
    while u&15==1: n+=1;u>>=4
    if not u&1:
        a,v=scan((0,)*k+(1,)+w)
        return (((1<<(4*n))|(u<<4*n))<<a)|((1<<a)-1),v,'main'
    if n and u&7==3:
        a,v=scan((1,)*(2*n-1)+(0,)*(k+2)+(1,)+w)
        return (((u>>3)*2+1)<<a)|((1<<a)-1),v,'mixed11'
    if u&15==9:
        if n:
            a,v=scan((1,)*(2*n-1)+(0,)*(k+2)+(1,)+w)
            return (((u>>4)*4+3)<<a)|((1<<a)-1),v,'special'
        return (u>>4)*4+3,(0,)*k+(1,)+w,'special0'
    return None

def jump(l,w):
    if l&15>1: return None
    u=l;x=0;m=0
    while u and (u&15)<=1:
        x|=(u&1)<<m;u>>=4;m+=1
    n=len(w)//3;v=sum(w[3*i+2]<<i for i in range(n))
    d=(1<<n)-1-v
    if u: d=min(d,((1<<m)-1-x)//2)
    if d<=0: return None
    y=x+2*d;hi=(v^(v+d)).bit_length();out=list(w)
    for j in range(hi): out[3*j:3*j+3]=[0,0,((v+d)>>j)&1]
    return enc(y)|(u<<(4*m)),tuple(out),d

def guard(l,w): return l==1 and len(w)>=10 and w[:3]==(1,)*3 and w[-7:]==(0,)*6+(1,)

def certificate():
    l,w=1,()
    assert raw((0,0,0),21)==config(l,w)
    trace=[('initial',21,l,w)]
    for i in range(1000):
        if guard(l,w): break
        j=jump(l,w)
        if j:
            l,w,d=j; trace.append(('jump',d,l,w));continue
        f=frame(l,w)
        if f:
            l,w,rule=f;trace.append((rule,1,l,w));continue
        # Exact finite primitive replay for unmatched prefixes.
        z=config(l,w)
        for k in range(1,100001):
            z=primitive(z)
            if z[0]==0 and z[2]&31==26:
                l,w=z[1],unpack(z[2]>>5)
                trace.append(('primitive',k,l,w));break
        else: raise AssertionError('no frame')
    else: raise AssertionError('no guarded entry')
    assert guard(l,w)
    text='\n'.join(f'{tag} {n} {l:x} {"".join(map(str,w))}' for tag,n,l,w in trace)+'\n'
    print('transitions',len(trace)-1,'jump count',sum(tag=='jump' for tag,*_ in trace), 'jump iterations',sum(n for tag,n,*_ in trace if tag=='jump'))
    print('guard word', ''.join(map(str,w)), 'length',len(w),'sha256',sha256(text.encode()).hexdigest())
    return trace,text

if __name__=='__main__': certificate()
