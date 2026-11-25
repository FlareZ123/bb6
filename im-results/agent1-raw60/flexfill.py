"""Opaque-tail symbolic discovery for generalized unary recursive fills.

The induction hypothesis is an arbitrary-tail transfer of a block s*n+r.
Discovery treats L/R and the outgoing bit as opaque markers. All symbolic
steps, sweeps, induction instances and final growth claims are checked by Lean.
"""
from recursive_fill import C, norm, prepend, subrun, parse, word, sweep

L=((2,0,1),)
R=((3,0,1),)
B=((4,0,1),)

def pop(w,head=False):
    if not w:return 0,()
    x,a,b=w[0]
    if b==0 or x in (2,3) or (head and x==4):raise ValueError
    return x,norm(((x,a,b-1),*w[1:]))

def step(p,c):
    x,lt=pop(c.l,True);m=p[2*c.q+x]
    if m=='---':raise ValueError
    y=int(m[0]);q=ord(m[2])-65
    if m[1]=='L':return C(q,lt,prepend(c.r,(y,0,1)))
    b,rt=pop(c.r)
    return C(q,prepend(lt,(b,0,1),(y,0,1)),rt)

def try_macro(p,c,q0,s,r,lp=((0,0,1),),oq=0):
    if c.q==q0 and c.l[:len(lp)]==lp and c.r and c.r[0][0]==1:
        x,a,b=c.r[0]
        if a==s and b>=r:
            tail=subrun(c.r,a,r)
            if tail and tail[0][2]>0 and tail[0][0] in (0,1,4):
                bit,rt=pop(tail);lt=c.l[len(lp):]
                d=C(oq,prepend(lt,(bit,0,1),(1,a,r),*lp),rt)
                return 'ih',d,(bit,lt,rt)
    if c.l and (a:=c.l[0][1]):
        x,_,b=c.l[0];y=sweep(p,c.q,x,a,'L')
        if y is not None:
            lt=subrun(c.l,a,0);d=C(c.q,lt,prepend(c.r,(y,a,0)))
            return 'left',d,(a,x,y,lt,c.r)
    if c.r and (a:=c.r[0][1]):
        x,_,b=c.r[0]
        try:bit,lt=pop(c.l)
        except ValueError:bit=-1
        if bit==x:
            y=sweep(p,c.q,x,a,'R')
            if y is not None:
                rt=subrun(c.r,a,0);d=C(c.q,prepend(lt,(bit,0,1),(y,a,0)),rt)
                return 'right',d,(a,bit,x,y,lt,rt)
    return None

def strip_prefix(w,lp):
    try:
        for x,_,b in lp:
            for _ in range(b):
                y,w=pop(w,True)
                if x!=y:return None
        return w
    except ValueError:return None

def grow_macro(p,c,q0,s,r,lp,oq):
    lt=strip_prefix(c.l,lp)
    if c.q==q0 and lt is not None and c.r and c.r[0][0]==1:
        x,a,b=c.r[0]
        if a and a%s==0 and b>=r:
            j=(b-r)//s;k=a//s;tail=subrun(c.r,a,s*j+r)
            if tail and tail[0][2]>0 and tail[0][0] in (0,1,4):
                bit,rt=pop(tail)
                d=C(oq,prepend(lt,(bit,0,1),(1,a,s*j+r),*lp),rt)
                return 'fill',d,(k,j,bit,lt,rt)
    return try_macro(p,c,-1,s,r,lp,oq)

def path(p,st,tg,q0,s,r,lp,oq,limit=1000,*,growth=False):
    c=st;hist=[];seen=set()
    macro=grow_macro if growth else try_macro
    for _ in range(limit):
        if c==tg:return hist
        if c in seen:return None
        seen.add(c);m=macro(p,c,q0,s,r,lp,oq)
        if m:typ,d,info=m
        else:
            try:d=step(p,c)
            except ValueError:return None
            typ,info='step',()
        hist.append((typ,c,d,info));c=d
    return None

def grow_path(p,st,tg,q0,s,r,lp,oq,limit=200):
    return path(p,st,tg,q0,s,r,lp,oq,limit,growth=True)

def base(p,q,r,lp=((0,0,1),),oq=0,b=4):
    src=C(q,(*lp,*L),norm(((1,0,r),(b,0,1),*R)))
    tg=C(oq,norm(((b,0,1),(1,0,r),*lp,*L)),R)
    c=src
    for n in range(10000):
        if c==tg:return n
        try:c=step(p,c)
        except ValueError:return None
    return None

def discover(p,q0=5,lp=((0,0,1),),oq=0):
    for s in range(1,13):
        for r in range(16):
            b=base(p,q0,r,lp,oq)
            if b is None:continue
            src=C(q0,(*lp,*L),norm(((1,s,r+s),*B,*R)))
            tg=C(oq,norm((*B,(1,s,r+s),*lp,*L)),R)
            hist=path(p,src,tg,q0,s,r,lp,oq)
            if hist is not None and any(x[0]=='ih' for x in hist):
                return s,r,b,hist
    return None

def growth(p,s,r,lp,q0=5,oq=0):
    import generate_sweeps as one
    ev=one.concrete_events(p,50000)
    for t,side,c in ev[:150]:
        for sd,w in [('L',word(c.l.pre)),('R',word(c.r.pre))]:
            for i,(x,a,b) in enumerate(w):
                if b<1:continue
                for k in [s,2*s,3*s,1,2,3,4,5,6,8,10]:
                    W=w[:i]+((x,k,b),)+w[i+1:]
                    V=w[:i]+((x,k,b+k),)+w[i+1:]
                    st=C(c.q,W if sd=='L' else word(c.l.pre),word(c.r.pre) if sd=='L' else W)
                    tg=C(c.q,V if sd=='L' else word(c.l.pre),word(c.r.pre) if sd=='L' else V)
                    hist=grow_path(p,st,tg,q0,s,r,lp,oq,200)
                    if hist and any(x[0]=='fill' for x in hist):
                        return t,st,tg,hist
    return None
