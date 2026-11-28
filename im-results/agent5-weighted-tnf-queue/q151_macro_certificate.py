"""Candidate finite q0-151 macro closure; exact source soundness still to prove."""
from collections import deque
from functools import lru_cache
D={(0,1):0,(0,0):1,(1,0):1,(1,1):1,(1,2):0}
ALL,END=3,4
TYPES=(2,3)
SUFFIX=(2,3,4)
CATS=(1,2,4,5,6,8)
EMPTY=((),(0,1),0)
def plus(a,b):
    if a==0:return b
    if b==0:return a
    return a+b if a+b<=4 else 5+(a+b-1)%4
@lru_cache(None)
def pre(r,t):
    if t==END:t=ALL
    return sum(1<<g for g in range(2) if (g,r%4) in D and (t>>D[g,r%4])&1)
@lru_cache(None)
def typ(r):
    p,t=r
    if t==END:t=ALL
    for c in p[::-1]:t=pre(c,t)
    return t
@lru_cache(None)
def front(t):
    if t==END:return ((None,END),)
    return tuple((c,v) for c in CATS for v in SUFFIX if pre(c,v)==t)
@lru_cache(None)
def cut(r):
    p,t=r
    if not p:
        assert t==END
        return ((None,r),)
    if t==END:return ((p[0],((),t)),)
    return tuple((p[0],((c,) if c else (),v)) for c,v in front(t))
@lru_cache(None)
def closed(s):
    p,f,c=s
    assert c
    return ((c,),f,0) if not p else (p,tuple(D.get((g,c%4),-1) for g in f),0)
@lru_cache(None)
def app(s,w):
    for ch in w:
        s=(s[0],s[1],plus(s[2],1)) if ch=='1' else closed(s)
    return s
@lru_cache(None)
def shorten(s):
    assert s[2]==3,s
    return (s[0],s[1],2)
@lru_cache(None)
def concat(s,r):
    p,f,c=s;rp,t=r
    if c and rp:rp=(plus(c,rp[0]),)+rp[1:]
    elif c:rp=(c,)
    if not p:
        assert f==(0,1)
        for v in rp[1:][::-1]:t=pre(v,t)
        return rp[:1],t
    for v in rp[::-1]:t=pre(v,t)
    return p,sum(1<<g for g,h in enumerate(f) if h>=0 and ((ALL if t==END else t)>>h)&1)
def prepend(w,r):return concat(app(EMPTY,w),r)
def choicesA(c):return (c//4,) if c<=4 else tuple(range(2 if c==8 else 1,4))
@lru_cache(None)
def transitions(st):
    q,r,s=st;out=[]
    for c,v in cut(r):
        if c is None:out.append(('pop',concat(s if q=='B' else shorten(s),v),None))
        elif c%4==1:
            for a in choicesA(c):
                if q=='B' and a:out.append(('push',('B',v,app(EMPTY,'10'*(2*a-1)+'11')),s))
                else:out.append(('stay',('B',v,app(s,'01' if q=='B' else '10'*(2*a)+'11')),None))
        elif c%4==0:
            for a in choicesA(c):
                if q=='B':out.append(('push',('C',v,app(EMPTY,'10'*(2*a-2)+'111')),s))
                else:out.append(('stay',('C',v,app(s,'10'*(2*a-1)+'111')),None))
        elif c%4==2:
            for a in choicesA(c):
                if a or q=='C':
                    if q=='B':out.append(('stay',('B',prepend('10'*(2*a-1)+'1',v),app(s,'1111')),None))
                    else:out.append(('pop',concat(app(s,'10'*(2*a)+'1'),v),None))
                else:
                    for w,z in cut(v):
                        if w is None:out.append(('pop',concat(app(s,'1111'),z),None))
                        elif w%4==1:
                            for j in choicesA(w):
                                p='111' if j==0 else '1110'+'10'*(2*j-1)+'1'
                                out.append(('pop',concat(app(s,p),z),None))
                        elif w%4==0:
                            for j in choicesA(w):out.append(('stay',('B',z,app(s,'1110'+'10'*(2*j-1)+'11')),None))
                        else:out.append(('bad',None,None))
        else:out.append(('bad',None,None))
    return tuple(out)
def certificate():
    seed=('B',((),END),app(EMPTY,'1'))
    seen={seed};stored={EMPTY};todo=deque([seed]);pops=set()
    def insert(x):
        if x not in seen:seen.add(x);todo.append(x)
    while todo:
        st=todo.popleft()
        assert typ(st[1]) in TYPES
        for op,ns,sym in transitions(st):
            assert op!='bad',(st,op)
            if op=='push':
                if sym not in stored:
                    stored.add(sym)
                    for t in pops:insert(('B',t,app(sym,'1111')))
                insert(ns)
            elif op=='stay':insert(ns)
            else:
                assert typ(ns) in TYPES,(st,ns)
                if ns not in pops:
                    pops.add(ns)
                    for sym in stored:insert(('B',ns,app(sym,'1111')))
    print('control states',len(seen),'saved segment summaries',len(stored),'pop result summaries',len(pops))
    return seen,stored,pops
if __name__=='__main__':certificate()
