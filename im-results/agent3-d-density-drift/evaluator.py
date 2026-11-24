"""Literal source-table suffix evaluator using framed first-left exits."""
from functools import lru_cache
RULES=((1,1,1),(0,1,4),(1,-1,2),(0,1,0),(1,-1,0),(1,-1,3),(1,-1,2),(1,-1,5),(0,-1,2),(0,-1,1),(1,-1,4),None)

def split(w):return (int(w[0]),w[1:]) if w else (0,'')
def canon(w):
    w=w.rstrip('0');q=len(w)-len(w.lstrip('1'));return q,w[q:]

@lru_cache(maxsize=250000)
def first_exit(q,w):
    left=[]
    while True:
        b,z=split(w);ins=RULES[2*q+b]
        if ins is None:return None
        b,d,q=ins;b=str(b)
        if d==1:left.append(b);w=z
        else:
            y=b+z
            if not left:return q,y.rstrip('0')
            w=left.pop()+y

@lru_cache(maxsize=250000)
def e_step(w):
    q=4;guard='00101010'
    for p in range(len(guard)+1):
        if p>=2 and p%2==0 and q in (1,3) and not w.startswith('1'):
            l,s=canon(w[1:]);return 11-p+l,s
        if q==5 and w.startswith('1'):return None
        if p==len(guard):raise AssertionError((w,q))
        a=first_exit(q,w)
        if a is None:return None
        q,y=a;w=(guard[p]+y).rstrip('0')

@lru_cache(maxsize=500000)
def step(w,r):
    assert w=='' or (w[0]=='0' and w[-1]=='1')
    if r==2:
        l,s=canon(w[1:]);return 9+l,s
    if r==1:return e_step(w)
    v=w[1:];c=0
    while v.startswith('1'):
        z=v+'000'
        if z.startswith('10'):v=v[2:];c+=2
        elif z.startswith('111'):v=v[3:];c+=8
        else:
            ans=e_step(('0'+v[3:]).rstrip('0'))
            return None if ans is None else (ans[0]+c+2,ans[1])
    l,s=canon(v[1:]);return 11+c+l,s

