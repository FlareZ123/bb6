"""Discover a finite graph of positive macro returns among periodic tape families."""
from independent import *
from dataclasses import dataclass
from pathlib import Path

TARGETS={int(i):s for i,s in (line.split() for line in Path(__file__).with_name('phase_candidates.tsv').read_text().splitlines())}
ROWS.update(TARGETS)
MINBLOCK=5
MINREP=4

def cstep(p,q,l,r):
    a=p[q*2+int(l[0] if l else '0')]
    if a=='---':raise ValueError('hole')
    q,w=ord(a[2])-65,a[0]
    if a[1]=='R':return q,(r[0] if r else '0')+w+l[1:],r[1:]
    return q,l[1:],w+r

@dataclass(frozen=True)
class Fam:
    q:int;side:str;pre:str;block:str;suf:str;base:int
    def at(self,n):
        w=self.pre+self.block*(self.base+n)+self.suf
        return self.q,w if self.side=='L' else '',w if self.side=='R' else ''
    def symbolic(self,c=0):
        w=word(self.pre+self.block*(self.base+c),Rep(self.block,'n'),self.suf)
        return Config(self.q,w if self.side=='L' else (),w if self.side=='R' else ())
    def match(self,q,l,r):
        if q!=self.q or (r if self.side=='L' else l):return
        w=l if self.side=='L' else r
        d=len(w)-len(self.pre)-len(self.suf)
        if d<0 or d%len(self.block):return
        n=d//len(self.block)-self.base
        if n>=0 and self.at(n)==(q,l,r):return n

def canon(pre,block,suf):
    rotations=[]
    while pre and pre[-1]==block[-1]:
        b=pre[-1];rotations.append((pre,block,suf));pre,block,suf=pre[:-1],b+block[:-1],b+suf
    count=0
    while suf.startswith(block):count+=1;suf=suf[len(block):]
    return pre,block,suf,count,rotations

def abstract(q,side,pre,block,suf,keep):
    a,b,c,k,_=canon(pre,block,suf);base=min(k,keep)
    return Fam(q,side,a,b,c,base),k-base

def concrete_family(q,l,r,keep,maxblock=12,minrep=None):
    if minrep is None:minrep=MINREP
    if bool(l)==bool(r):return
    side='L' if l else 'R';w=l or r
    best=None
    for i in range(len(w)):
        for k in range(MINBLOCK,min(maxblock,(len(w)-i)//minrep)+1):
            p=w[i:i+k];j=i+k
            while w.startswith(p,j):j+=k
            n=(j-i)//k
            if n<minrep:continue
            rank=(j-i,-k,-i)
            if best is None or rank>best[0]:best=(rank,i,j,p,n)
    if best:
        _,i,j,p,n=best
        f,x=abstract(q,side,w[:i],p,p*n+w[j:],keep)
        assert f.at(x)==(q,l,r)
        return f,x

def symbolic_family(c,keep):
    if bool(c.l)==bool(c.r):return
    side='L' if c.l else 'R';w=c.l or c.r
    rep=[x for x in w if isinstance(x,Rep)]
    if len(rep)!=1:return
    x=rep[0];i=w.index(x);pre=''.join(w[:i]);suf=''.join(w[i+1:]);f,k=abstract(c.q,side,pre,x.block,suf,keep)
    return f,k

def find_generic(p,f,keep,maxcut=5,limit=1500,require_sweep=True):
    for cut in range(maxcut+1):
        st=f.symbolic(cut);c=st;hist=[];seen=set();positive=False;swept=False
        for it in range(limit):
            if positive and (swept or not require_sweep) and (x:=symbolic_family(c,keep)) is not None:
                g,k=x
                return cut,st,hist,c,g,k
            if c in seen:break
            seen.add(c);opts=list(loops(p,c))
            if opts:
                x=opts[0];hist.append(x);c=x[2];swept=True;continue
            try:d=step(p,c)
            except ValueError:break
            hist.append(('step',c,d,1));c=d;positive=True
    return None

def find_concrete(p,c,fams,keep,limit=20000):
    q,l,r=c
    for t in range(1,limit+1):
        try:q,l,r=cstep(p,q,l,r)
        except ValueError:return None
        if bool(l)==bool(r):continue
        for f in fams:
            n=f.match(q,l,r)
            if n is not None:return t,f,n
        a=concrete_family(q,l,r,keep)
        if a is not None:return t,*a
    return None

def closure(i,keep=1,maxfam=150,require_sweep=True):
    p=parse(ROWS[i]);first=find_concrete(p,(0,'',''),[],keep)
    if not first:return None,'entry'
    t,f,n=first;fs=[f];arcs=[]
    def add(g,k):
        for h in fs:
            if (g.q,g.side,g.pre,g.block,g.suf)==(h.q,h.side,h.pre,h.block,h.suf) and h.base<=g.base:return fs.index(h),k+g.base-h.base
        fs.append(g);return len(fs)-1,k
    for j,f in enumerate(fs):
        if len(fs)>maxfam:return None,f'cap {len(fs)}'
        ret=find_generic(p,f,keep,require_sweep=require_sweep)
        if ret is None:return None,f'generic {j} {f}'
        cut,st,hist,last,g,k=ret;idx,off=add(g,k);branches=[]
        for a in range(cut):
            re=find_concrete(p,f.at(a),fs,keep)
            if re is None:return None,f'finite {j} {f} {a}'
            steps,h,m=re;ind,m=add(h,m);branches.append((a,steps,ind,m))
        arcs.append((cut,st,hist,last,idx,off,branches))
    return (t,n,fs,arcs),'ok'
