"""Discover positive returns between independent repeated-word counters.
Candidate generation is untrusted; emitted Lean verifies every macro."""
from dataclasses import dataclass
from functools import lru_cache
from itertools import groupby

ROWS = {
    299: "1RB0LA_1RC---_0RD1LE_1LD1RE_0LF0LE_1RF0RA",
    320: "1RB0LC_1RC---_0RD---_1LD1RE_0LF0LE_1RF0RA",
    323: "1RB0RB_1RC0LC_0RD---_1LD1RE_0LF0LE_1RF0RA",
    325: "1RB0RB_1RC1LD_0RD---_1LD1RE_0LF0LE_1RF0RA",
    340: "1RB1LA_1RC1LE_0RD---_1LD1RE_0LF0LE_1RF0RA",
    345: "1RB1LB_1RC---_0RD1LE_1LD1RE_0LF0LE_1RF0RA",
    347: "1RB1LD_1RC---_0RD---_1LD1RE_0LF0LE_1RF0RA",
    348: "1RB1LE_1RC0LB_0RD---_1LD1RE_0LF0LE_1RF0RA",
    353: "1RB1RB_1RC0LB_0RD---_1LD1RE_0LF0LE_1RF0RA",
    363: "1RB0LC_1RC0RA_0RD---_1LD1RE_0LF0LE_1RF0RB",
}

def parse(s):
    s=s.replace('_','')
    return tuple(s[i:i+3] for i in range(0,36,3))

@dataclass(frozen=True)
class Rep:
    block:str
    var:str

def word(*parts):
    out=[]
    for x in parts:
        if not x:continue
        if isinstance(x,str) and out and isinstance(out[-1],str):out[-1]+=x
        else:out.append(x)
    return tuple(out)
def prefix(w):return w[0] if w and isinstance(w[0],str) else ''
def firstrep(w):
    p=prefix(w);i=bool(p)
    if len(w)>i and isinstance(w[i],Rep):return p,w[i],w[i+1:]
def cons(x,w):return word(x,*w)
def head(w):
    if not w:return '0'
    if isinstance(w[0],Rep):raise ValueError('opaque')
    return w[0][0]
def tail(w):
    if not w:return w
    if isinstance(w[0],Rep):raise ValueError('opaque')
    return word(w[0][1:],*w[1:])
@dataclass(frozen=True)
class Config:
    q:int;l:tuple=();r:tuple=()
def step(p,c):
    a=p[2*c.q+int(head(c.l))]
    if a=='---':raise ValueError('hole')
    q,w=ord(a[2])-65,a[0]
    if a[1]=='R':return Config(q,cons(head(c.r),cons(w,tail(c.l))),tail(c.r))
    return Config(q,tail(c.l),cons(w,c.r))
@lru_cache(maxsize=200000)
def local(p,q,lp,rp,side,block,limit=200):
    c=Config(q,word(lp+(block if side=='L' else ''),Rep('X','X')),word(rp+(block if side=='R' else ''),Rep('Y','Y')))
    for n in range(1,limit+1):
        try:c=step(p,c)
        except ValueError:return
        if c.q!=q:continue
        a,b=prefix(c.l),prefix(c.r)
        if side=='L' and a==lp and b.startswith(rp) and len(b)==len(rp)+len(block):return n,b[len(rp):]
        if side=='R' and b==rp and a.startswith(lp) and len(a)==len(lp)+len(block):return n,a[len(lp):]

def loops(p,c):
    for side,w,other in [('L',c.l,c.r),('R',c.r,c.l)]:
        s=firstrep(w)
        if s is None:continue
        pre,rep,tail=s;op=prefix(other)
        for j in range(min(len(op),16)+1):
            m=local(p,c.q,pre if side=='L' else op[:j],op[:j] if side=='L' else pre,side,rep.block)
            if not m:continue
            k,out=m;ot=word(op[j:],*other[bool(op):]);v=word(pre,*tail);u=word(op[:j],Rep(out,rep.var),*ot)
            d=Config(c.q,v,u) if side=='L' else Config(c.q,u,v)
            yield ('loop',c,d,k,side,rep,out,pre,op[:j],tail,ot)
            break

def runlength(w):
    """Return consecutive homogeneous runs with lengths affine in independent variables."""
    runs=[]
    def add(b,cs):
        if runs and runs[-1][0]==b:
            for v,k in cs.items():runs[-1][1][v]=runs[-1][1].get(v,0)+k
        else:runs.append((b,dict(cs)))
    for x in w:
        if isinstance(x,Rep):
            if len(set(x.block))!=1:return None
            add(x.block[0],{x.var:len(x.block)})
        else:
            for b,g in groupby(x):add(b,{'':len(list(g))})
    return runs

def linear_div(cs,sub,div):
    cs=dict(cs);cs['']=cs.get('',0)-sub
    if any(v<0 or v%div for v in cs.values()):return None
    return {v:k//div for v,k in cs.items() if k}
def boundary(c,q,zbase,zstep,obase=1,ostep=1):
    if c.q!=q or c.l:return
    r=runlength(c.r)
    if r is None or [b for b,_ in r]!=['0','1']:return
    a=linear_div(r[0][1],zbase,zstep);b=linear_div(r[1][1],obase,ostep)
    if a is not None and b is not None:return a,b

def discover(p,start,target,limit=2000):
    c=start;hist=[];seen=set()
    for i in range(limit):
        if i and (ans:=target(c)) is not None:return hist,c,ans
        if c in seen:return
        seen.add(c);opt=list(loops(p,c))
        if opt:
            x=opt[0];hist.append(x);c=x[2];continue
        try:d=step(p,c)
        except ValueError:return
        hist.append(('step',c,d,1));c=d

def test(i,zbase,zstep,cut):
    p=parse(ROWS[i]);res=[]
    for b in range(1,cut+2):
        start=Config(5,(),word('0'*zbase,Rep('0'*zstep,'a'),'1'*b,Rep('1','b') if b==cut+1 else ''))
        ans=discover(p,start,lambda c:boundary(c,5,zbase,zstep))
        if not ans:return
        res.append((start,ans))
    return res
