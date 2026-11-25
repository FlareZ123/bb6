from dataclasses import dataclass
from collections import defaultdict
def step(t,z):
    q,l,r=z
    w,d,p=t[3*(2*q+int(l[0] if l else '0')):][:3]
    if w=='-':return None
    return (ord(p)-65,(r[0] if r else '0')+w+l[1:],r[1:]) if d=='R' else (ord(p)-65,l[1:],w+r)
import time

@dataclass(frozen=True)
class Word:
    # pre + block^n + post. A literal is a word with no repeat.
    pre:str
    block:str=''
    post:'Word|str|None'=None
    def __post_init__(self):
        if self.block and not isinstance(self.post,Word):object.__setattr__(self,'post',Word(self.post or ''))
        if not self.block and self.post is not None:raise ValueError(self)
    def concrete(self,n): return self.pre+self.block*n+(self.post.concrete(n) if self.block else '')
    def tail(self):
        if not self.pre: raise ValueError('unknown or blank')
        return Word(self.pre[1:],self.block,self.post)
    def prepend(self,x):return Word(x+self.pre,self.block,self.post)
    def head(self):
        if self.pre:return self.pre[0]
        if not self.block:return '0'
        raise ValueError('unknown')
    def drop(self):return self.tail() if self.pre else self if not self.block else (_ for _ in ()).throw(ValueError('unknown'))
    def norm(self):
        p,b,s=self.pre,self.block,self.post
        if not b:return self
        while p and p[-1]==b[-1]:
            c=p[-1]; p=p[:-1]; b=c+b[:-1]; s=s.prepend(c)
        return Word(p,b,s.norm())
    def grow(self,d):return Word(self.pre+self.block*d,self.block,self.post.grow(d)) if self.block else self
    def size(self):return len(self.pre)+(self.post.size() if self.block else 0)

@dataclass(frozen=True)
class C:
    q:int
    l:Word
    r:Word
    def concrete(self,n): return self.q,self.l.concrete(n),self.r.concrete(n)
    def norm(self):return C(self.q,self.l.norm(),self.r.norm())

def symstep(t,z):
    q,l,r=z.q,z.l,z.r
    a=l.head(); w,d,p=t[3*(2*q+int(a)):][:3]
    if w=='-': raise ValueError('hole')
    q=ord(p)-65
    if d=='R': return C(q,l.drop().prepend(r.head()+w),r.drop())
    return C(q,l.drop(),r.prepend(w))

def localstep(t,z):
    # Both unknown tails. None if any transition reads unknown tail.
    q,l,r=z
    if not l: return None
    w,d,p=t[3*(2*q+int(l[0])):][:3]
    if w=='-': return None
    q=ord(p)-65
    if d=='R':
        if not r:return None
        return q,r[0]+w+l[1:],r[1:]
    return q,l[1:],w+r

def sweeps(t,z,maxsteps=100):
    # One whole repeated segment transfers, with arbitrary symbolic tails.
    for d in ['R','L']:
        a,b=(z.l,z.r) if d=='R' else (z.r,z.l)
        if not b.block: continue
        rp=b.pre; I=b.block
        for f in range(len(a.pre)+1):
            lp=a.pre[:f]; L=Word(a.pre[f:],a.block,a.post); R=b.post
            s=(z.q,lp,rp+I) if d=='R' else (z.q,rp+I,lp)
            for k in range(1,maxsteps+1):
                s=localstep(t,s)
                if s is None: break
                q,x,y=s
                x,y=(x,y) if d=='R' else (y,x)
                if q==z.q and y==rp and x.startswith(lp) and len(x)==len(lp)+len(I):
                    O=x[len(lp):]
                    aa=Word(lp,O,L);bb=R.prepend(rp)
                    new=C(q,aa,bb) if d=='R' else C(q,bb,aa)
                    yield new,(d,lp,rp,I,O,k,L,R)
                    break

def inserts(x,y,multi=False):
    d=len(y)-len(x)
    if d==0:
        if x==y:yield Word(x)
        return
    if d<0 or d>120:return
    for i in range(len(x)+1):
        if y[:i]==x[:i] and y[i+d:]==x[i:]:
            yield Word(x[:i],y[i:i+d],x[i:])
    if not multi or d<2 or d>30 or len(x)>60:return
    for i in range(len(x)+1):
        if y[:i]!=x[:i]:break
        for j in range(i+1,len(x)+1):
            if y[j+d:]!=x[j:]:continue
            for d1 in range(1,d):
                if y[i+d1:j+d1]==x[i:j]:
                    yield Word(x[:i],y[i:i+d1],Word(x[i:j],y[j+d1:j+d],x[j:]))

def family(z1,z2,multi=False):
    if z1[0]!=z2[0] or len(z1[1])+len(z1[2])>=len(z2[1])+len(z2[2]):return
    for l in inserts(z1[1],z2[1],multi):
        for r in inserts(z1[2],z2[2],multi):yield C(z1[0],l,r)

def target(f,d):return C(f.q,f.l.grow(d),f.r.grow(d))

def symbolic(t,f,maxsteps=1500,maxsweeps=12,maxinc=8,deadline=float("inf")):
    # Branching search: finite step or apply a complete unknown repeat sweep.
    # Prioritize accelerated states, and check exact normalization only.
    targets={target(f,d).norm():d for d in range(1,maxinc+1)}
    seen=set()
    def dfs(z,path,cost,sweepcount):
        if z.norm() in targets and path:return targets[z.norm()],path,cost
        if time.monotonic()>deadline:return None
        if len(path)>=maxsteps or sweepcount>maxsweeps or z in seen:return None
        seen.add(z)
        for y,info in sweeps(t,z):
            if y==z: continue
            r=dfs(y,path+[(z,y,info)],(cost[0]+info[5],cost[1]),sweepcount+1)
            if r:return r
        try:y=symstep(t,z)
        except ValueError:return None
        if y.l.size()+y.r.size()>1000:return None
        return dfs(y,path+[(z,y,None)],(cost[0],cost[1]+1),sweepcount)
    return dfs(f,[],(0,0),0)

def infer(t,limit=15000,budget=1):
    # First prefer one growing block; then allow correlated multi-block growth.
    deadline=time.monotonic()+budget
    z=(0,'','');hist=defaultdict(list);tried=set()
    for n in range(limit+1):
        if time.monotonic()>deadline:return None
        q,l,r=z
        if min(len(l),len(r))<=16 and max(len(l),len(r))<600:
            key=(q, min(len(l),len(r)) if min(len(l),len(r))<=3 else -1)
            a=hist[key]
            for j,old in reversed(a[-30:]):
                if len(l)+len(r)<=len(old[1])+len(old[2]):continue
                for f in family(old,z,True):
                    if time.monotonic()>deadline:return None
                    if f.norm() in tried:continue
                    tried.add(f.norm())
                    try:res=symbolic(t,f,maxsteps=250,deadline=deadline)
                    except RecursionError:res=None
                    if res:return j,f,res,n
            a.append((n,z))
        z=step(t,z)
        if z is None:return ('hole',n)
    return None

if __name__=='__main__':
    import sys,time
    for line in sys.stdin:
        t=line.split()[0];start=time.monotonic();r=infer(t)
        if r and r[0]!='hole':
            j,f,(d,path,cost),n=r
            print(t,'FOUND',j,f,d,cost,len(path),n,'seconds',round(time.monotonic()-start,3),flush=True)
        else:print(t,'FAIL',r,'seconds',round(time.monotonic()-start,3),flush=True)
