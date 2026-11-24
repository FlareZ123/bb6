"""Independent W7-2 exact affine block execution; Python 3, stdlib only."""
from collections import defaultdict, Counter
from functools import lru_cache
import time
TM="1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD".split("_")

# Affine counts: (constant, coefficient(s)); tests hold on all N^d.
def add(x,y):
    if len(x)!=len(y): raise ValueError("dimension mismatch")
    return tuple(a+b for a,b in zip(x,y))
def sub(x,y):
    if len(x)!=len(y): raise ValueError("dimension mismatch")
    return tuple(a-b for a,b in zip(x,y))
def mul(x,n): return tuple(a*n for a in x)
def nonneg(x): return min(x)>=0
def pos(x): return x[0]>0 and min(x)>=0
def con(n,d): return (n,)+(0,)*d
def floor_div(x,n):
    if any(a%n for a in x[1:]): raise ValueError("nonaffine quotient")
    return (x[0]//n,)+tuple(a//n for a in x[1:])
def minimal(xs):
    for x in xs:
        if all(nonneg(sub(y,x)) for y in xs): return x
    raise ValueError("ambiguous minimum")

@lru_cache(None)
def block(q,d,w):
    bits=[(w>>(3-i))&1 for i in range(4)]
    i=0 if d==1 else 3
    seen=set()
    for t in range(1,10000):
        key=q,i,tuple(bits)
        if key in seen: raise ValueError("internal loop")
        seen.add(key)
        a=TM[q][bits[i]*3:bits[i]*3+3]
        if a=="---": raise ValueError("halt")
        bits[i]=int(a[0]); i+=1 if a[1]=="R" else -1; q=ord(a[2])-65
        if i not in range(4):
            return q,1 if i==4 else 0,sum(b<<(3-j) for j,b in enumerate(bits)),t
    raise AssertionError

# Config q,d,left,right; both run lists nearest block first. d=0 left, 1 right.
def shape(s):
    q,d,L,R=s
    return q,d,tuple(w for w,n in L),tuple(w for w,n in R)
def counts(s): return tuple(n for side in s[2:] for w,n in side)
def rebuild(sh,ns):
    q,d,L,R=sh
    if len(ns)!=len(L)+len(R): raise ValueError("wrong count arity")
    return q,d,tuple(zip(L,ns[:len(L)])),tuple(zip(R,ns[len(L):]))
def push(side,w,n):
    if not pos(n): raise ValueError("nonpositive push")
    if not side and not w: return side
    if side and side[0][0]==w: return ((w,add(side[0][1],n)),)+side[1:]
    return ((w,n),)+side
def ordinary(s):
    q,d,L,R=s
    side=[L,R]; z=len(counts(s)[0])-1 if L or R else 0
    w,n=side[d][0] if side[d] else (0,con(1,z))
    nq,nd,nw,t=block(q,d,w)
    # All-length sweep if state/direction unchanged.
    take=n if q==nq and d==nd and side[d] else con(1,z)
    if side[d]:
        rem=sub(n,take)
        if not any(rem): side[d]=side[d][1:]
        elif pos(rem): side[d]=((w,rem),)+side[d][1:]
        else: raise ValueError("ambiguous zero")
    side[1-nd]=push(side[1-nd],nw,take)
    return nq,nd,*side

class Rule:
    def __init__(self,sh,base,delta,free,ops):
        self.sh=sh;self.base=base;self.delta=delta;self.free=free;self.ops=ops
    def apply(self,s):
        if shape(s)!=self.sh: raise ValueError("wrong shape")
        ns=counts(s);z=len(ns[0])-1
        if not (len(ns)==len(self.base)==len(self.free)==len(self.delta)): raise ValueError("wrong rule arity")
        for n,b,f in zip(ns,self.base,self.free):
            if f:
                if not nonneg(sub(n,con(b,z))): raise ValueError("threshold")
            elif n!=con(b,z): raise ValueError("fixed")
        # Number of iterations: min floor((n-b)/-d)+1.
        times=minimal([add(floor_div(sub(n,con(b,z)),-d),con(1,z))
                       for n,b,d in zip(ns,self.base,self.delta) if d<0])
        if not pos(times): raise ValueError("no positive iterations")
        out=tuple(add(n,mul(times,d)) for n,d in zip(ns,self.delta))
        if not all(pos(n) for n in out): raise ValueError("nonpositive result")
        return rebuild(self.sh,out)
def op(s,r): return ordinary(s) if r is None else r.apply(s)

def prove(s0,s1,ops):
    sh=shape(s0)
    if shape(s1)!=sh: return None
    n0=counts(s0);n1=counts(s1)
    if not n0: return None
    ds=[sub(b,a) for a,b in zip(n0,n1)]
    if any(any(x[1:]) for x in ds): return None
    delta=[x[0] for x in ds]
    if min(delta)>=0:return None
    for broad in (True,False):
      free=[d!=0 or any(n[1:]) or (broad and n[0]>1) for n,d in zip(n0,delta)]
      z=sum(free)
      for extra in (0,1,2,4,8):
        base=[min(n[0],max(1,1-d)+extra) if f else n[0] for n,d,f in zip(n0,delta,free)]
        if min(base)<1:continue
        var=iter(range(z));ns=[]
        for b,f in zip(base,free):
            v=list(con(b,z))
            if f:v[next(var)+1]=1
            ns.append(tuple(v))
        a=rebuild(sh,ns)
        try:
            for r in ops:a=op(a,r)
        except ValueError:continue
        if shape(a)==sh and counts(a)==tuple(add(n,con(d,z)) for n,d in zip(ns,delta)):
            return Rule(sh,base,delta,free,tuple(ops))
    return None

def mk(q,d,L,R,z=1):
    def conv(a):
        return tuple((int(w,2),n if isinstance(n,tuple) else con(n,z)) for w,n in a)
    return q,d,conv(L),conv(R)
def fmt(s):
    q,d,L,R=s
    f=lambda side:" ".join(f"{w:04b}^{n}" for w,n in side)
    return f"{f(L[::-1])} {'<' if d==0 else ''}{chr(q+65)}{'>' if d==1 else ''} {f(R)}"
def N(n):return mk(0,0,[("1011",n),("0001",1)],[("0001",28),("0011",1),("0000",1),("1000",1)],len(n)-1)
def Q(n):return mk(5,1,[("1101",1),("0011",1)],[("1010",1),("0010",n),("0000",1),("0010",28),("0000",1),("1000",1),("0100",1)],len(n)-1)
def D(X,Y2,Y1):
    return mk(2,1,[("0111",Y1),("1111",1),("1101",Y2),("0111",X),("1111",1),("1101",17)],[],len(X)-1)

class Engine:
    def __init__(self,s):
        self.s=s;self.rules=defaultdict(list);self.history={};self.ops=[];self.stats=Counter();self.i=0
    def tick(self):
        s=self.s;sh=shape(s)
        for r in self.rules[sh]:
            try:
                a=r.apply(s)
                if a==s:continue
            except ValueError:continue
            self.stats['applied']+=1;self.s=a;self.ops.append(r);self.i+=1;return
        old=self.history.get(sh)
        if old:
            prev,i=old
            if 0<len(self.ops)-i<=1000:
                self.stats['attempts']+=1
                r=prove(prev,s,self.ops[i:])
                if r:
                    self.rules[sh].append(r);self.stats['proved']+=1
                    try:
                        a=r.apply(s)
                        self.s=a;self.ops.append(r);self.i+=1;self.stats['applied']+=1;return
                    except ValueError:pass
        self.history[sh]=(s,len(self.ops))
        self.s=ordinary(s);self.ops.append(None);self.i+=1
    def run(self,limit,target=None,seconds=25):
        start=time.monotonic()
        for _ in range(limit):
            if target is not None and (target(self.s) if callable(target) else self.s==target):return "target"
            try:self.tick()
            except ValueError as ex:return str(ex)
            if self.i%1000==0 and time.monotonic()-start>seconds:return "time"
        return "limit"

# Replay ignores discovery history, checks the dependency DAG recursively,
# and checks the exact endpoint. The primitive/affine semantics are shared.
def verify(engine,start,target):
    verified=set(); active=set()
    def check(r):
        if r in verified:return
        if r in active:raise ValueError("cyclic rule dependency")
        active.add(r)
        if not r.ops or min(r.delta)>=0 or min(r.base)<1:
            raise ValueError("invalid rule")
        if any(d!=0 and not f for d,f in zip(r.delta,r.free)):
            raise ValueError("fixed field changes")
        ns=[];z=sum(r.free);it=iter(range(z))
        for b,f in zip(r.base,r.free):
            v=list(con(b,z))
            if f:v[next(it)+1]=1
            ns.append(tuple(v))
        a=rebuild(r.sh,ns)
        for subrule in r.ops:
            if subrule is not None:check(subrule)
            a=op(a,subrule)
        expect=tuple(add(n,con(d,z)) for n,d in zip(ns,r.delta))
        if shape(a)!=r.sh or counts(a)!=expect:
            raise ValueError("wrong rule result")
        active.remove(r);verified.add(r)
    s=start
    for r in engine.ops:
        if r is not None:check(r)
        s=op(s,r)
    if s!=target:raise ValueError("wrong final endpoint")
    return len(verified)

def prove_path(name,start,target,limit):
    e=Engine(start)
    status=e.run(limit,target,seconds=float("inf"))
    if status!="target":raise RuntimeError((name,status,e.i,fmt(e.s)))
    final=e.s
    print(name,e.i,dict(e.stats),"verified rules",verify(e,start,final),fmt(final),flush=True)
    return final

if __name__=="__main__":
    import sys
    tests=set(sys.argv[1:]) or {"N","A","Q","D","E"}
    if "N" in tests:prove_path("N",N((22,1)),N((38626190,262144)),1000000)
    if "A" in tests:prove_path("A",(0,1,(),()),N((508932094,)),2000000)
    if "Q" in tests:prove_path("Q",Q((14,1)),Q((38101896,262144)),1000000)
    if "D" in tests:prove_path("D",D((100,1,0,0),(130,0,1,0),(30,0,0,1)),
        D((454337500,1048576,0,0),(10,0,1,0),(6,0,0,1)),2000000)
    if "E" in tests:prove_path("E",D((349479900,1048576),(5759218639205926131,0),(13,0)),
        Q((23036877419765819664,8589934592)),2000000)
