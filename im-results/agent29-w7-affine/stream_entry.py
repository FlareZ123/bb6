"""Memory-bounded W7-2 certificate discovery and topological replay."""
import json, sys, time, gzip
from collections import defaultdict, deque, Counter
from affine_replay import *

class StreamEngine:
    def __init__(self,s,out):
        self.s=s;self.out=out;self.rules=defaultdict(list);self.history={}
        self.order=deque();self.ops=deque(maxlen=1000);self.stats=Counter();self.i=0;self.nr=0;self.pending=0
    def flush(self):
        if self.pending:
            self.out.write(json.dumps(["B",self.pending],separators=(",",":"))+"\n")
            self.pending=0
    def record(self,r):
        self.flush();self.nr+=1;r.id=self.nr
        self.out.write(json.dumps(["R",r.sh,r.base,r.delta,r.free,[x.id if x else 0 for x in r.ops]],separators=(",",":"))+"\n")
        r.ops=()
    def done(self,a,r):
        self.s=a;self.ops.append(r);self.i+=1
        if r is None:self.pending+=1
        else:
            self.flush();self.out.write(json.dumps(["A",r.id])+"\n")
    def tick(self):
        s=self.s;sh=shape(s)
        for r in self.rules[sh]:
            try:
                a=r.apply(s)
                if a==s:continue
            except ValueError:continue
            self.stats["applied"]+=1;self.done(a,r);return
        old=self.history.get(sh)
        if old:
            prev,i=old
            length=self.i-i
            if 0<length<=len(self.ops):
                self.stats["attempts"]+=1
                r=prove(prev,s,list(self.ops)[-length:])
                if r:
                    self.record(r)
                    self.rules[sh].append(r)
                    self.stats["proved"]+=1
                    try:
                        a=r.apply(s);self.stats["applied"]+=1;self.done(a,r);return
                    except ValueError:pass
        while self.order and self.i-self.order[0][0]>1000:
            j,k=self.order.popleft()
            if self.history.get(k,(None,None))[1]==j:del self.history[k]
        self.history[sh]=(s,self.i);self.order.append((self.i,sh))
        self.done(ordinary(s),None)
    def run(self,limit,target):
        start=time.monotonic()
        for _ in range(limit):
            if target(self.s):
                self.flush();return self.s
            self.tick()
            if self.i%250000==0:
                print("progress",self.i,self.nr,round(time.monotonic()-start,1),fmt(self.s),flush=True)
        self.flush();raise RuntimeError(("limit",self.i,fmt(self.s)))

def thaw_shape(s):
    return s[0],s[1],tuple(s[2]),tuple(s[3])

def verify_stream(path,start,target):
    rules=[None];s=start;n=0
    with gzip.open(path,"rt") as f:
        for line in f:
            record=json.loads(line)
            if record[0]=="B":
                if not isinstance(record[1],int) or record[1]<1:raise ValueError("bad block count")
                for _ in range(record[1]):s=ordinary(s)
                n+=record[1]
            elif record[0]=="A":
                i=record[1]
                if not 0<i<len(rules):raise ValueError("invalid applied rule ID")
                s=rules[i].apply(s);n+=1
            elif record[0]=="R":
                _,sh,base,delta,free,ops=record
                sh=thaw_shape(sh)
                if not(len(base)==len(delta)==len(free)==len(sh[2])+len(sh[3])):raise ValueError("arity")
                if not ops or min(base)<1 or min(delta)>=0 or any(d and not f for d,f in zip(delta,free)):raise ValueError("invalid rule")
                if any(not 0<=i<len(rules) for i in ops):raise ValueError("dependency order")
                z=sum(free);it=iter(range(z));ns=[]
                for b,v in zip(base,free):
                    a=list(con(b,z))
                    if v:a[next(it)+1]=1
                    ns.append(tuple(a))
                t=rebuild(sh,ns)
                for i in ops:t=op(t,rules[i])
                if shape(t)!=sh or counts(t)!=tuple(add(a,con(d,z)) for a,d in zip(ns,delta)):raise ValueError("rule proof mismatch")
                rules.append(Rule(sh,base,delta,free,()))
            else:raise ValueError("unknown record")
    if not target(s):raise ValueError(("endpoint",fmt(s)))
    print("verified",n,"rules",len(rules)-1,fmt(s),flush=True)
    return s

def goal(s):
    if shape(s)!=shape(D((100,),(130,),(30,))):return False
    ns=counts(s)
    return ns[0]==(939468133961604901,) and ns[2]==(10456559309013950571,) and ns[3][0]>=100

if __name__=="__main__":
    path=sys.argv[2] if len(sys.argv)>2 else "w7-D-entry.jsonl.gz"
    start=(3,1,(),())
    if sys.argv[1]=="discover":
        with gzip.open(path,"wt",compresslevel=3) as f:
            e=StreamEngine(start,f)
            s=e.run(15000000,goal)
            print("target",e.i,e.nr,fmt(s),flush=True)
    elif sys.argv[1]=="verify":verify_stream(path,start,goal)
    else:raise ValueError("mode")
