"""Deterministic reconstruction of the Raw122 run-aware certificates in hits.tsv.
Usage: python generate.py OUTPUT_DIR [certificate indices...].
The search and quotient are untrusted; the generated theorems use IndexedBiDFA.
"""
from collections import deque
from pathlib import Path
import sys

class Side:
    def __init__(self,k,c,p,lag):
        self.k,self.c,self.p,self.lag=k,c,p,lag
        self.keys=[(0,0,())]; self.idx={self.keys[0]:0}
        self.delta=[[-1,-1]]; self.edges=[{(0,0)}]; self.wait=[[]]
    def push(self,i,b):
        t=self.delta[i][b]
        if t>=0:return t
        h,last,runs=self.keys[i]
        if i==0 and b==0:t=0
        else:
            z=b^((h>>(self.lag-1))&1) if self.lag else b
            hh=((h<<1)|b)&((1<<self.lag)-1)
            if runs and last==z:
                n=runs[0]+1
                if n==self.c+self.p:n=self.c
                rr=(n,)+runs[1:]
            else:rr=(1,)+runs[:self.k-1]
            key=(hh,z,rr)
            t=self.idx.get(key)
            if t is None:
                t=len(self.keys);self.idx[key]=t;self.keys.append(key)
                self.delta.append([-1,-1]);self.edges.append(set());self.wait.append([])
        self.delta[i][b]=t;return t

def discover(m,lp,rp,cap=50000):
    s=[Side(*lp),Side(*rp)]
    moves=[m[i:i+3] for i in range(0,36,3)]
    moves=[None if x=='---' else (int(x[0]),int(x[1]=='L'),ord(x[2])-65) for x in moves]
    seen={(0,0,0,0)};todo=deque(seen)
    def add(q,b,l,r):
        assert moves[2*q+b] is not None,'hole'
        state=(q,b,l,r)
        if state not in seen:
            assert len(seen)<cap,'cap'
            seen.add(state);todo.append(state)
    def pop(st,e):
        q,b,l,r=st;w,dr,n=moves[q*2+b];z,src=e
        if dr==0:add(n,z,s[0].delta[l][w],src)
        else:add(n,z,src,s[1].delta[r][w])
    while todo:
        st=todo.popleft();q,b,l,r=st;w,dr,n=moves[2*q+b]
        old,x=(l,r) if dr==0 else (r,l)
        dest=s[dr].push(old,w);e=(w,old)
        if e not in s[dr].edges[dest]:
            s[dr].edges[dest].add(e)
            for other in s[dr].wait[dest]:pop(other,e)
        s[1-dr].wait[x].append(st)
        for e in s[1-dr].edges[x]:pop(st,e)
    return [[max(0,x) for pair in t.delta for x in pair] for t in s],len(seen)

def replay(m,dl,dr):
    moves=[m[i:i+3] for i in range(0,36,3)]
    ds=[dl,dr];es=[[set() for _ in range(len(d)//2)] for d in ds]
    ws=[[[] for _ in range(len(d)//2)] for d in ds]
    es[0][0].add((0,0));es[1][0].add((0,0))
    seen={(0,0,0,0)};todo=deque(seen)
    def add(s):
        assert moves[2*s[0]+s[1]]!='---',s
        if s not in seen:seen.add(s);todo.append(s)
    def advance(s,e):
        q,b,l,r=s;m=moves[2*q+b];w=int(m[0]);n=ord(m[2])-65;a,i=e
        if m[1]=='R':add((n,a,dl[2*l+w],i))
        else:add((n,a,i,dr[2*r+w]))
    while todo:
        s=todo.popleft();q,b,l,r=s;m=moves[q*2+b];w=int(m[0]);d=int(m[1]=='L')
        old,other=(l,r) if d==0 else (r,l)
        dest=ds[d][2*old+w];e=(w,old)
        if e not in es[d][dest]:
            es[d][dest].add(e)
            for state in ws[d][dest]:advance(state,e)
        ws[1-d][other].append(s)
        for e in es[1-d][other]:advance(s,e)
    return es,sorted(seen)

def compress(m,d):
    es,st=replay(m,*d)
    for side in (0,1):
        known={(src,b) for row in es[side] for b,src in row}
        d[side]=[x if (j//2,j%2) in known else -1 for j,x in enumerate(d[side])]
    def quotient(d,st,side):
        n=len(d[side])//2;ctx=[set() for _ in range(n)]
        for q,b,l,r in st:ctx[l if side==0 else r].add((q,b,r if side==0 else l))
        def cls(sig):
            ix={};return [ix.setdefault(x,len(ix)) for x in sig]
        p=cls([tuple(sorted(x)) for x in ctx])
        while True:
            q=cls([(p[i],*(p[x] if x>=0 else -1 for x in d[side][2*i:2*i+2])) for i in range(n)])
            if q==p:break
            p=q
        a=[-1]*(2*(max(p)+1))
        for i in range(n):
            for b in range(2):
                x=d[side][2*i+b]
                if x>=0:
                    assert a[2*p[i]+b] in [-1,p[x]]
                    a[2*p[i]+b]=p[x]
        d[side]=a
        st=list({(q,b,p[l],r) if side==0 else (q,b,l,p[r]) for q,b,l,r in st})
        return st,n-len(a)//2
    while True:
        st,a=quotient(d,st,0);st,b=quotient(d,st,1)
        if a+b==0:break
    d=[[max(0,x) for x in a] for a in d]
    es2,st2=replay(m,*d)
    assert len(st2)<=len(st)
    return d,len(st2)

def emit(m,ds,n,i,path):
    dl,dr=ds;es,states=replay(m,dl,dr);assert len(states)==n
    name=f'Agent29Raw122Indexed{i:03}';ns=f'BB6Coverage.Agent29Raw122Indexed.M{i:03}'
    f=['import IndexedBiDFA','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck']
    f+=['def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
    b=lambda v:'true' if v else 'false'
    for j in range(12):
        t=m[3*j:3*j+3]
        if t!='---':f.append(f'  | {j//2},{b(j%2)} => some (some ⟨{b(t[0]=="1")},{b(t[1]=="R")},{ord(t[2])-65}⟩)')
    f.append('  | _,_ => none')
    def node(k):
        q,a,l,r=states[k];return f'⟨{q},{b(a)},{l},{r}⟩'
    def tree(lo,hi):
        if lo==hi:return '.empty'
        mid=(lo+hi)//2;return f'(.node {tree(lo,mid)} {node(mid)} {tree(mid+1,hi)})'
    def build(lo,hi):
        if lo==hi:return '.empty'
        nm=f't{lo}_{hi}'
        if hi-lo<=16:f.append(f'def {nm} : Tree := {tree(lo,hi)}')
        else:
            mid=(lo+hi)//2;l,r=build(lo,mid),build(mid+1,hi)
            f.append(f'def {nm} : Tree := .node {l} {node(mid)} {r}')
        return nm
    root=build(0,len(states))
    f.append('def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#'+str(dl)+',#'+str(dr)+',')
    for e in es:f.append('  #['+','.join('['+','.join(f'({b(bit)},{src})' for bit,src in sorted(row))+']' for row in e)+'],')
    f.append(f'  {root}⟩')
    step='BB6Coverage.Agent1IndexedBiDFA.stepOK table cert'
    def prove(lo,hi):
        if lo==hi:return '(by rfl)'
        nm=f'check{lo}_{hi}';tr=f't{lo}_{hi}'
        if hi-lo<=16:f.append(f'theorem {nm} : {tr}.all ({step}) = true := by decide')
        else:
            mid=(lo+hi)//2;l,r=prove(lo,mid),prove(mid+1,hi)
            f.append(f'theorem node{mid} : {step} {node(mid)} = true := by decide')
            f.append(f'theorem {nm} : {tr}.all ({step}) = true := Tree.all_node node{mid} {l} {r}')
        return nm
    check=prove(0,len(states))
    f+=['theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := '+check,
        'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm',
        '#print axioms never',f'end {ns}','']
    (path/(name+'.lean')).write_text('\n'.join(f))
    return name

def rows():
    for line in Path(__file__).with_name('hits.tsv').read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        i,shard,m,lp,rp,n=line.split()
        yield int(i),shard,m,tuple(map(int,lp.split(','))),tuple(map(int,rp.split(','))),int(n)

def generate(path,indices=None):
    path.mkdir(parents=True,exist_ok=True)
    for i,shard,m,lp,rp,n0 in rows():
        if indices is not None and i not in indices:continue
        ds,n=discover(m,lp,rp)
        assert n==n0,(i,n,n0)
        ds,n=compress(m,ds)
        print(emit(m,ds,n,i,path),n,flush=True)

if __name__=='__main__':
    generate(Path(sys.argv[1]),set(map(int,sys.argv[2:])) if len(sys.argv)>2 else None)
