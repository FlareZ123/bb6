#!/usr/bin/env python3
"""Two-level run-pair push abstraction and original-source MaskBiDFA certificate.

The abstraction is untrusted discovery.  Independently replayed primitive
transition closure and the Lean checker establish NeverHalts, not the run
partition itself.  Input is cold_census.py's frozen 1RA/miss.txt.
"""
from collections import defaultdict, deque
from pathlib import Path
import hashlib, sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent32-raw59"))
from quotient_search import partition, refine, dfa, witness
from emit_mask import emit_data

class PairDfa:
    """Leading partial 0^a1^b followed by groups of identical complete pairs."""
    def __init__(self,k,t0,p0,t1,p1,tg,pg):
        self.k=k
        self.t=(t0,t1)
        self.p=(p0,p1)
        self.tg=tg
        self.pg=pg
        self.words=[(0,0,())]
        self.ids={self.words[0]:0}
        self.delta={}
    @staticmethod
    def inc(n,t,p):
        n+=1
        return t if n>=t+p else n
    def push(self,s,b):
        x=(s,b)
        if x in self.delta:
            return self.delta[x]
        a,o,g=self.words[s]
        if b==0:
            if o:
                a=self.inc(a,self.t[0],self.p[0])
        elif not a:
            o=self.inc(o,self.t[1],self.p[1])
        else:
            if g and g[0][:2]==(a,o):
                g=((a,o,self.inc(g[0][2],self.tg,self.pg)),)+g[1:]
            else:
                g=(((a,o,1),)+g)[:self.k]
            a,o=0,1
        w=(a,o,g)
        if w not in self.ids:
            self.ids[w]=len(self.words)
            self.words.append(w)
        self.delta[x]=self.ids[w]
        return self.delta[x]

def primitive(table,params,cap=1000000):
    D=[PairDfa(*params[:7]),PairDfa(*params[7:])]
    T=table.replace("_","")
    T=[T[3*i:3*i+3] for i in range(12)]
    E=[defaultdict(set),defaultdict(set)]
    wait=[defaultdict(list),defaultdict(list)]
    S={(0,0,0)}
    todo=deque(S)
    for e in E:
        e[0].add((0,0))
    def add(s,l,r):
        st=(s,l,r)
        if st not in S:
            S.add(st)
            todo.append(st)
    def pop(st,b,prev):
        s,l,r=st
        w,dd,q=T[s]
        w=int(w)
        q=ord(q)-65
        if dd=="R":
            add(2*q+b,D[0].push(l,w),prev)
        else:
            add(2*q+b,prev,D[1].push(r,w))
    while todo:
        if len(S)>cap:
            return "cap",D,E,S
        st=todo.popleft()
        s,l,r=st
        w,dd,q=T[s]
        if w=="-":
            return "hole",D,E,S
        w=int(w)
        dd=int(dd=="R")
        src=l if dd else r
        dst=D[1-dd].push(src,w)
        e=w,src
        if e not in E[1-dd][dst]:
            E[1-dd][dst].add(e)
            for v in wait[1-dd][dst]:
                pop(v,*e)
        x=r if dd else l
        wait[dd][x].append(st)
        for b,y in E[dd][x]:
            pop(st,b,y)
    return "closed",D,E,S

def compress(table,D,E,S):
    C=[{0},{0}]
    P=[defaultdict(set),defaultdict(set)]
    push=[{},{}]
    for s,l,r in S:
        C[0].add(l)
        C[1].add(r)
        P[0][l].add((s,r))
        P[1][r].add((s,l))
    for d in range(2):
        for dst,edges in E[d].items():
            for b,src in edges:
                C[d].update((src,dst))
                assert D[d].push(src,b)==dst
                push[d][src,b]=dst
    def trial(cl,label):
        small=[dfa(C[d],push[d],cl[d]) for d in range(2)]
        E2,n,S2=witness(table,small,400000)
        print(label,[len(d)//2 for d in small],n,"closed" if E2 is not None else S2,flush=True)
        return (small,E2,S2) if E2 is not None else None
    cl=[refine(C[d],push[d],partition(C[d],lambda x:0)) for d in range(2)]
    out=trial(cl,"language")
    if out is not None:
        return out
    cl=[refine(C[d],push[d],partition(C[d],lambda x:frozenset(s for s,_ in P[d][x]))) for d in range(2)]
    out=trial(cl,"slots")
    if out is not None:
        return out
    for it in range(8):
        new=[refine(C[d],push[d],partition(C[d],lambda x:(cl[d][x],frozenset((s,cl[1-d][y]) for s,y in P[d][x])))) for d in range(2)]
        if new==cl:
            break
        cl=new
        out=trial(cl,f"partner {it+1}")
        if out is not None:
            return out
    cl=[refine(C[d],push[d],partition(C[d],lambda x:frozenset(P[d][x]))) for d in range(2)]
    out=trial(cl,"exact")
    assert out is not None
    return out

SPECS={
    250:((6,3,1,32,6,16,6,10,32,6,32,6,16,6),(242163,2937,38747,41852),(4150,933,912,1986)),
}
def edge_count(E):
    return sum(len(v) for e in E for v in e.values())
def emit(rows,out,i):
    params,raw,small=SPECS[i]
    table=rows[i]
    assert i!=250 or table=="1RB---_1RC0RF_0RD0RF_1LD0LE_1RA0LE_1RB1RE"
    status,D,E,S=primitive(table,params)
    assert status=="closed",(status,len(S))
    assert (len(S),len(D[0].words),len(D[1].words),edge_count(E))==raw
    D,E,S=compress(table,D,E,S)
    assert (len(S),len(D[0])//2,len(D[1])//2,edge_count(E))==small
    name=f"Raw54OneRAPair{i}"
    emit_data(out,name,table,D,E,S)
    print(name,hashlib.sha256((out/(name+".lean")).read_bytes()).hexdigest())
if __name__=="__main__":
    path=Path(sys.argv[1])
    assert hashlib.sha256(path.read_bytes()).hexdigest()=="5b92ebb47de7e0e1edc4eb3acb2fbcc5b0956856b283a87dd93f0a928511e0da"
    rows=path.read_text().splitlines()
    out=Path(sys.argv[2])
    for i in map(int,sys.argv[3:] or list(SPECS)):
        emit(rows,out,i)
