#!/usr/bin/env python3
"""Search by finite run-length stack summaries, then quotient the accepted graph.
The search is untrusted; emit_mask independently recomputes the closure and
emits a certificate for the original Lean MaskBiDFA checker.
"""
from collections import defaultdict, deque
from pathlib import Path
import json, sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent32-raw59"))
from quotient_search import partition, refine, dfa, witness
from emit_mask import emit

# Each side: number of retained runs, zero threshold/period, one threshold/period.
# Lengths less than the threshold are exact; higher lengths are modulo period.
SPECS = {
    69: ("1RB0LF_1RC0LA_0RD---_1LD0LE_1RF0LE_1RA0RC",
         (8,16,2,8,4,5,10,2,10,2), (65094,588,1018,1859), (2017,168,178,417)),
    144: ("1RB0LF_1RC1RF_0RD---_1LD0LE_1RF0LE_1RA0RC",
          (8,6,3,16,2,5,12,2,8,3), (119215,1062,1123,2451), (2646,215,189,477)),
}

class RunDFA:
    def __init__(self,k,t0,p0,t1,p1):
        self.k=k
        self.threshold=(t0,t1)
        self.period=(p0,p1)
        self.words=[()]
        self.ids={():0}
        self.delta=[[-1,-1]]
    def push(self,s,b):
        if self.delta[s][b]>=0:return self.delta[s][b]
        word=self.words[s]
        if not word and b==0:
            new=()
        elif word and word[0][0]==b:
            n=word[0][1]+1
            if n>=self.threshold[b]+self.period[b]:n=self.threshold[b]
            new=((b,n),)+word[1:]
        else:
            new=(((b,1),)+word)[:self.k]
        if new not in self.ids:
            self.ids[new]=len(self.words)
            self.words.append(new)
            self.delta.append([-1,-1])
        dest=self.ids[new]
        self.delta[s][b]=dest
        return dest
    def total(self):
        return [max(0,x) for row in self.delta for x in row]

def run_search(table,params,cap=300000):
    D=[RunDFA(*params[:5]),RunDFA(*params[5:])]
    T=table.replace("_","")
    T=[T[3*i:3*i+3] for i in range(12)]
    E=[defaultdict(set),defaultdict(set)]
    wait=[defaultdict(list),defaultdict(list)]
    seen={(0,0,0)}
    todo=deque(seen)
    for e in E:e[0].add((0,0))
    def add(s,l,r):
        x=(s,l,r)
        if x not in seen:
            seen.add(x);todo.append(x)
    def pop(st,b,prev):
        s,l,r=st;w,d,q=T[s];w=int(w);q=ord(q)-65
        if d=="R":add(2*q+b,D[0].push(l,w),prev)
        else:add(2*q+b,prev,D[1].push(r,w))
    while todo:
        if len(seen)>cap:return None,len(seen),"cap"
        st=todo.popleft();s,l,r=st;w,d,q=T[s]
        if w=="-":return None,len(seen),"hole"
        w=int(w);d=int(d=="R")
        src=l if d else r;dst=D[1-d].push(src,w);e=(w,src)
        if e not in E[1-d][dst]:
            E[1-d][dst].add(e)
            for v in wait[1-d][dst]:pop(v,*e)
        x=r if d else l;wait[d][x].append(st)
        for b,y in E[d][x]:pop(st,b,y)
    return [d.total() for d in D],len(seen),(E,seen)

def edge_count(E):return sum(len(v) for e in E for v in e.values())

def quotient(table,D,E,S):
    C=[{0},{0}];P=[defaultdict(set),defaultdict(set)];push=[{},{}]
    for s,l,r in S:
        C[0].add(l);C[1].add(r)
        P[0][l].add((s,r));P[1][r].add((s,l))
    for d in range(2):
        for dst,edges in E[d].items():
            for b,src in edges:
                C[d].update((src,dst))
                assert D[d][2*src+b]==dst
                push[d][src,b]=dst
    # Exact partner profiles, then deterministic push congruence.
    cl=[refine(C[d],push[d],partition(C[d],lambda x:frozenset(P[d][x]))) for d in range(2)]
    small=[dfa(C[d],push[d],cl[d]) for d in range(2)]
    E2,n,S2=witness(table,small)
    assert E2 is not None
    return {"table":table,"dfa":small,"states":n,"edges":edge_count(E2),"method":"exact profiles"}

def generate(i):
    table,params,raw,small=SPECS[i]
    D,n,info=run_search(table,params)
    assert D is not None,(i,n,info)
    E,S=info
    assert (n,len(D[0])//2,len(D[1])//2,edge_count(E))==raw
    record=quotient(table,D,E,S)
    assert (record["states"],len(record["dfa"][0])//2,len(record["dfa"][1])//2,record["edges"])==small
    (ROOT/f"rf{i}-run-quotient.json").write_text(json.dumps(record,separators=(",",":"))+"\n")
    emit(ROOT,f"Raw54RF{i}RunQuot",record)

if __name__=="__main__":
    for i in map(int,sys.argv[1:] or list(SPECS)):generate(i)
