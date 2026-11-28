#!/usr/bin/env python3
"""Deterministically reconstruct the 10-state/side Box27 exceptional FAR.

Untrusted discovery only: the emitted Lean certificate is independently checked
against the original two-sided stack semantics and authentic partial TM source.
No bounded trace, seed, random choice, or search heuristic is trusted by Lean.
"""
from pathlib import Path
import argparse

CODES = (8,24,11,8,13,13,14,17,22,15,4,0)
DELTA = ((2,0,2,3),(1,3,2,3))

def compose(f,g):
    return tuple(f[x] for x in g)

def stack():
    tail=tuple(range(4))
    for _ in range(8): tail=compose(tail,DELTA[0])
    basis=[tail]; idx={tail:0}; edges=[]
    for f in basis:
        z=[]
        for d in DELTA:
            v=compose(f,d)
            if v not in idx: idx[v]=len(basis);basis.append(v)
            z.append(idx[v])
        edges.append(z)
    states=[(0,0)];idx={(0,0):0};push=[]
    for a,v in states:
        row=[]
        for b in (0,1):
            p=(edges[a][b],(b<<2)|(v>>1))
            if p not in idx:idx[p]=len(states);states.append(p)
            row.append(idx[p])
        push.append(row)
    pop=[[] for _ in states]
    for i,row in enumerate(push):
        for b,j in enumerate(row):pop[j].append((b,i))
    assert len(basis)==3 and len(states)==10
    return pop,push

def closure(pop,push):
    todo=[(0,0,0,0)];seen=set(todo)
    for q,a,l,r in todo:
        t=CODES[2*q+a]
        assert t>0, (q,a,l,r)
        v=t-1;w=(v>>1)&1;d=v&1;qn=v>>2
        if d:
            nxt=((qn,b,push[l][w],rr) for b,rr in pop[r])
        else:
            nxt=((qn,b,ll,push[r][w]) for b,ll in pop[l])
        for x in nxt:
            if x not in seen:seen.add(x);todo.append(x)
    assert len(todo)==306
    return todo

def trie(v):
    if not v:return '.empty'
    if v==[0]:return '.leaf'
    return '(.branch '+trie([x//2 for x in v if x%2==0])+' '+trie([(x-1)//2 for x in v if x%2==1])+')'

def emit(pop,push,states):
    n=len(push)
    groups=[[] for _ in range(12)]
    for q,a,l,r in states:groups[2*q+a].append(r+n*l)
    groups=[sorted(v) for v in groups]
    assert len(groups[11])==0
    b=lambda x: 'true' if x else 'false'
    s='⟨#['+','.join('['+','.join(f'({b(v)},{i})' for v,i in es)+']' for es in pop)+'], #['+','.join(f'({x},{y})' for x,y in push)+']⟩'
    rows=[]
    for i,t in enumerate(CODES):
        if not t:continue
        q,a=divmod(i,2);v=t-1
        rows.append(f'  | ({q},{b(a)}) => some (some ⟨{b((v>>1)&1)},{b(v&1)},{v>>2}⟩)')
    return '''import TwoSidedAutomata
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Nonhalting FAR for the unique 25-completion E0=22 holdout.
    Ten states per stack; 306 reachable abstract configurations. -/
namespace BB6.Agent49.Box27ExceptionalFAR
open BB6Coverage

def table : PartialMachine := fun s => match s with
'''+ '\n'.join(rows)+'''
  | _ => none

def cert : BB6.Agent4Automata.Cert :=
  ⟨'''+s+', '+s+', #['+','.join(trie(v) for v in groups)+''']⟩

theorem checked : BB6.Agent4Automata.check table cert = true := by decide

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent4Automata.never table cert checked m hm

#print axioms checked
#print axioms never
end BB6.Agent49.Box27ExceptionalFAR
'''

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'Box27ExceptionalFAR.lean')
    a=p.parse_args()
    pop,push=stack();reach=closure(pop,push)
    a.output.write_text(emit(pop,push,reach))
    print('stack_states_per_side',len(push),'reachable_abstract_configs',len(reach),'output',a.output)
