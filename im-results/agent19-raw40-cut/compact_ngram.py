#!/usr/bin/env python3
"""Sparse n-gram closure, then compact the reachable deterministic stack summaries.

This is discovery, not the proof checker. Each side records only pushes actually
required by the abstract fixed point. Unused transitions are sent to summary 0;
a fresh fixed-point computation through emit_rungram.witness must reproduce the
same counts. The emitted FastBiDFA check then independently certifies all live
states with the original machine semantics, without a 2**width dense array.

Usage:
  python compact_ngram.py --table TABLE --left 16 --right 17 --id 198 --case 1RE
  python compact_ngram.py --data a0lb198-compact.json --namespace BB6.Agent19Raw40.A0LB1RECompact
The first command emits JSON; the second independently reconstructs the closure
from its compact delta and emits Lean source.
"""
import argparse
import json
from collections import defaultdict, deque
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / 'agent32-raw59'))
from emit_rungram import emit, witness

def abstract(table, starts, pushf, method, cap=1000000):
    p = table.replace('_', '')
    assert len(p) == 36
    p = [p[i:i+3] for i in range(0, 36, 3)]
    push = [{}, {}]
    incoming = [defaultdict(set), defaultdict(set)]
    waiting = [defaultdict(list), defaultdict(list)]
    for i,e in enumerate(incoming):
        e[starts[i]].add((0, starts[i]))
    states = {(0, 0, *starts)}
    work = deque(states)

    def add(q, a, l, r):
        state = q, a, l, r
        if state in states:
            return
        if p[2*q+a] == '---':
            raise ValueError('abstraction reaches unassigned transition')
        if len(states) >= cap:
            raise ValueError('state cap, no conclusion')
        states.add(state)
        work.append(state)

    def pop(state, bit, old):
        q, a, l, r = state
        m = p[2*q+a]
        w, d, n = int(m[0]), m[1], ord(m[2])-65
        if d == 'R':
            add(n, bit, pushf[0](l,w), old)
        else:
            add(n, bit, old, pushf[1](r,w))

    while work:
        state = work.popleft()
        q, a, l, r = state
        m = p[2*q+a]
        if m == '---':
            raise ValueError('abstraction reaches unassigned transition')
        w, d = int(m[0]), m[1]
        side, src, x = (0,l,r) if d == 'R' else (1,r,l)
        dst = pushf[side](src,w)
        push[side][src,w] = dst
        edge = w, src
        if edge not in incoming[side][dst]:
            incoming[side][dst].add(edge)
            for st in waiting[side][dst]:
                pop(st, *edge)
        waiting[1-side][x].append(state)
        for e in incoming[1-side][x]:
            pop(state, *e)

    dfa = []
    sizes = []
    counts = []
    for side in range(2):
        # Some queried-but-unpushed keys can be empty defaultdict entries.
        # A summary actually occurring in a state has a predecessor edge.
        live = sorted(x for x, es in incoming[side].items() if es)
        index = {x:i for i,x in enumerate(live)}
        assert index[starts[side]] == 0
        delta = [0] * (2*len(live))
        for (x,b), y in push[side].items():
            delta[2*index[x]+b] = index[y]
        dfa.append(delta)
        sizes.append(len(live))
        counts.append(sum(map(len,incoming[side].values())))
    ed, ss = witness(table, *dfa)
    new_counts = [sum(map(len,x.values())) for x in ed]
    assert len(ss) == len(states) and new_counts == counts
    return dict(table=table.replace('_',''),dfa=dfa,states=len(states),
                edges=sum(counts),method=method,
                summary_counts=sizes,edge_counts=counts)

def ngram(k):
    assert k >= 1
    mask = (1 << k)-1
    return lambda s,b: ((s<<1)|b)&mask

def rungram(params):
    runs,c0,c1,m0,m1=params
    C,M=[c0,c1],[m0,m1]
    assert runs>=1 and min(C+M)>=1
    def push(s,b):
        if not s and b==0:
            return ()
        if s and s[0]==b:
            n=s[1]+1
            if n>=C[b]+M[b]:
                n=C[b]
            return (b,n,*s[2:])
        return (b,1,*s)[:2*runs]
    return push

def laggram(params):
    # A lag-XOR maps a word of period k to an all-zero difference run.
    # Keep the last k raw bits, then a finite residue summary of the differences.
    k,r,c0,c1,m0,m1=params
    base=rungram([r,c0,c1,m0,m1])
    mask=(1<<k)-1
    def push(s,b):
        word,tail=s
        if k==0:
            return (0,base(tail,b))
        return (((word<<1)|b)&mask,base(tail,b^(word>>(k-1))))
    return push

def compact(table, widths, cap=1000000):
    return abstract(table,[0,0],[ngram(k) for k in widths],
                    ['compact-ngram',*widths],cap)

def compact_run(table,left,right,cap=1000000):
    return abstract(table,[(),()],[rungram(left),rungram(right)],
                    ['compact-run',left,right],cap)

def compact_lag(table,left,right,cap=1000000):
    return abstract(table,[(0,()),(0,())],[laggram(left),laggram(right)],
                    ['compact-lag',left,right],cap)

def find_lag(table,left,right,cap=30000):
    """Try near the recorded lag parameters first, then modest refinements.
    Failure of all attempts is unresolved, not evidence of halting.
    """
    def refinements(p):
        k,r,m0,m1=p
        for k1 in dict.fromkeys([k,k+1,k+2,3,4,5,6,7,8]):
            for r1 in dict.fromkeys([r+1,r,r+2,1,2,3,4]):
                if r1<1: continue
                for c0,c1 in [(1,2),(1,1),(2,2),(2,1),(1,3),(3,3),(3,1)]:
                    for a,b in dict.fromkeys([(m0,m1),(m0,4),(m0,2),(m0,3),(2*m0,m1),(m0,2*m1)]):
                        yield (k1,r1,c0,c1,a,b)
    if left!=right:
        # Pair the recorded asymmetric parameters with the same refinements.
        pairs=zip(refinements(left),refinements(right))
    else:
        pairs=((p,p) for p in refinements(left))
    for l,r in pairs:
        try:
            return compact_lag(table,l,r,cap)
        except ValueError:
            pass
    raise ValueError('lag-XOR search exhausted')

def lean(record, namespace):
    return ('import FastBiDFA\nset_option maxRecDepth 100000\n'
            'set_option maxHeartbeats 0\nnamespace '+namespace+'\n'
            'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA\n'
            +emit(record['id'],record['table'],*record['dfa'],
                  [record['states'],record['edges']])+'\nend '+namespace+'\n')

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table')
    ap.add_argument('--left',type=int)
    ap.add_argument('--right',type=int)
    ap.add_argument('--id',type=int,default=0)
    ap.add_argument('--case',default='')
    ap.add_argument('--cap',type=int,default=1000000)
    ap.add_argument('--data',type=Path)
    ap.add_argument('--namespace',default='BB6.Agent19Raw40.Compact')
    args=ap.parse_args()
    if args.data:
        rec=json.loads(args.data.read_text())
        print(lean(rec,args.namespace),end='')
    else:
        if args.table is None or args.left is None or args.right is None:
            ap.error('require --table --left --right, or --data')
        rec=compact(args.table,[args.left,args.right],args.cap)
        print(json.dumps(dict(c=args.case,id=args.id,**rec),separators=(',',':')))
