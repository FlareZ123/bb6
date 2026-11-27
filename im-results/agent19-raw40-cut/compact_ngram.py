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

def compact(table, widths, cap=1000000):
    p = table.replace('_', '')
    assert len(p) == 36
    p = [p[i:i+3] for i in range(0, 36, 3)]
    masks = [(1 << k)-1 for k in widths]
    assert min(widths) >= 1
    push = [{}, {}]
    incoming = [defaultdict(set), defaultdict(set)]
    waiting = [defaultdict(list), defaultdict(list)]
    for e in incoming:
        e[0].add((0, 0))
    states = {(0, 0, 0, 0)}
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
            add(n, bit, ((l << 1)|w)&masks[0], old)
        else:
            add(n, bit, old, ((r << 1)|w)&masks[1])

    while work:
        state = work.popleft()
        q, a, l, r = state
        m = p[2*q+a]
        if m == '---':
            raise ValueError('abstraction reaches unassigned transition')
        w, d = int(m[0]), m[1]
        side, src, x = (0,l,r) if d == 'R' else (1,r,l)
        dst = ((src<<1)|w)&masks[side]
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
        assert index[0] == 0
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
                edges=sum(counts),method=['compact-ngram',*widths],
                summary_counts=sizes,edge_counts=counts)

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
