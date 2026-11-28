#!/usr/bin/env python3
"""Untrusted 25-way split-tree generator; Lean checks every terminal."""
from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
import json

PARENT = ('1RB', None, '1RC', None, '0RD', None, '1LC', None, None, None, None, None)
STATES = 'ABCDEF'
CHOICES = ('H',) + tuple(w+d+q for q,w,d in product(STATES,'01','LR'))
CODES = {None:0, 'H':1, **{w+d+q:2+i for i,(w,d,q) in enumerate(product('01','LR',STATES))}}

@lru_cache(maxsize=100000)
def closed_states(p):
    ss = set(range(6))
    while True:
        nxt = {q for q in ss if all(p[2*q+b] not in (None,'H') and STATES.index(p[2*q+b][2]) in ss for b in (0,1))}
        if nxt == ss:
            return tuple(sorted(ss))
        ss = nxt

@lru_cache(maxsize=100000)
def simulate(p, cap, window):
    q = head = 0
    ones, hist = set(), []
    ss = closed_states(p)
    for t in range(cap+1):
        if q in ss:
            return ('closed',t,ss)
        for i in range(max(0,t-window),t):
            oq,oh,oo = hist[i]
            if oq != q:
                continue
            delta = head-oh
            for right in ((True,False) if delta == 0 else (delta > 0,)):
                b = (min if right else max)(x[1] for x in hist[i:])
                def side(x):
                    return x >= b if right else x <= b
                if (all(not side(x) or x+delta in ones for x in oo) and
                    all(not side(x-delta) or x-delta in oo for x in ones)):
                    return ('side',i,t-i,right,b)
        slot = 2*q+int(head in ones)
        a = p[slot]
        if a is None:
            return ('split',slot,t)
        if a == 'H':
            return ('halt',t)
        hist.append((q,head,ones.copy()))
        if a[0] == '1':
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if a[1] == 'R' else -1
        q = STATES.index(a[2])
    return ('residual',cap)

def refine(p,s,a):
    assert p[s] is None
    return p[:s]+(a,)+p[s+1:]

def codes(p):
    return [CODES[a] for a in p]

def parse(text):
    flat = text.replace('_','')
    assert len(flat)==36
    p = tuple(None if flat[i:i+3]=='---' else 'H' if flat[i:i+3]=='HLT' else flat[i:i+3] for i in range(0,36,3))
    assert all(a in CODES for a in p)
    assert all(a is None or p[i]==a for i,a in enumerate(PARENT))
    return p

def format_table(p):
    s = ['---' if a is None else 'HLT' if a=='H' else a for a in p]
    return '_'.join(s[i]+s[i+1] for i in range(0,12,2))

class Builder:
    def __init__(self,cap=300,window=40,depth=12):
        self.cap,self.window,self.depth=cap,window,depth
        self.nodes,self.rows,self.stats,self.mass=[],[],Counter(),Counter()
        self.maxhalt=0
        self.attainer=None
    def visit(self,p,depth=0):
        i=len(self.nodes);self.nodes.append(None)
        cert=simulate(p,self.cap,self.window)
        kind=cert[0]
        if kind=='split' and depth<self.depth:
            s=cert[1]
            children=[self.visit(refine(p,s,a),depth+1) for a in CHOICES]
            self.nodes[i]=('split',s,children)
            self.stats['split']+=1
        else:
            if kind in ('residual','split'):
                j=len(self.rows);self.rows.append(codes(p))
                self.nodes[i]=('residual',j);kind='residual'
            else:
                self.nodes[i]=cert
                if kind=='halt' and cert[1]+1>self.maxhalt:
                    self.maxhalt=cert[1]+1;self.attainer=(p,cert[1])
            self.stats[kind]+=1
            self.mass[kind]+=25**p.count(None)
        return i

def lean_node(node):
    kind,*args=node
    if kind=='split':
        s,children=args
        return f'.split ({s//2},{str(bool(s%2)).lower()}) {children}'
    if kind=='residual':
        return f'.residual {args[0]}'
    if kind=='halt':
        return f'.leaf (.halt {args[0]})'
    if kind=='side':
        entry,period,right,b=args
        return f'.leaf (.side {entry} {period} {str(right).lower()} ({b}))'
    if kind=='closed':
        entry,ss=args
        return f'.leaf (.closed {entry} {list(ss)})'
    raise ValueError(node)

def emit(b,p,namespace,output):
    bound=max(1,b.maxhalt)
    assert sum(b.mass.values())==25**p.count(None)
    assert len(b.nodes)==1+25*b.stats['split']
    lines=['import Raw34Plan','set_option maxRecDepth 100000','set_option maxHeartbeats 0',
           f'namespace {namespace}','open BB6Coverage BB6.Agent50Raw34Plan',
           f'/-- Literal source parent: {format_table(p)}. All 25 choices are checked. -/',
           f'def parent : PartialMachine := table {codes(p)}',
           f'def residuals : List (List Nat) := {b.rows}',
           'def nodes : Array Node := #[',
           ',\n'.join('  '+lean_node(n) for n in b.nodes),']',
           f'theorem checked : check nodes residuals {bound} {p.count(None)+1} 0 parent = true := by decide +kernel',
           f'theorem conditional {{good : Machine → Prop}} (lift : ∀ m, DecidedBelow {bound} m → good m)',
           '    (hrows : ∀ (j : Nat) (row : List Nat), residuals[j]? = some row → Cover good (table row)) :',
           '    Cover good parent :=',
           f'  check_sound nodes residuals {bound} lift hrows {p.count(None)+1} 0 parent checked',
           f'theorem residual_count : residuals.length = {len(b.rows)} := by decide']
    if not b.rows:
        lines += [f'theorem cover : Cover (DecidedBelow {bound}) parent :=',
                  f'  check_closed nodes {bound} {p.count(None)+1} 0 parent checked']
    if b.attainer:
        a,n=b.attainer
        lines += [f'def attainer : PartialMachine := table {codes(a)}',
                  f'theorem attainer_halt : finiteHaltCheck attainer {n} = true := by decide +kernel']
    lines += ['#print axioms checked','#print axioms conditional','#print axioms residual_count']
    if not b.rows:lines.append('#print axioms cover')
    if b.attainer:lines.append('#print axioms attainer_halt')
    lines += [f'end {namespace}','']
    Path(output).write_text('\n'.join(lines))

def main():
    ap=ArgumentParser()
    ap.add_argument('--parent',default='1RB---_1RC---_0RD0RE_1LC0LD_---0LF_0LC---')
    ap.add_argument('--cap',type=int,default=300);ap.add_argument('--window',type=int,default=40)
    ap.add_argument('--depth',type=int,default=12)
    ap.add_argument('--namespace',default='BB6.Agent50Raw34Pilot')
    ap.add_argument('--output',default='Raw34Pilot.lean')
    ap.add_argument('--summary',default=None)
    args=ap.parse_args()
    p=parse(args.parent);b=Builder(args.cap,args.window,args.depth);b.visit(p)
    emit(b,p,args.namespace,args.output)
    summary=dict(parent=format_table(p),nodes=len(b.nodes),stats=dict(b.stats),mass=dict(b.mass),max_halt_score=b.maxhalt,residuals=b.rows,attainer=None if b.attainer is None else format_table(b.attainer[0]))
    if args.summary:Path(args.summary).write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary))

if __name__=='__main__':main()
