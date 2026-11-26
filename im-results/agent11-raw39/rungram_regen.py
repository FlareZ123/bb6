"""Lazy run-length/residue stack summaries for FastBiDFA candidate production."""
from collections import defaultdict, deque

class RunDFA:
    def __init__(self, params):
        self.k, self.c0, self.c1, self.m0, self.m1 = params
        assert self.k >= 1 and min(self.c0,self.c1,self.m0,self.m1) >= 1
        self.words = [()]
        self.ids = {(): 0}
        self.delta = [[None,None]]

    def push(self, idx, b):
        j = self.delta[idx][b]
        if j is not None:
            return j
        v = self.words[idx]
        if not v:
            w = ((1,1),) if b else ()
        elif v[0][0] == b:
            c,m = (self.c1,self.m1) if b else (self.c0,self.m0)
            n = v[0][1] + 1
            if n == c+m:
                n = c
            w = ((b,n),) + v[1:]
        else:
            w = (((b,1),) + v)[:self.k]
        if w not in self.ids:
            self.ids[w] = len(self.words)
            self.words.append(w)
            self.delta.append([None,None])
        j = self.ids[w]
        self.delta[idx][b] = j
        return j

    def finish(self):
        # Unused entries are arbitrary; FastBiDFA checks every required push.
        return [0 if j is None else j for v in self.delta for j in v]

def discover(table, left, right, cap=100000, dfa=RunDFA):
    ds = [dfa(left),dfa(right)]
    p = table.replace('_','')
    assert len(p)==36
    p = [p[i:i+3] for i in range(0,36,3)]
    edges = [defaultdict(set),defaultdict(set)]
    waiting = [defaultdict(list),defaultdict(list)]
    todo = deque([(0,0,0,0)])
    seen = set(todo)
    for e in edges: e[0].add((0,0))
    def add(q,a,l,r):
        s = (q,a,l,r)
        if s not in seen:
            if p[2*q+a] == '---':
                raise ValueError(('unknown',s))
            seen.add(s); todo.append(s)
            if len(seen)>cap: raise ValueError('cap')
    def pop(s,b,src):
        q,a,l,r=s
        m=p[2*q+a]; w,n=int(m[0]),ord(m[2])-65
        if m[1]=='R': add(n,b,ds[0].push(l,w),src)
        else: add(n,b,src,ds[1].push(r,w))
    while todo:
        s=todo.popleft(); q,a,l,r=s
        m=p[2*q+a]
        if m=='---': raise ValueError(('unknown',s))
        w=int(m[0]); side=int(m[1]=='R')
        old=l if side else r
        dest=ds[1-side].push(old,w)
        e=(w,old)
        if e not in edges[1-side][dest]:
            edges[1-side][dest].add(e)
            for st in waiting[1-side][dest]:pop(st,*e)
        x=r if side else l
        waiting[side][x].append(s)
        for b,y in sorted(edges[side][x]):pop(s,b,y)
    return ds[0].finish(),ds[1].finish(),len(seen),sum(len(v) for es in edges for v in es.values())
