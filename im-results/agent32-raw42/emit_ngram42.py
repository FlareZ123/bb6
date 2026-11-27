#!/usr/bin/env python3
"""Emit kernel-checked asymmetric n-gram certificates from table/width rows.
Input: one line per certificate: id, compact 36-char table, left/right widths.
Uses Agent32's AsymNGram checker. Discovery output is not trusted by Lean.
"""
import sys
from collections import defaultdict

def saturate(s, kl, kr):
    tr=[None if s[i]=='-' else (ord(s[i+2])-65,int(s[i]),s[i+1]=='R') for i in range(0,36,3)]
    k=[kl,kr]; masks=[(1<<v)-1 for v in k]
    edges=[defaultdict(set),defaultdict(set)]
    waiting=[defaultdict(list),defaultdict(list)]
    seen=set(); todo=[]
    def add(c):
        if c not in seen:
            assert tr[2*c[0]+c[1]] is not None, ('reachable hole',c)
            seen.add(c);todo.append(c)
    def pop(c,e):
        q,a,l,r=c; q,w,R=tr[2*q+a]
        if R:add((q,r&1,((l<<1)|w)&masks[0],(r>>1)|(e<<(kr-1))))
        else:add((q,l&1,(l>>1)|(e<<(kl-1)),((r<<1)|w)&masks[1]))
    def edge(d,x,e):
        if e in edges[d][x]:return
        edges[d][x].add(e)
        for c in waiting[d][x]:pop(c,e)
    edge(0,0,0);edge(1,0,0);add((0,0,0,0))
    for c in todo:
        q,a,l,r=c; _,w,R=tr[2*q+a];d=0 if R else 1
        p=(l,r)[d];v=(l,r)[1-d]
        edge(d,((p<<1)|w)&masks[d],p>>(k[d]-1))
        waiting[1-d][v].append(c)
        for e in sorted(edges[1-d][v]):pop(c,e)
    rows=[[] for _ in range(12)]
    for q,a,l,r in seen:rows[2*q+a].append((l<<kr)|r)
    return [[2*x+e for x,es in ed.items() for e in es] for ed in edges], rows

def trie(xs):
    if not xs:return '.empty'
    if set(xs)=={0}:return '.leaf'
    return f'(.branch {trie([x//2 for x in xs if not x%2])} {trie([x//2 for x in xs if x%2])})'

def emit(i,s,kl,kr):
    edges,rows=saturate(s,kl,kr)
    print(f'namespace Leaf{i}\n-- {s}\ndef table : PartialMachine := fun s => match s with')
    for j in range(12):
        v=s[3*j:3*j+3]
        if v!='---':print(f'  | ({j//2}, {str(bool(j%2)).lower()}) => some (some ⟨{str(v[0]=="1").lower()}, {str(v[1]=="R").lower()}, {ord(v[2])-65}⟩)')
    print('  | _ => none')
    print(f'def cert : Cert := ⟨{kl-1}, {kr-1}, {trie(edges[0])}, {trie(edges[1])}, #[{", ".join(map(trie,rows))}]⟩')
    print('theorem checked : check table cert = true := by decide')
    print('theorem live (m : Machine) (hm : compatible table m) : NeverHalts m := never table cert checked m hm')
    print(f'#print axioms live\nend Leaf{i}')

if __name__=='__main__':
    print('import AsymNGram\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent32Raw42RA.NGram\nopen BB6Coverage BB6.Agent32AsymNGram')
    for line in sys.stdin:
        i,s,l,r=line.split();emit(int(i),s,int(l),int(r))
    print('end BB6.Agent32Raw42RA.NGram')
