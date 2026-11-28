#!/usr/bin/env python3
"""Rewrite exact closedCheck proof terms to a prefix-sharing kernel checker.
The exported theorem statements and all original Cut trees remain unchanged.
"""
import re
from pathlib import Path
import sys

REFINE = re.compile(r'refine (.+) \((\d),\s*(true|false)\) \(some ⟨(true|false),\s*(true|false),\s*(\d)⟩\)$')
ROOT = re.compile(r'^abbrev (pRoot\w+) := (.*)$')
CHECK = re.compile(r'^(theorem cRoot\w+ : closedCheck (\d+) (\d+) (pRoot\w+) (tRoot\w+) = true := by )decide(?: \+kernel)?$')

def bit(x):return int(x=='true')
def boolword(x):return 'true' if x else 'false'

def unparen(expr):
    while expr.startswith('(') and expr.endswith(')'):
        n=0
        for i,ch in enumerate(expr):
            if ch=='(':n+=1
            elif ch==')':n-=1
            if n==0:break
        if i!=len(expr)-1:break
        expr=expr[1:-1]
    return expr

def parse(expr, tables):
    expr=unparen(expr)
    if expr in tables:return tables[expr]
    m=REFINE.fullmatch(expr)
    if not m:raise ValueError(expr)
    parent,q,a,w,r,j=m.groups()
    t=parse(parent,tables).copy();s=int(q),bit(a)
    assert s not in t
    t[s]=bit(w),bit(r),int(j)
    return t

def root_table(branch):
    return {(0,0):(1,1,1),(1,0):(1,1,2),(2,0):(0,1,3),(3,0):(1,0,3),(3,1):(0,0,1),(1,1):(int(branch[0]),int(branch[1]=='R'),ord(branch[2])-65)}

def prefix(t,cap=100006):
    q=l=r=h=0
    for i in range(cap+1):
        s=q,l%2
        if s not in t:return i,q,l,r,h
        w,d,q=t[s]
        if d:l,r,h=r%2+2*(w+2*(l//2)),r//2,h+1
        else:l,r,h=l//2,w+2*r,h-1
    return None

def transform(src,branch):
    tables={'p':root_table(branch)};exprs={};keys={};out=['import PrefixClosed'];count=0;common=0
    for line in src.splitlines():
        m=ROOT.fullmatch(line)
        if m:
            name,expr=m.groups();exprs[name]=expr
            try:tables[name]=parse(expr,tables)
            except (ValueError,AssertionError):pass
        m=CHECK.fullmatch(line)
        if not m:out.append(line);continue
        start,B,cut,p,t=m.groups();count+=1
        expr=exprs.get(p,'');r=REFINE.fullmatch(expr)
        if r:
            parent,q,a,w,d,j=r.groups();k=(parent,q,a)
            try:
                table=parse(parent,tables)
                z=prefix(table) if (int(q),bit(a)) not in table else None
            except (ValueError,AssertionError):z=None
            if z:
                n,c,l,rr,h=z
                if k not in keys:
                    i=len(keys);keys[k]=i
                    out += [f'private abbrev prefixP{i} : PartialMachine := {parent}',
                            f'private def prefixZ{i} : BB6.Agent3PackedCycle.H := ⟨⟨{c},{l},{rr}⟩,({h})⟩',
                            f'private theorem prefixH{i} : BB6.Agent3PackedCycle.runH prefixP{i} {n} BB6.Agent3PackedCycle.startH = some prefixZ{i} := by decide +kernel',
                            f'private theorem prefixU{i} : prefixP{i} ({q},{a}) = none := by decide +kernel']
                i=keys[k];common+=1
                out += [start.rstrip(),
                        f'  apply BB6.Agent32PrefixClosed.checkFrom_sound {B} {cut} {p} {n} prefixZ{i} {t}',
                        f'  · exact BB6.Agent32PrefixClosed.runH_refine_unknown prefixP{i} ({q},{a}) ⟨{w},{d},{j}⟩ prefixU{i} {n} BB6.Agent3PackedCycle.startH prefixZ{i} prefixH{i}',
                        '  · decide +kernel']
                continue
        out.append(start+'apply BB6.Agent32PrefixClosed.fastClosedCheck_sound; decide +kernel')
    return '\n'.join(out)+'\n',count,common,len(keys)

if __name__=='__main__':
    p=Path(sys.argv[1]);branch=sys.argv[2];out=Path(sys.argv[3]) if len(sys.argv)>3 else p
    s,c,n,k=transform(p.read_text(),branch);print(p.name,'checks',c,'shared',n,'groups',k);out.write_text(s)
