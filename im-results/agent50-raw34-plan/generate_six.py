#!/usr/bin/env python3
"""Exhaustive two-level partition with existing FAR and AutoPump witnesses."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path
import json, sys
from generate import CHOICES, STATES, parse, format_table, refine, simulate
from generate_compact import Builder, resolve, emit_child, emit_parent
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'agent48-raw139-f1-oneLA'))
import autopump

class Aggregate:
    def __init__(self, children):
        self.children=children
        self.attainer=max((b.attainer for b in children if b.attainer),key=lambda x:x[1]+1+x[2],default=None)
    def rows(self):return [r for b in self.children for r in b.rows()]

def main():
    ap=ArgumentParser();ap.add_argument('--parent',default='1RB---_1RC---_0RD0RE_1LC0LD_------_------')
    ap.add_argument('--far',default='./far');ap.add_argument('--output',default='generated6');ap.add_argument('--name',default='Raw34D1LD_C1RE')
    ap.add_argument('--cap',type=int,default=200);ap.add_argument('--window',type=int,default=40);ap.add_argument('--long-cap',type=int,default=10000)
    args=ap.parse_args();out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
    p=parse(args.parent);first=simulate(p,args.cap,args.window);assert first[0]=='split';s=first[1]
    groups=[];units=[]
    for i,a in enumerate(CHOICES):
        q=refine(p,s,a);name=f'{args.name}Child{i:02}';c=simulate(q,args.cap,args.window)
        slot=c[1] if c[0]=='split' else None
        tables=[refine(q,slot,x) for x in CHOICES] if slot is not None else [q]
        children=[]
        for j,t in enumerate(tables):
            b=Builder(args.cap,args.window);b.visit(t);n=f'{name}Leaf{j:02}' if slot is not None else name
            unit=(b,t,n);units.append(unit);children.append(unit)
        groups.append((q,name,slot,children))
        print('first child',a,len(children),sum(len(b.pending) for b,_,_ in children),flush=True)
    builders=[b for b,_,_ in units];resolve(builders,args.far,6,args.long_cap)
    cache={}
    for b in builders:
        pending=b.pending;b.pending=[]
        for i,t in pending:
            if t not in cache:
                a=[24 if x in (None,'H') else 4*STATES.index(x[2])+2*int(x[0])+(x[1]=='R') for x in t]
                cache[t]=autopump.find(a,lim=3000)
                print('pump',format_table(t),bool(cache[t]),flush=True)
            if cache[t]:b.close_pump(i,t,cache[t])
            else:b.pending.append((i,t))
    for b,t,_ in units:b.finish(t)
    bound=max(1,max(b.bound for b in builders));print('weighted bound',bound,flush=True)
    for b,t,n in units:emit_child(b,t,n,'BB6.Agent50'+n,bound,out)
    children=[];names=[]
    for q,name,slot,us in groups:
        bs=[b for b,_,_ in us];ns=[n for _,_,n in us]
        if slot is not None:emit_parent(q,slot,bs,ns,['BB6.Agent50'+n for n in ns],bound,out,name)
        children.append(Aggregate(bs));names.append(name)
    emit_parent(p,s,children,names,['BB6.Agent50'+n for n in names],bound,out,args.name)
    info={'parent':format_table(p),'weighted_bound':bound,'nodes':sum(len(b.nodes) for b in builders)+26*(1+sum(slot is not None for _,_,slot,_ in groups)),
          'stats':dict(sum((b.stats for b in builders),Counter())),'mass':dict(sum((b.mass for b in builders),Counter())),
          'children':[{'name':n,'parent':format_table(q),'residuals':a.rows()} for (q,n,_,_),a in zip(groups,children)]}
    if not any(a.rows() for a in children):
        a,n,d=Aggregate(children).attainer;info['attainer']={'table':format_table(a),'ordinary':n+1,'delay':d}
    (out/'summary.json').write_text(json.dumps(info,indent=2)+'\n');print(json.dumps({k:v for k,v in info.items() if k!='children'}),flush=True)
if __name__=='__main__':main()
