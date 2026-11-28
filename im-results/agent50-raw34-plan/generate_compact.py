#!/usr/bin/env python3
"""Untrusted split-proof generator with last-hole compression and FAR leaves."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path
import json,subprocess
from generate import CODES,CHOICES,STATES,parse,format_table,codes,refine,simulate,lean_node
from fastsim import simulate_bits

def max_delay_path(p):
    def dfs(q,seen):
        best=[q]
        for s in range(6):
            if s in seen:continue
            a=p[2*s]
            if a is None or (a not in (None,'H') and a[0]=='0' and STATES.index(a[2])==q):
                cand=dfs(s,seen|{s})+[q]
                if len(cand)>len(best):best=cand
        return best
    return dfs(0,{0})

def fill_attainer(p,path):
    p=list(p)
    for a,b in zip(path,path[1:]):
        if p[2*a] is None:p[2*a]='0R'+STATES[b]
    return tuple('H' if x is None else x for x in p)

class Builder:
    def __init__(self,cap,window):
        self.cap,self.window=cap,window
        self.nodes,self.pending=[],[]
        self.stats=Counter();self.mass=Counter();self.bound=0;self.attainer=None
    def halt(self,p,n):
        path=max_delay_path(p);d=len(path)-1;weight=n+1+d
        if weight>self.bound:self.bound=weight;self.attainer=(fill_attainer(p,path),n,d)
    def visit(self,p,cert=None,i=None):
        if i is None:i=len(self.nodes);self.nodes.append(None)
        if cert is None:cert=simulate(p,self.cap,self.window)
        kind=cert[0]
        if kind=='split':
            s,n=cert[1:]
            if p.count(None)==1 and 'H' not in p:
                self.nodes[i]=('last',s,n)
                self.halt(refine(p,s,'H'),n)
                self.stats['last']+=1;self.mass['last']+=25
            else:
                children=[self.visit(refine(p,s,a)) for a in CHOICES]
                self.nodes[i]=('split',s,children);self.stats['split']+=1
        elif kind=='residual':
            self.nodes[i]=('pending',p);self.pending.append((i,p))
        else:
            self.nodes[i]=cert;self.stats[kind]+=1;self.mass[kind]+=25**p.count(None)
            if kind=='halt':self.halt(p,cert[1])
        return i
    def close_far(self,i,p,c):
        self.nodes[i]=('far',c);self.stats['far']+=1;self.mass['far']+=25**p.count(None)
    def close_pump(self,i,p,c):
        self.nodes[i]=('pump',c);self.stats['pump']+=1;self.mass['pump']+=25**p.count(None)
    def rows(self):
        return [codes(n[1]) for n in self.nodes if n[0]=='pending']
    def finish(self,p):
        self.stats['residual']=len(self.rows());self.mass['residual']=sum(25**r.count(0) for r in self.rows())
        assert sum(self.mass.values())==25**p.count(None)
        assert len(self.nodes)==1+25*self.stats['split']

def far_search(executable,ps,limit):
    if not ps:return {}
    ps=list(dict.fromkeys(ps))
    text=''.join(' '.join(map(str,[i,*codes(p)]))+'\n' for i,p in enumerate(ps))
    completed=subprocess.run([str(Path(executable).resolve()),str(limit)],input=text,text=True,stdout=subprocess.PIPE,check=True)
    data=[json.loads(x) for x in completed.stdout.splitlines()]
    assert len(data)==len(ps)
    return {ps[x['id']]:x for x in data if 'd' in x}

def resolve(builders,far,far_limit,cap2):
    ps=list(dict.fromkeys(p for b in builders for i,p in b.pending))
    print('initial pending',len(ps),flush=True)
    certs=far_search(far,ps,min(4,far_limit))
    print('FAR4',len(certs),flush=True)
    sims={p:simulate_bits(p,cap2) for p in ps if p not in certs}
    print('long simulation',Counter(c[0] for c in sims.values()),flush=True)
    if far_limit>4:
        certs.update(far_search(far,[p for p,c in sims.items() if c[0]=='residual'],far_limit))
    for b in builders:
        pending=b.pending;b.pending=[]
        for i,p in pending:
            if p in certs:b.close_far(i,p,certs[p]);continue
            c=sims[p]
            if c[0]=='residual':b.pending.append((i,p));continue
            b.visit(p,c,i)
    for b in builders:
        pending=b.pending;b.pending=[]
        for i,p in pending:
            if p in certs:b.close_far(i,p,certs[p])
            else:b.pending.append((i,p))

def lean_bits(s):
    return '['+','.join('true' if x=='1' else 'false' for x in s)+']'

def lean_word(w):
    if not w:return '.lit []'
    pre=w[0] if isinstance(w[0],str) else ''
    rest=w[1:] if isinstance(w[0],str) else w
    if not rest:return f'.lit {lean_bits(pre)}'
    x=rest[0];block=x['g'] if isinstance(x,dict) else x.p
    return f'.periodic {lean_bits(pre)} {lean_bits(block)} ({lean_word(rest[1:])})'

def lean_pump(c):
    entry,fam,(ops,_)=c
    q,l,r=fam
    f=f'⟨{q},{lean_word(l)},{lean_word(r)}⟩'
    actions=[];a=b=run=0
    for op in ops:
        if op[0]=='step':run+=1;b+=1;continue
        if run:actions.append(f'List.replicate {run} .step');run=0
        side,_,sp,dp,P,O,k,sr,dr=op[3]
        lp,rp,L,R=(sp,dp,sr,dr) if side=='L' else (dp,sp,dr,sr)
        direction='left' if side=='L' else 'right'
        actions.append(f'[.{direction} {lean_bits(lp)} {lean_bits(rp)} {lean_bits(P)} {lean_bits(O)} ({lean_word(L)}) ({lean_word(R)}) {k}]')
        a+=k
    if run:actions.append(f'List.replicate {run} .step')
    return f'⟨{entry},{f},1,({" ++ ".join(actions) or "[]"}),{a},{b}⟩'

def lean_compact_node(n,rowidx):
    kind,*a=n
    if kind=='pump':return f'.leaf (.pump {lean_pump(a[0])})'
    if kind=='pending':return f'.residual {rowidx[tuple(codes(a[0]))]}'
    if kind=='last':
        s,k=a;return f'.leaf (.last ({s//2},{str(bool(s%2)).lower()}) {k})'
    if kind=='far':
        c=a[0];return f'.leaf (.far {c["d"]} {str(c["reflect"]).lower()} ⟨0,{c["dfa"]},{c["m0"]},{c["m1"]},{c["z"]}⟩)'
    v=lean_node(n)
    return v if kind=='split' else '.leaf (.basic '+v[len('.leaf '):]+')'

def emit_child(b,p,name,ns,bound,out):
    rows=b.rows();rowidx={tuple(r):i for i,r in enumerate(rows)}
    assert len(rowidx)==len(rows)
    fuel=p.count(None)+1
    lines=['import Raw34CompactPlan','set_option maxRecDepth 100000','set_option maxHeartbeats 0',
           f'namespace {ns}', 'open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50Raw34Plan',
           f'/-- {format_table(p)} -/',f'def codes : List Nat := {codes(p)}',
           'def parent : PartialMachine := table codes',f'def rows : List (List Nat) := {rows}',
           'def nodes : Array (PlanNode CompactCert) := #[', ',\n'.join('  '+lean_compact_node(n,rowidx) for n in b.nodes),']',
           f'theorem checked : checkWith nodes rows (compactCheck {bound}) {fuel} 0 parent = true := by decide +kernel',
           f'theorem conditional (hrows : ∀ (j : Nat) (row : List Nat), rows[j]? = some row → Cover (WeightedBound {bound}) (table row)) :',
           f'    Cover (WeightedBound {bound}) parent :=',
           f'  checkWith_sound nodes rows (compactCheck {bound}) (compactCheck_sound {bound}) hrows {fuel} 0 parent checked',
           f'theorem residual_count : rows.length = {len(rows)} := by decide']
    if not rows:
        lines += [f'theorem cover : Cover (WeightedBound {bound}) parent := by',
                  '  apply conditional','  intro j row hj','  simp [rows] at hj','#print axioms cover']
    lines += ['#print axioms conditional','#print axioms residual_count',f'end {ns}','']
    (out/(name+'.lean')).write_text('\n'.join(lines))

def emit_parent(p,slot,children,names,nss,bound,out,name):
    ns='BB6.Agent50'+name
    lines=[*(f'import {n}' for n in names),'set_option maxRecDepth 100000','set_option maxHeartbeats 0',
           f'namespace {ns}','open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50Raw34Plan',
           f'def codes : List Nat := {codes(p)}','def parent : PartialMachine := table codes',
           f'def rows : List (List Nat) := [{", ".join(x+".codes" for x in nss)}]',
           'def nodes : Array (PlanNode CompactCert) := #[',
           f'  .split ({slot//2},{str(bool(slot%2)).lower()}) {list(range(1,26))},',
           ',\n'.join(f'  .residual {i}' for i in range(25)),']',
           f'theorem checked : checkWith nodes rows (compactCheck {bound}) 2 0 parent = true := by decide +kernel',
           f'theorem conditional (hrows : ∀ (j : Nat) (row : List Nat), rows[j]? = some row → Cover (WeightedBound {bound}) (table row)) :',
           f'    Cover (WeightedBound {bound}) parent :=',
           f'  checkWith_sound nodes rows (compactCheck {bound}) (compactCheck_sound {bound}) hrows 2 0 parent checked']
    if all(not b.rows() for b in children):
        lines += [f'theorem cover : Cover (WeightedBound {bound}) parent := by',
                  '  apply conditional','  intro j row hj','  have hm := List.mem_of_getElem? hj',
                  '  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at hm',
                  '  rcases hm with '+' | '.join('rfl' for _ in nss),
                  *(f'  · exact {x}.cover' for x in nss)]
        if any(b.attainer for b in children):
            a,n,d=max((b.attainer for b in children if b.attainer),key=lambda x:x[1]+1+x[2])
            assert n+1+d<=bound
            lines += [f'def attainer : PartialMachine := table {codes(a)}',
                  'def attainerMachine : Machine := fun s => (attainer s).getD none',
                  f'theorem attained : ∃ m, compatible parent m ∧ HaltsAfter m {n} ∧ {d} ∈ delays (zeroNext m) 0 := by',
                  '  have hm : compatible attainer attainerMachine := by','    intro s t ht','    simp [attainerMachine,ht]',
                  '  exact ⟨attainerMachine,extendsTable_sound parent attainer (by decide) _ hm,',
                  f'    finiteHaltCheck_exact attainer {n} (by decide +kernel) _ hm,by decide⟩',
                  '#print axioms attained']
        lines += ['#print axioms cover']
    lines += ['#print axioms conditional',f'end {ns}','']
    (out/(name+'.lean')).write_text('\n'.join(lines))

def extract_subbuilder(b, root, parent_table):
    """Rebase an already-resolved source tree to a fresh local root.

    Every emitted node is copied verbatim, except that its child indices
    are rebased. This avoids rerunning the untrusted FAR/autopump searches
    and permits each subtree to get a separate Lean kernel invocation.
    The original ordinary proof nodes and row certificates are unchanged.
    """
    out=Builder(b.cap,b.window)
    def clone(old):
        i=len(out.nodes)
        out.nodes.append(None)
        node=b.nodes[old]
        if node[0]=='split':
            out.nodes[i]=('split',node[1],[clone(k) for k in node[2]])
        else:out.nodes[i]=node
        return i
    assert clone(root)==0
    assert not out.rows(), 'full source Cover cannot have pending rows'
    if b.attainer is not None:
        a,steps,delay=b.attainer
        if all(x is None or x==y for x,y in zip(parent_table,a)):
            out.attainer=b.attainer
    return out


def emit_heavy_split(b, q, name, bound, out):
    """Split a single heavy RootChild into 25 checkable grandchildren.

    The original outer RootChild module keeps exactly its name and
    Cover statement, now proved by importing its child Covers.
    """
    top=b.nodes[0]
    assert top[0]=='split', (name,top[0])
    _,slot,indices=top
    assert len(indices)==25
    leaves=[];leaf_names=[];leaf_nss=[]
    for i,(action,idx) in enumerate(zip(CHOICES,indices)):
        subq=refine(q,slot,action)
        small=extract_subbuilder(b,idx,subq)
        lname=f'{name}Grand{i:02}'
        ns=f'BB6.Agent50{lname}'
        emit_child(small,subq,lname,ns,bound,out)
        leaves.append(small);leaf_names.append(lname);leaf_nss.append(ns)
    emit_parent(q,slot,leaves,leaf_names,leaf_nss,bound,out,name)


def main():
    ap=ArgumentParser()
    ap.add_argument('--parent',default='1RB---_1RC---_0RD0RE_1LC0LD_---1LB_------')
    ap.add_argument('--cap',type=int,default=200);ap.add_argument('--window',type=int,default=40)
    ap.add_argument('--long-cap',type=int,default=10000);ap.add_argument('--far-limit',type=int,default=6)
    ap.add_argument('--far',default='./far');ap.add_argument('--output',default='generated');ap.add_argument('--name',default='Raw34E1LB')
    ap.add_argument('--split-children',default='',help='comma-separated source child indices 0..24 to emit as 25 smaller source Covers')
    args=ap.parse_args();out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
    p=parse(args.parent);c=simulate(p,args.cap,args.window);assert c[0]=='split';slot=c[1]
    tables=[refine(p,slot,a) for a in CHOICES];builders=[]
    for q in tables:
        b=Builder(args.cap,args.window);b.visit(q);builders.append(b)
    resolve(builders,args.far,args.far_limit,args.long_cap)
    for b,q in zip(builders,tables):b.finish(q)
    bound=max(1,max(b.bound for b in builders))
    names=[f'{args.name}Child{i:02}' for i in range(25)];nss=[f'BB6.Agent50{x}' for x in names]
    heavy={int(i) for i in args.split_children.split(',') if i.strip()}
    assert heavy <= set(range(25)),heavy
    for i,(b,q,name,ns) in enumerate(zip(builders,tables,names,nss)):
        if i in heavy: emit_heavy_split(b,q,name,bound,out)
        else: emit_child(b,q,name,ns,bound,out)
    emit_parent(p,slot,builders,names,nss,bound,out,args.name)
    info={'parent':format_table(p),'split':slot,'weighted_bound':bound,'nodes':sum(len(b.nodes) for b in builders)+26,
          'stats':dict(sum((b.stats for b in builders),Counter())),'mass':dict(sum((b.mass for b in builders),Counter())),
          'children':[{'table':format_table(q),'nodes':len(b.nodes),'bound':b.bound,'residuals':b.rows()} for b,q in zip(builders,tables)]}
    if all(not b.rows() for b in builders):
        a,n,d=max((b.attainer for b in builders if b.attainer),key=lambda x:x[1]+1+x[2]);info['attainer']={'table':format_table(a),'ordinary':n+1,'delay':d}
    (out/'summary.json').write_text(json.dumps(info,indent=2)+'\n');print(json.dumps({k:v for k,v in info.items() if k!='children'}),flush=True)
if __name__=='__main__':main()
