#!/usr/bin/env python3
"""Graft all 45 exact extension roots onto the original Agent48 partition.
No search and no acceptance claim: the output still needs Lean source checking.
Usage: graft_oneLA.py partition.json spec-compact.json extension.json.zlib.b64 OUTDIR
"""
import base64, collections, json, pathlib, sys, zlib
ORDER=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
PARENT=[7,24,11,24,14,24,24,16,2,11,24,24]

def graft(part,spec,ext):
    assert part['counts']==spec['counts'] and spec['parent']==PARENT
    old=part['open']; assert len(old)==len({tuple(t) for t in old})
    covered={int(i) for i in spec['late']} | {int(i) for i in spec['proven']} | {i for _,g in spec['block_groups'] for i in g}
    roots={int(k) for k in ext if '_' not in k}
    assert roots == set(range(len(old)))-covered and len(roots)==45
    new=[]; idx={}; used=set(); extra_proven={}; imports=set(spec['external_imports'])
    def add(t):
        key=tuple(t); assert key not in idx, ('duplicate open',t)
        idx[key]=len(new); new.append(t); return idx[key]
    remap={i:add(t) for i,t in enumerate(old) if i not in roots}
    root_by_table={tuple(old[i]):str(i) for i in roots}
    def proven(k,t,ns,module):
        i=add(t); extra_proven[str(i)]=ns; imports.add(module); return ['open',t]
    def expand(k,t):
        assert k not in used and ext[k][0]==t, (k,t)
        used.add(k); typ,*a=ext[k][1]
        if k=='11147':
            assert typ=='cycle'; return proven(k,t,'BB6.Agent48OneLALongCycle','OneLALongCycle')
        if typ=='split':
            n,s=a; assert t[s]==24
            children=[]
            for v in ORDER:
                tt=t.copy(); tt[s]=v; children.append(expand(f'{k}_{v}',tt))
            return ['split',n,s,children]
        if typ in ('cycle','last','far'): return [typ,*a]
        if typ=='wide':
            w=a[0]
            if w==2:
                return proven(k,t,'BB6.Agent48Raw139E0OneLAExtensionBlocks.R'+k,'OneLAExtBlock'+k)
            assert w in (5,6)
            return proven(k,t,f'BB6.Agent48Wide{w}.OneLAWide{k}','OneLAWide'+k+'Proof')
        assert typ=='open' and k in ('8938','9138','9162')
        return proven(k,t,'BB6.Agent48Raw139E0OneLASweeps.Sweep'+k,'Sweep8938Bridge' if k=='8938' else 'OneLAGrowth')
    visited=set(); c=collections.Counter(); maxquery=0
    def walk(n,t):
        if n[0]=='open':
            assert n[1]==t
            key=tuple(t); assert key not in visited; visited.add(key)
            if key in root_by_table: return walk_new(expand(root_by_table[key],t))
        if n[0]=='split':
            _,steps,s,kids=n; assert t[s]==24 and len(kids)==24
            out=[]
            for v,kid in zip(ORDER,kids):
                tt=t.copy(); tt[s]=v; out.append(walk(kid,tt))
            n=['split',steps,s,out]
        count(n); return n
    def count(n):
        nonlocal maxquery
        c[n[0]]+=1
        if n[0] in ('split','last'): maxquery=max(maxquery,n[1])
    def walk_new(n):
        count(n)
        if n[0]=='split':
            for k in n[3]: walk_new(k)
        return n
    tree=walk(part['tree'],PARENT)
    assert visited=={tuple(t) for t in old} and used==set(ext)
    assert c['open']==len(new) and sum(c.values())-c['split']==1+23*c['split']
    c['maxquery']=maxquery
    assert maxquery+6<=spec['bound']
    spec=dict(spec); spec['counts']=dict(c)
    spec['block_groups']=[[p,[remap[i] for i in g]] for p,g in spec['block_groups']]
    spec['late']={str(remap[int(i)]):a for i,a in spec['late'].items()}
    spec['proven']={str(remap[int(i)]):a for i,a in spec['proven'].items()}|extra_proven
    spec['external_imports']=sorted(imports)
    allids=[i for _,g in spec['block_groups'] for i in g]+list(map(int,spec['late']))+list(map(int,spec['proven']))
    assert sorted(allids)==list(range(len(new)))
    return {'tree':tree,'open':new,'counts':dict(c)},spec

if __name__=='__main__':
    a,b,c,d=map(pathlib.Path,sys.argv[1:]); d.mkdir(parents=True,exist_ok=True)
    ext=json.loads(zlib.decompress(base64.b64decode(c.read_text())))
    p,s=graft(json.loads(a.read_text()),json.loads(b.read_text()),ext)
    for n,o in [('partition.json',p),('spec-compact.json',s)]:
        (d/n).write_text(json.dumps(o,separators=(',',':'))+'\n')
    print('GRAFT',p['counts'],'bound',s['bound'],'imports',s['external_imports'])
