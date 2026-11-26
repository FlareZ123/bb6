#!/usr/bin/env python3
"""Replay exact RF affine families with arbitrary-tail sweeps, then emit Lean.
A block may change length during a sweep; the original SweepPumping theorem
already supports unequal input/output block lengths.
"""
from pathlib import Path
import tempfile
from la_multivar import C, var, pat, newpat, equivalents, signature, gen, Machine, step
from generate_rf_witnesses import ROOT,census

def sweeps(M,c,maxsteps=100):
    for left in (True,False):
        s,d=(c.l,c.r) if left else (c.r,c.l)
        k=next((i for i,x in enumerate(s) if var(x)),None)
        if k is None:continue
        pre,v,suf=s[:k],s[k],s[k+1:];p=pat(c,v)
        dk=next((i for i,x in enumerate(d) if var(x)),len(d))
        for i in range(dk+1):
            dp,ds=d[:i],d[i:];src=pre+p+'X';dst=dp+'Y';q=c.q;l,r=(src,dst) if left else (dst,src)
            for t in range(1,maxsteps+1):
                a=step(M,q,l,r)
                if a is None:break
                q,l,r=a;ns,nd=(l,r) if left else (r,l)
                if q==c.q and ns==pre+'X' and nd.startswith(dp) and nd.endswith('Y'):
                    out=nd[i:-1]
                    if out and set(out)<=set('01') and len(out)<=64:
                        ns=pre+suf;nd=dp+v+ds
                        yield t,C(q,*((ns,nd) if left else (nd,ns)),newpat(c,v,out)),(left,pre,dp,suf,ds,p,out)
                        break

def replay(M,start,target,a,b):
    c=start;ops=[];cost=[0,0];seen=set()
    want0=target.concrete(0);want1=target.concrete(1);sig=signature(target)
    for i in range(1000):
        if cost[1]>b or cost[0]>a:return
        eqs=list(equivalents(c,limit=64))
        if i and tuple(cost)==(a,b) and c.concrete(0)==want0 and c.concrete(1)==want1:
            for v,path in eqs:
                if signature(v)==sig:
                    for v,info in path:ops.append(('rotate',c,v,info));c=v
                    return ops,tuple(cost)
        if c in seen:return
        seen.add(c);found=None
        for v,path in eqs:
            x=next(sweeps(M,v),None)
            if x is not None:found=(v,path,x);break
        if found:
            v,path,(t,d,info)=found
            for v0,info0 in path:ops.append(('rotate',c,v0,info0));c=v0
            ops.append(('sweep',v,d,(t,info)));c=d;cost[0]+=t;continue
        for v,path in eqs:
            x=step(M,v.q,v.l,v.r)
            if x is not None:
                for v0,info0 in path:ops.append(('rotate',c,v0,info0));c=v0
                d=C(*x,v.ps);ops.append(('step',v,d,1));c=d;cost[1]+=1;break
        else:return

def emit_growth(rows,root=ROOT):
    for line in (ROOT/'rf-growth.txt').read_text().splitlines():
        i,entry,q,l,r,ps,tl,tr,a,b=line.split()
        i,entry,a,b=map(int,(i,entry,a,b))
        l,r,tl,tr=map(lambda s:'' if s=='-' else s,(l,r,tl,tr))
        ps=tuple(ps.split(','));st=C(q,l,r,ps);tg=C(q,tl,tr,ps);M=Machine(rows[i])
        ans=replay(M,st,tg,a,b)
        assert ans is not None and ans[1]==(a,b),i
        source=gen(i,M,st,tg,entry,ans).replace('BB6.Agent8Raw54.LA.','BB6.Agent8Raw54.RF.').replace('maxHeartbeats 1000000','maxHeartbeats 0')
        (root/f'Raw54RFGrow{i}.lean').write_text(source)

if __name__=='__main__':
    with tempfile.TemporaryDirectory() as d:emit_growth(census(Path(d)))
