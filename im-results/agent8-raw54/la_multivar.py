"""Generate exact multi-block growth proofs. Discovery choices are untrusted;
Lean checks every primitive computation, arbitrary-tail sweep and rotation.
"""
from dataclasses import dataclass
from itertools import groupby
from collections import deque
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'agent8-tnf-raw117'))
from raw112_multisweep import Machine,step,w,make_table
import time

@dataclass(frozen=True)
class C:
    q:str
    l:str
    r:str
    ps:tuple
    def concrete(self,n):
        def f(s):return ''.join(x if x in '01' else self.ps[ord(x)-65]*n for x in s)
        return self.q,f(self.l),f(self.r)

def var(x):return x not in '01'
def pat(c,v):return c.ps[ord(v)-65]
def newpat(c,v,p):
    a=list(c.ps);a[ord(v)-65]=p;return tuple(a)

def sweeps(M,c,maxsteps=120):
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
                    if out and set(out)<=set('01') and len(out)==len(p):
                        ns=pre+suf;nd=dp+v+ds
                        yield t,C(q,*((ns,nd) if left else (nd,ns)),newpat(c,v,out)),(left,pre,dp,suf,ds,p,out)
                        break

def rotations(c):
    for left in (True,False):
        s=c.l if left else c.r
        for k,v in enumerate(s):
            if not var(v):continue
            pre,suf=s[:k],s[k+1:];p=pat(c,v)
            if pre and pre[-1]==p[-1]:
                b=pre[-1];ns=pre[:-1]+v+b+suf;np=b+p[:-1]
                yield C(c.q,ns if left else c.l,c.r if left else ns,newpat(c,v,np)),('rotL',left,pre[:-1],b,p[:-1],suf)
            if suf and suf[0]==p[0]:
                b=suf[0];ns=pre+b+v+suf[1:];np=p[1:]+b
                yield C(c.q,ns if left else c.l,c.r if left else ns,newpat(c,v,np)),('rotR',left,pre,b,p[1:],suf[1:])

def equivalents(c,limit=128):
    seen={c};queue=deque([(c,[])])
    while queue:
        u,path=queue.popleft();yield u,path
        for v,info in rotations(u):
            if v not in seen and len(seen)<limit:seen.add(v);queue.append((v,path+[(v,info)]))

def signature(c):
    def f(s):
        return tuple((x,) if x in '01' else ('rep',pat(c,x)) for x in s)
    return c.q,f(c.l),f(c.r)

def find(M,start,target,maxsteps=1000,max_fixed=1000,seconds=10):
    c=start;ops=[];cost=[0,0];seen=set();clock=time.monotonic()
    for i in range(maxsteps):
        if time.monotonic()-clock>seconds:return
        eqs=list(equivalents(c))
        if i and c.concrete(0)==target.concrete(0) and c.concrete(1)==target.concrete(1) and c.concrete(2)==target.concrete(2):
            for v,path in eqs:
                if signature(v)==signature(target):
                    for v,info in path:ops.append(('rotate',c,v,info));c=v
                    return ops,tuple(cost)
        if cost[1]>max_fixed or c in seen:return
        seen.add(c);found=None
        for v,path in eqs:
            a=next(sweeps(M,v),None)
            if a is not None:found=(v,path,a);break
        if found:
            v,path,(t,d,info)=found
            for v0,info0 in path:ops.append(('rotate',c,v0,info0));c=v0
            ops.append(('sweep',v,d,(t,info)));c=d;cost[0]+=t;continue
        for v,path in eqs:
            a=step(M,v.q,v.l,v.r)
            if a is not None:
                for v0,info0 in path:ops.append(('rotate',c,v0,info0));c=v0
                d=C(*a,v.ps);ops.append(('step',v,d,1));c=d;cost[1]+=1;break
        else:return

def word(s,c):
    parts=[];bits=''
    for x in s:
        if x in '01':bits+=x;continue
        if bits:parts.append(w(bits));bits=''
        parts.append(f'(rep {w(pat(c,x))} n)')
    if bits:parts.append(w(bits))
    if not parts:return '[]'
    if len(parts)==1:return parts[0]
    return '('+' ++ ('.join(parts)+')'*len(parts)

def cfg(c):return f'⟨{ord(c.q)-65},{word(c.l,c)},{word(c.r,c)}⟩'

def compress(ops):
    for k,g in groupby(ops,key=lambda x:x[0]=='step'):
        g=list(g)
        if k:yield 'fixed',g[0][1],g[-1][2],len(g)
        else:yield from g

def gen(id,M,start,target,entry,ans):
    ns=f'BB6.Agent8Raw54.LA.M{id}';ops,costs=ans;a,b=costs
    out=['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 1000000',f'namespace {ns}','open BB6Coverage BB6Coverage.Agent31Pump','',make_table(M),'',f'def family (n : Nat) : Z0 := {cfg(start)}',f'theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl','',f'theorem epoch (n : Nat) : run0 table ({a}*n+{b}) (family n) = some (family (n+1)) := by']
    times=[];cur=None
    for j,(k,c,d,info) in enumerate(compress(ops)):
        if k=='fixed':cost=str(info);proof='by rfl'
        elif k=='sweep':
            t,(left,pre,dp,suf,ds,p,o)=info
            lp,rp=(pre,dp) if left else (dp,pre);L,R=(suf,ds) if left else (ds,suf);q=ord(c.q)-65
            cost=f'({t}*n)';proof=f'by\n    simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using sweep{"L" if left else "R"} table {q} {w(lp)} {w(rp)} {w(p)} {w(o)} {t} (fun _ _ => rfl) n {word(L,c)} {word(R,c)}'
        elif k=='rotate':
            typ,left,pre,bit,p,suf=info
            arg=f'moveCut {word(pre,c)} {word(suf,c)} {w(p)} {str(bit=="1").lower()} n'
            if typ=='rotR':arg=f'({arg}).symm'
            q=ord(c.q)-65;f=f'fun x => (⟨{q},x,{word(c.r,c)}⟩ : Z0)' if left else f'fun x => (⟨{q},{word(c.l,c)},x⟩ : Z0)'
            out += [f'  have e{j} : ({cfg(c)} : Z0) = {cfg(d)} := by',f'    simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using congrArg ({f}) ({arg})']
            if cur is None:out += [f'  have h{j} : run0 table 0 {cfg(c)} = some {cfg(d)} := by rw [e{j}]; rfl'];cost='0'
            else:out += [f'  rw [e{j}] at {cur}'];continue
        else:raise ValueError(k)
        if k!='rotate':out += [f'  have h{j} : run0 table {cost} {cfg(c)} = some {cfg(d)} := {proof}']
        times.append(cost)
        if cur is None:cur=f'h{j}'
        else:out += [f'  have g{j} := join0 {cur} h{j}'];cur=f'g{j}'
    out += [f'  rw [show {"+".join(times)}={a}*n+{b} by omega] at {cur}',f'  have htarget : ({cfg(target)} : Z0) = family (n+1) := by', '    simp only [family,rep,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] <;> rfl','  rw [htarget] at '+cur,'  exact '+cur,'',f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',f'  never_of_growth table family {entry} (fun n => {a}*n+{b}) entry (by intro n; omega) epoch m hm','','#print axioms never',f'end {ns}']
    return '\n'.join(out)+'\n'

# id, entry, q, left, right, patterns, target-left, target-right, exact epoch costs
SPECS=[
(26,59,'C','10A1010B110101','',('101','1'),'10101A10101B110101','',(14,44)),
(45,17,'B','1AB10001','',('00','1000'),'100A1000B10001','',(24,40)),
(38,22,'E','','011A010B1',('1','0'),'','0111A0100B1',(4,20)),
(42,17,'E','','01A010B1',('1','0'),'','011A0100B1',(4,14)),
(83,13,'F','10A1001B','',('00','1'),'1000A10011B','',(12,25)),
(84,13,'F','10A1001B','',('00','1'),'1000A10011B','',(10,23)),
(95,18,'F','0A1001B01','',('00','1'),'000A10011B01','',(4,13)),
(99,79,'E','','00000A100010B1',('0','0'),'','000000A1000100B1',(4,34)),
(100,79,'E','','00000A100010B1',('0','0'),'','000000A1000100B1',(4,34)),
(40,23,'D','101011A','',('11',),'10101111A','',(42,77)),
(44,21,'D','101011A','',('11',),'10101111A','',(36,65)),
(93,2,'C','0A11','',('000000',),'0000000A11','',(24,26)),
(151,8,'A','','1A0011',('1111111111',),'','11111111111A0011',(40,56)),
]
def emit_multi(misses,root):
    for i,entry,q,l,r,ps,tl,tr,cost in SPECS:
        M=Machine(misses[i]);st=C(q,l,r,ps);tg=C(q,tl,tr,ps)
        ans=find(M,st,tg)
        assert ans is not None and ans[1]==cost,(i,ans)
        (root/f'Raw54LAMulti{i}.lean').write_text(gen(i,M,st,tg,entry,ans))
if __name__=='__main__':
    from generate_la_witnesses import enumerate_misses,ROOT
    import tempfile
    with tempfile.TemporaryDirectory() as d:emit_multi(enumerate_misses(Path(d)),ROOT)
