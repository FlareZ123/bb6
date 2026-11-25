"""Discover and emit exact, arbitrary-tail single-period multi-sweep returns.
Python is only candidate generation: every fixed segment is a Lean rfl proof,
every variable segment is an application of SweepPumping.sweepL/R with
a literal arbitrary-tail rfl proof, and every cut rotation is proved.
"""
from dataclasses import dataclass
from itertools import groupby
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parent
SPECS = {
  # code, state, left, right (V=variable repeated block), period, jump, entry, costs
  56: ('1RB0LE_1RC1RA_0RD0LA_1LD1RE_1RF1LC_0RA---','A','','0100001110001110000110011V100001000','1111100001111',1,1946,(0,1773)),
  4710: ('1RB0LE_1RC0RF_0RD0RA_1LD1RE_1LA1LC_1RC---','E','','01'*11+'V','0101',6,179,(48,468)),
  6043: ('1RB0LE_1RC0RA_0RD1LA_1LD1RE_1RF1LC_1RA---','D','0011111111V','','01111',4,27,(80,290)),
  12495: ('1RB1LB_1RC0LF_0RD1RF_1LD1RE_---1LC_0RA0LB','D','0011011111011111'+'0111'*4+'V0','','0111',5,892,(240,2153)),
}

class Machine:
    def __init__(self, code):
        p=code.replace('_','')
        self.a=[p[j:j+3] for j in range(0,36,3)]

@dataclass(frozen=True)
class C:
    q:str
    l:str
    r:str
    p:str
    def concrete(self,n):
        return self.q,self.l.replace('V',self.p*n),self.r.replace('V',self.p*n)

def step(M,q,l,r):
    if l and l[0] not in '01':return
    a=M.a[2*(ord(q)-65)+int(l[0] if l else '0')]
    if a=='---':return
    w,d,q=a
    if d=='R':
        if r and r[0] not in '01':return
        return q,(r[0] if r else '0')+w+l[1:],r[1:]
    return q,l[1:],w+r

def sweep(M,c,maxsteps=100):
    left='V' in c.l
    s,d=(c.l,c.r) if left else (c.r,c.l)
    pre,suf=s.split('V');p=c.p
    for k in range(len(d)+1):
        dp,ds=d[:k],d[k:]
        src=pre+p+'X';dst=dp+'Y';q=c.q;l,r=(src,dst) if left else (dst,src)
        for t in range(1,maxsteps+1):
            a=step(M,q,l,r)
            if a is None:break
            q,l,r=a
            ns,nd=(l,r) if left else (r,l)
            if q==c.q and ns==pre+'X' and nd.startswith(dp) and nd.endswith('Y') and len(nd)==len(dp)+len(p)+1:
                out=nd[k:-1]
                if set(out)<=set('01'):
                    ns=pre+suf;nd=dp+'V'+ds
                    return t,C(q,*((ns,nd) if left else (nd,ns)),out),(left,pre,dp,suf,ds,p,out)

def rotations(c):
    left='V' in c.l;s=c.l if left else c.r
    pre,suf=s.split('V');p=c.p
    if pre and pre[-1]==p[-1]:
        b=pre[-1];ns=pre[:-1]+'V'+b+suf;np=b+p[:-1]
        yield C(c.q,ns if left else c.l,c.r if left else ns,np),('rotL',left,pre[:-1],b,p[:-1],suf)
    if suf and suf[0]==p[0]:
        b=suf[0];ns=pre+b+'V'+suf[1:];np=p[1:]+b
        yield C(c.q,ns if left else c.l,c.r if left else ns,np),('rotR',left,pre,b,p[1:],suf[1:])

def equivalents(c):
    seen={c};queue=[(c,[])]
    while queue:
        u,path=queue.pop(0);yield u,path
        for v,info in rotations(u):
            if v not in seen:seen.add(v);queue.append((v,path+[(v,info)]))

def find(M,start,target,maxsteps=20000,max_fixed=None):
    c=start;ops=[];time=[0,0];seen=set()
    for i in range(maxsteps):
        if i and c.concrete(0)==target.concrete(0) and c.concrete(1)==target.concrete(1):
            for v,path in equivalents(c):
                if v==target:
                    for v,info in path:ops.append(('rotate',c,v,info));c=v
                    return ops,time
        if max_fixed is not None and time[1]>max_fixed:return
        if c in seen:return
        seen.add(c);found=None
        for v,path in equivalents(c):
            a=sweep(M,v)
            if a is not None:found=(v,path,a);break
        if found:
            v,path,(t,w,info)=found
            for v0,info0 in path:ops.append(('rotate',c,v0,info0));c=v0
            ops.append(('sweep',v,w,(t,info)));c=w;time[0]+=t
            continue
        for v,path in equivalents(c):
            a=step(M,v.q,v.l,v.r)
            if a is not None:
                for v0,info0 in path:ops.append(('rotate',c,v0,info0));c=v0
                w=C(*a,v.p);ops.append(('step',v,w,1));c=w;time[1]+=1;break
        else:return

def w(s):
    return '['+','.join('true' if x=='1' else 'false' for x in s)+']'
def word(s,p):
    if 'V' not in s:return w(s)
    a,b=s.split('V');return f'({w(a)} ++ (rep {w(p)} n ++ {w(b)}))'
def cfg(c):
    return f'⟨{ord(c.q)-65},{word(c.l,c.p)},{word(c.r,c.p)}⟩'
def make_table(M):
    out=['def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
    for i,a in enumerate(M.a):
        if a=='---':continue
        b,r,q=a;out.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(b=="1").lower()},{str(r=="R").lower()},{ord(q)-65}⟩)')
    return '\n'.join(out+['  | _,_ => none'])
def compress(ops):
    for k,g in groupby(ops,key=lambda x:x[0]=='step'):
        g=list(g)
        if k:yield 'fixed',g[0][1],g[-1][2],len(g)
        else:yield from g

def gen(i,M,start,target,entry,jump):
    namespace=f'BB6.Agent8Raw112MultiSweep.M{i}'
    answer=find(M,start,target)
    assert answer is not None,i
    ops,time=answer
    assert ops[-1][2]==target
    lines=['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 1000000',f'namespace {namespace}','open BB6Coverage BB6Coverage.Agent31Pump','',make_table(M),'',f'def family (n : Nat) : Z0 := {cfg(start)}',f'theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl','',f'theorem epoch (n : Nat) : run0 table ({time[0]}*n+{time[1]}) (family n) = some (family (n+{jump})) := by']
    times=[];cur=None
    for j,(k,c,d,info) in enumerate(compress(ops)):
        if k=='fixed':
            cost=str(info);proof='by rfl'
        elif k=='sweep':
            t,(left,pre,dp,suf,ds,p,out)=info
            lp,rp=(pre,dp) if left else (dp,pre);L,R=(suf,ds) if left else (ds,suf);q=ord(c.q)-65
            cost=f'({t}*n)';proof=f'by\n    exact sweep{"L" if left else "R"} table {q} {w(lp)} {w(rp)} {w(p)} {w(out)} {t} (fun _ _ => rfl) n {w(L)} {w(R)}'
        elif k=='rotate':
            typ,left,pre,b,p,suf=info
            arg=f'moveCut {w(pre)} {w(suf)} {w(p)} {str(b=="1").lower()} n'
            if typ=='rotR':arg=f'({arg}).symm'
            q=ord(c.q)-65
            f=f'fun x => (⟨{q},x,{w(c.r)}⟩ : Z0)' if left else f'fun x => (⟨{q},{w(c.l)},x⟩ : Z0)'
            lines += [f'  have e{j} : ({cfg(c)} : Z0) = {cfg(d)} := congrArg ({f}) ({arg})']
            if cur is None:
                lines += [f'  have h{j} : run0 table 0 {cfg(c)} = some {cfg(d)} := by rw [e{j}]; rfl'];cost='0'
            else:
                lines += [f'  rw [e{j}] at {cur}'];continue
        else:raise ValueError(k)
        if k!='rotate':lines += [f'  have h{j} : run0 table {cost} {cfg(c)} = some {cfg(d)} := {proof}']
        times.append(cost)
        if cur is None:cur=f'h{j}'
        else:lines += [f'  have g{j} := join0 {cur} h{j}'];cur=f'g{j}'
    a,b=time
    lines += [f'  rw [show {"+".join(times)}={a}*n+{b} by omega] at {cur}',f'  exact {cur}', '',f'def orbit (n : Nat) := family ({jump}*n)',f'theorem orbit_entry : run0 table {entry} ⟨0,[],[]⟩ = some (orbit 0) := entry',f'theorem growth (n : Nat) : run0 table ({a}*({jump}*n)+{b}) (orbit n) = some (orbit (n+1)) := by',f'  have h := epoch ({jump}*n)',f'  rw [show {jump}*n+{jump}={jump}*(n+1) by omega] at h',f'  exact h','',f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',f'  never_of_growth table orbit {entry} (fun n => {a}*({jump}*n)+{b}) orbit_entry (by intro n; omega) growth m hm','','#print axioms epoch','#print axioms growth','#print axioms never',f'end {namespace}']
    return '\n'.join(lines)+'\n',tuple(time)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('ids',type=int,nargs='*')
    ap.add_argument('--out',type=Path,default=ROOT/'raw112')
    args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    for i in args.ids or SPECS:
        code,q,l,r,p,jump,entry,costs=SPECS[i]
        st=C(q,l,r,p);tg=C(q,l.replace('V',p*jump+'V'),r.replace('V',p*jump+'V'),p)
        source,time=gen(i,Machine(code),st,tg,entry,jump)
        assert time==costs,(i,time,costs)
        (args.out/f'Raw112MultiSweep{i}.lean').write_text(source)
        print(i,'epoch costs',time,'jump',jump,'entry',entry)

if __name__=='__main__':main()
