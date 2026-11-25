"""Generate the three shared, independently kernel-checked raw108 #1930 traces."""
from pathlib import Path
import sys
P=(0,1,1);Q=(1,0,1);R=(1,1,0);Z=(0,0,0)
BASE='1RB---_1RC0LB_0RD---_1LD1RE_0RF1LB_1RA0LB'.replace('_','')

def seg(p,n,t): return (p,n,t) if n else t
def pop(t):
    if not t: return None
    p,n,r=t
    if not n: return pop(r)
    return p[0],seg(p[1:]+p[:1],n-1,r)
def popd(t): return pop(t) or (0,None)
def push(b,t):
    if t:
        p,n,r=t
        if n==1: return ((b,p[0],0),2,r)
        if n==2: return ((b,p[0],p[1]),3,r)
        if n>=3 and b==p[2]: return ((b,p[0],p[1]),n+1,r)
    return ((b,0,0),1,t)
def pop3(t):
    a=[]
    for _ in range(3):
        v=pop(t)
        if not v: return None
        b,t=v
        a.append(b)
    return tuple(a),t
def strip(p,t):
    n=0
    for _ in range(1024):
        if not t: break
        q,k,r=t
        if q==p and k>=3:
            n+=k//3
            t=seg(p,k%3,r)
            continue
        v=pop3(t)
        if v and v[0]==p:
            n+=1
            t=v[1]
            continue
        break
    return n,t
def machine(v):
    s=BASE[:3]+v+BASE[6:]
    return [s[i:i+3] for i in range(0,36,3)]
def step(tr,c):
    q,l,r=c
    b,u=popd(l)
    a,v=popd(r)
    mv=tr[2*q+b]
    if mv=='---': return None
    w,d,z=mv
    w=int(w);z=ord(z)-65
    return (z,push(a,push(w,u)),v) if d=='R' else (z,u,push(w,r))
def macro(tr,c):
    q,l,r=c
    if q==1:
        v=pop3(r)
        if v and v[0]==Z:
            n,u=strip(P,l)
            if n: return 9*n,(1,u,(Z,3,(R,3*n,v[1])))
    elif q==2:
        v=pop(l)
        if v and v[0]==0:
            n,u=strip(Q,r)
            if n: return 5*n,(2,push(0,(R,3*n,v[1])),u)
    d=step(tr,c)
    return (1,d) if d else None
def common(c):
    tr=machine('---')
    t=i=0
    out=[(0,c)]
    while m:=macro(tr,c):
        k,c=m
        t+=k;i+=1
        if i%512==0: out.append((t,c))
    if out[-1][0]!=t: out.append((t,c))
    return out
def patched(c):
    results=[]
    for v,ns in [('0LB',2),('0LF',2),('1RE',4)]:
        x=c
        for _ in range(ns): x=step(machine(v),x)
        results.append(x)
    assert results[0]==results[1]==results[2]
    return results[0]
def segments():
    a=common((0,None,None))
    b=common(patched(a[-1][1]))
    c=common(patched(b[-1][1]))
    assert [p[-1][0] for p in [a,b,c]]==[91502,999449,3045215]
    assert [(p[-1][1][0],popd(p[-1][1][1])[0]) for p in [a,b,c]]==[(0,1),(0,1),(2,1)]
    return a,b,c
def lit(t):
    if not t: return '.nil'
    p,n,r=t
    return f'.run ⟨{str(bool(p[0])).lower()},{str(bool(p[1])).lower()},{str(bool(p[2])).lower()}⟩ {n} ({lit(r)})'
def cfg(c): return f'⟨{c[0]}, {lit(c[1])}, {lit(c[2])}⟩'
def generate(out,imp='Raw108CompressedTrace'):
    out=Path(out);out.mkdir(exist_ok=True)
    a,b,c=segments()
    pre='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent10Raw108Long\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent10CompressedTape\n'
    post='\nend BB6.Agent10Raw108Long\n'
    def write(name,imports,body):
        (out/(name+'.lean')).write_text(''.join(f'import {x}\n' for x in imports)+pre+'\n'.join(body)+post)
    for name,trace in [('A',a),('B',b),('C',c)]:
        write(f'Raw108Long{name}Data',[imp],[f'def {name}{i} : Cfg := {cfg(z)}' for i,(t,z) in enumerate(trace)])
        shards=[]
        for start in range(0,len(trace)-1,4):
            end=min(start+4,len(trace)-1);ls=[]
            for i in range(start,end):
                n=trace[i+1][0]-trace[i][0]
                ls.append(f'theorem {name}step{i} : run0 (table none) {n} (pr {name}{i}) = some (pr {name}{i+1}) :=\n  fastRun_sound none 512 {n} {name}{i} {name}{i+1} (by decide +kernel)')
            mod=f'Raw108Long{name}Shard{start//4}'
            shards.append(mod);write(mod,[f'Raw108Long{name}Data'],ls)
        def combine(lo,hi):
            if hi-lo==1: return f'{name}step{lo}'
            m=(lo+hi)//2
            n=trace[m][0]-trace[lo][0];k=trace[hi][0]-trace[m][0]
            return f'(joinN (p := table none) (n := {n}) (k := {k}) (t := {n+k}) (a := pr {name}{lo}) (b := pr {name}{m}) (c := pr {name}{hi}) (by decide) {combine(lo,m)} {combine(m,hi)})'
        write(f'Raw108Long{name}',shards,[f'theorem segment{name} : run0 (table none) {trace[-1][0]} (pr {name}0) = some (pr {name}{len(trace)-1}) := {combine(0,len(trace)-1)}'])
    ls=[]
    for v,expr,n in [('kid1','some (some ⟨false,false,1⟩)',2),('kid5','some (some ⟨false,false,5⟩)',2),('kid22','some (some ⟨true,true,4⟩)',4)]:
        ls.append(f'def {v} : Option (Option Move) := {expr}')
        ls.append(f'theorem patchA_{v} : run0 (table {v}) {n} (pr A{len(a)-1}) = some (pr B0) := fastRun_sound {v} {n} {n} A{len(a)-1} B0 (by decide +kernel)')
        ls.append(f'theorem patchB_{v} : run0 (table {v}) {n} (pr B{len(b)-1}) = some (pr C0) := fastRun_sound {v} {n} {n} B{len(b)-1} C0 (by decide +kernel)')
        blocks=[(a[-1][0],f'run_refine {v} {a[-1][0]} (pr A0) (pr A{len(a)-1}) segmentA','A0',f'A{len(a)-1}'),(n,f'patchA_{v}',f'A{len(a)-1}','B0'),(b[-1][0],f'run_refine {v} {b[-1][0]} (pr B0) (pr B{len(b)-1}) segmentB','B0',f'B{len(b)-1}'),(n,f'patchB_{v}',f'B{len(b)-1}','C0'),(c[-1][0],f'run_refine {v} {c[-1][0]} (pr C0) (pr C{len(c)-1}) segmentC','C0',f'C{len(c)-1}')]
        t,proof,start,end=blocks[0]
        for k,h,u,w in blocks[1:]:
            assert end==u
            proof=f'joinN (p := table {v}) (n := {t}) (k := {k}) (t := {t+k}) (a := pr {start}) (b := pr {u}) (c := pr {w}) (by decide) ({proof}) ({h})'
            t+=k;end=w
        ls.append(f'theorem full_{v} : run0 (table {v}) {t} (pr {start}) = some (pr {end}) :=\n  {proof}')
        ls.append(f'#print axioms full_{v}')
    write('Raw108LongProof',['Raw108LongA','Raw108LongB','Raw108LongC'],ls)

if __name__=='__main__':
    generate(sys.argv[1] if len(sys.argv)>1 else Path(__file__).resolve().parent)
