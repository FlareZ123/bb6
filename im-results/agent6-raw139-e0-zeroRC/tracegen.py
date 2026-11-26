"""Generate proof-producing accelerated trace for E0=0RC open index 5144.

Uses existing Raw59PackedQuery/Raw59PackedMacro and PartialAudit (Agent32).
Run this generator, then compile the Lean files with those dependencies.
Each sweep is checked by an arbitrary-tail rfl proof and the exact state
sequence is checked in bounded chunks using the kernel, not native_decide.
"""
from pathlib import Path
P=[7,23,11,7,14,1,6,16,9,11,24,19]
OUT=Path(__file__).resolve().parent/'generated'
def push(x,b): return (x[0]+1,2*x[1]+b)
def head(x): return (x[1]&1) if x[0] else 0
def tail(x): return (max(0,x[0]-1),x[1]>>1)
def step(z):
    q,l,r=z;v=P[2*q+head(l)]
    if v==24:return None
    w=v>>1&1
    return (v>>2,push(push(tail(l),w),head(r)),tail(r)) if v&1 else (v>>2,tail(l),push(r,w))
def bits(x,n):return x[1]&((1<<n)-1)
def drop(x,n):return (x[0]-n,x[1]>>n)
def concat(a,b):return (a[0]+b[0],a[1]|(b[1]<<a[0]))
def repeat(x,n):
    k,b=x
    return (k*n,b*((1<<(k*n))-1)//((1<<k)-1)) if k else (0,0)
def starts(x,y):return x[0]>=y[0] and bits(x,y[0])==y[1]
def motif(z):
    q,l,r=z;u=z;h=0;lo=hi=0;best=None
    for k in range(1,33):
        v=P[2*u[0]+head(u[1])]
        if v==24:break
        h+=1 if v&1 else -1;lo=min(lo,h);hi=max(hi,h);u=step(u)
        if u[0]!=q or not h:continue
        if h>0:
            a=1-lo;b=max(0,hi-h);d=h
            if l[0]<a or r[0]<b+d:continue
            lp=(a,bits(l,a));rp=(b,bits(r,b));I=(d,bits(drop(r,b),d));O=(d,bits(drop(u[1],a),d))
            if not starts(u[1],lp) or not starts(u[2],rp):continue
            if drop(u[1],a+d)!=drop(l,a) or drop(u[2],b)!=drop(r,b+d):continue
            x=drop(r,b)
        else:
            d=-h;a=max(1,1-lo-d);b=hi
            if l[0]<a+d or r[0]<b:continue
            lp=(a,bits(l,a));rp=(b,bits(r,b));I=(d,bits(drop(l,a),d));O=(d,bits(drop(u[2],b),d))
            if not starts(u[1],lp) or not starts(u[2],rp):continue
            if drop(u[1],a)!=drop(l,a+d) or drop(u[2],b+d)!=drop(r,b):continue
            x=drop(l,a)
        l0=lp if h>0 else concat(lp,I);r0=concat(rp,I) if h>0 else rp
        w=(q,l0,r0);safe=True
        for _ in range(k):
            if not w[1][0]:safe=False;break
            v=P[2*w[0]+head(w[1])]
            if v==24 or (v&1 and not w[2][0]):safe=False;break
            w=step(w)
        want=(q,concat(lp,O),rp) if h>0 else (q,lp,concat(rp,O))
        if not safe or w!=want:continue
        low=0;high=x[0]//d+1
        while high-low>1:
            mid=(low+high)//2
            if starts(x,repeat(I,mid)):low=mid
            else:high=mid
        n=low
        if n<3:continue
        if h>0:out=(q,concat(concat(lp,repeat(O,n)),drop(l,a)),concat(rp,drop(r,b+d*n)))
        else:out=(q,concat(lp,drop(l,a+d*n)),concat(concat(rp,repeat(O,n)),drop(r,b)))
        if best is None or k*n>best[0]*best[1]:best=(k,n,(q,h>0,lp,rp,I,O),out)
    return best
def discover():
    z=(0,(0,0),(0,0));t=0;actions=[];raw=0;start=z
    while P[2*z[0]+head(z[1])]!=24:
        m=motif(z)
        if m:
            if raw:actions.append(('raw',raw,start,z));raw=0
            k,n,rule,out=m;actions.append(('sweep',k,n,rule,z,out));t+=k*n;z=out;start=z
        else:
            z=step(z);t+=1;raw+=1
        assert t<=1673357
    if raw:actions.append(('raw',raw,start,z))
    assert t==1673357 and z[0]==5 and head(z[1])==0 and len(actions)==3255
    return actions

def w(x):return f'⟨{x[0]},{x[1]}⟩'
def z(x):return f'⟨{x[0]},{w(x[1])},{w(x[2])}⟩'
def bl(x):return str(bool(x)).lower()
NS='BB6.Agent6E0ZeroRCTrace'
HEADER='''set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6E0ZeroRCTrace
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump
open BB6.Agent32Raw59PackedQuery BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit
'''
def emit(A):
    OUT.mkdir(exist_ok=True)
    rules=[]
    for a in A:
        if a[0]=='sweep':
            t=(a[1],a[3])
            if t not in rules:rules.append(t)
    s='import Raw59PackedMacro\n'+HEADER+'\ndef p : PartialMachine := fun s => match s.1.val,s.2 with\n'
    for i,v in enumerate(P):
        if v!=24:s+=f'  | {i//2},{bl(i%2)} => some (some ⟨{bl(v&2)},{bl(v&1)},{v//4}⟩)\n'
    s+='  | _,_ => none\n'
    for i,(k,r) in enumerate(rules):
        q,right,lp,rp,I,O=r
        s+=f'def r{i} : Rule := ⟨{q},{bl(right)},{w(lp)},{w(rp)},{w(I)},{w(O)},{k}⟩\ntheorem vr{i} : r{i}.Valid p := by intro L R; rfl\n'
    s+='def a (i n : Nat) : Action p := match i with\n'
    for i in range(len(rules)):s+=f'  | {i+1} => .sweep r{i} vr{i} n\n'
    s+='  | _ => .raw n\n'
    B=32
    chunks=[A[j:j+B] for j in range(0,len(A),B)]
    for i,chunk in enumerate(chunks):s+=f'def z{i} : BZ := {z(chunk[0][-2])}\n'
    num=len(chunks)
    s+=f'def z{num} : BZ := {z(A[-1][-1])}\nend {NS}\n'
    (OUT/'E0ZeroRCTraceBase.lean').write_text(s)
    names=[];cur=[]
    for start in range(0,num,8):
        name=f'E0ZeroRCTracePart{start//8:02}';names.append(name)
        s='import E0ZeroRCTraceBase\n'+HEADER
        for i,chunk in enumerate(chunks[start:start+8],start):
            cost=sum(a[1] if a[0]=='raw' else a[1]*a[2] for a in chunk)
            s+=f'def t{i} : List (Action p) := ['+','.join(f'a 0 {a[1]}' if a[0]=='raw' else f'a {rules.index((a[1],a[3]))+1} {a[2]}' for a in chunk)+']\n'
            s+=f'theorem h{i} : run0 p {cost} z{i}.decode = some z{i+1}.decode := by\n  exact trace_sound t{i} z{i} z{i+1} (by decide)\n'
            cur.append((f'h{i}',cost,i,i+1))
        (OUT/(name+'.lean')).write_text(s+f'end {NS}\n')
    s=''.join(f'import {name}\n' for name in names)+HEADER
    layer=0
    while len(cur)>1:
        nxt=[]
        for i in range(0,len(cur),2):
            if i+1==len(cur):nxt.append(cur[i]);continue
            l,r=cur[i:i+2];nm=f'j{layer}_{i//2}';cost=l[1]+r[1]
            s+=f'theorem {nm} : run0 p {cost} z{l[2]}.decode = some z{r[3]}.decode := join0 {l[0]} {r[0]}\n'
            nxt.append((nm,cost,l[2],r[3]))
        cur=nxt;layer+=1
    s+=f'''theorem first_query : zipRead p 1673357 = some (5,false) :=
  read_of_run p 1673357 z{num} (5,false) {cur[0][0]} (by decide)
theorem noAssignedHalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩; have hq : q.val < 6 := q.isLt
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    simp only [Fin.ext_iff]; omega
  rcases hcases with h|h|h|h|h|h <;> subst q <;> cases b <;> decide
theorem weighted : Cover (WeightedBound 1673363) p := by
  let t : BB6.Agent31ThreeHole.Audit := .last 1673357 (5,false)
  have hc : partialCheck 1673363 p (.closed t) = true :=
    last_of_query 1673363 p 1673357 (5,false)
      (query_of_read 1673363 p 1673357 (5,false) first_query (by decide) (by decide)) (by decide)
  apply Cover.leaf
  intro m hm
  rcases partialSound 1673363 p (.closed t) (by decide) noAssignedHalt hc m hm with h|h
  · exact h
  · simp [partialResiduals] at h
#print axioms first_query
#print axioms weighted
end {NS}
'''
    (OUT/'E0ZeroRCTrace.lean').write_text(s)
if __name__=='__main__':emit(discover())
