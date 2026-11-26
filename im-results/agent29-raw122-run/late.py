"""Generate exact Lean proofs for two late Raw122 first-hole traces.
Usage: python late.py OUTPUT_DIR 0|1 [block_size]
Original artifact 15012394320 provides Raw122Base and SweepPumping.
Compile PackedRun122, PackedSweep122, PackedAction122 first, then generated
PackedLate{i}Base, blocks, joins and PackedLate{i}. All proofs use rfl/decide
and the soundness lemmas, not a trusted simulator.
"""
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import sys

TABLES=[('1RB---1RC0RA0RD0LF1LD1RE0RB0LF1LC0LF',6659486),('1RB0LA1RC---0RD0RB1LD1RE0LA0LF1LB1LE',1296924)]

def parse(m):
    return [None if t=='---' else (int(t[0]),t[1]=='R',ord(t[2])-65) for t in [m[i:i+3] for i in range(0,36,3)]]
def step(m,z):
    q,l,r=z;mv=m[2*q+(l&1)]
    assert mv is not None
    w,d,q=mv
    if d:return q,(r&1)+2*(w+2*(l>>1)),r>>1
    return q,l>>1,w+2*r
@dataclass(frozen=True)
class Macro:
    q:int; k:int; right:bool; lp_len:int; lp:int; rp_len:int; rp:int; d:int; I:int; O:int
    def run(self,z):
        q,l,r=z
        if q!=self.q or l&((1<<self.lp_len)-1)!=self.lp or r&((1<<self.rp_len)-1)!=self.rp:return None
        a,b=(r>>self.rp_len,l>>self.lp_len) if self.right else (l>>self.lp_len,r>>self.rp_len)
        mask=(1<<self.d)-1;n=0;out=0
        while a&mask==self.I:
            if a==0 and self.I==0:break
            a>>=self.d;out=(out<<self.d)|self.O;n+=1
        if n<2:return None
        b=(b<<(self.d*n))|out
        if self.right:new=(q,self.lp|(b<<self.lp_len),self.rp|(a<<self.rp_len))
        else:new=(q,self.lp|(a<<self.lp_len),self.rp|(b<<self.rp_len))
        return n,new

def macro_at(states,positions,i,k):
    q,l,r=states[i];qq,ll,rr=states[i+k]
    if q!=qq:return None
    d=positions[i+k]-positions[i]
    if d==0:return None
    pmin=min(positions[i:i+k+1])-positions[i];pmax=max(positions[i:i+k+1])-positions[i]
    if d>0:
        lp_len=1-pmin;rp_len=pmax-d
        lp=l&((1<<lp_len)-1);rp=r&((1<<rp_len)-1)
        if ll&((1<<lp_len)-1)!=lp or rr&((1<<rp_len)-1)!=rp:return None
        I=(r>>rp_len)&((1<<d)-1);O=(ll>>lp_len)&((1<<d)-1)
        if ll>>(lp_len+d)!=l>>lp_len or rr>>rp_len!=r>>(rp_len+d):return None
        return Macro(q,k,True,lp_len,lp,rp_len,rp,d,I,O)
    else:
        lp_len=1+d-pmin;rp_len=pmax;d=-d
        lp=l&((1<<lp_len)-1);rp=r&((1<<rp_len)-1)
        if ll&((1<<lp_len)-1)!=lp or rr&((1<<rp_len)-1)!=rp:return None
        I=(l>>lp_len)&((1<<d)-1);O=(rr>>rp_len)&((1<<d)-1)
        if ll>>lp_len!=l>>(lp_len+d) or rr>>(rp_len+d)!=r>>rp_len:return None
        return Macro(q,k,False,lp_len,lp,rp_len,rp,d,I,O)

def learn(m,sample=30000):
    z=(0,0,0);p=0;states=[z];positions=[p]
    for t in range(sample):
        q,l,r=z;mv=m[2*q+(l&1)]
        if mv is None:break
        p+=1 if mv[1] else -1;z=step(m,z);states.append(z);positions.append(p)
    count=Counter()
    for i in range(len(states)-65):
        for k in range(1,33):
            if states[i][0]!=states[i+k][0] or states[i][0]!=states[i+2*k][0]:continue
            a=macro_at(states,positions,i,k)
            if a is None:continue
            v=a.run(states[i])
            if v is not None and v[0]>=2:count[a]+=a.k
    return [a for a in sorted(count,key=lambda x:(-count[x],x.k)) if a.k<=12 or count[a]>=1000][:80]

def execute(m,n,macros):
    byq=[[a for a in macros if a.q==q] for q in range(6)]
    z=(0,0,0);t=0;counts=Counter();segments=[];start=z;startt=0
    while t<n:
        best=None
        for a in byq[z[0]]:
            v=a.run(z)
            if v is not None and t+a.k*v[0]<=n and (best is None or a.k*v[0]>best[0].k*best[1][0]):best=(a,v)
        if best is None:
            z=step(m,z);t+=1
            if t-startt>=2000:segments.append((startt,t,start,z,None));start=z;startt=t
        else:
            a,(reps,dst)=best
            if t>startt:segments.append((startt,t,start,z,None))
            segments.append((t,t+a.k*reps,z,dst,(a,reps)))
            counts[a]+=1;z=dst;t+=a.k*reps;startt=t;start=z
    if t>startt:segments.append((startt,t,start,z,None))
    assert m[2*z[0]+(z[1]&1)] is None,(z,t)
    return segments,counts

def generate(P,i,sz):
    raw,n=TABLES[i];m=parse(raw);segs,c=execute(m,n,learn(m))
    ns=f'BB6Coverage.Agent29PackedLate.M{i}';prefix=f'PackedLate{i}'
    header=f'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun\n'
    footer=f'\nend {ns}\n'
    b=lambda x:'true' if x else 'false'
    def word(v,k):return '['+','.join(b((v>>j)&1) for j in range(k))+']'
    def cfg(z):return f'⟨{z[0]},{z[1]},{z[2]}⟩'
    def write(mod,imports,body):
        (P/(mod+'.lean')).write_text(''.join(f'import {a}\n' for a in imports)+header+'\n'.join(body)+footer)
    base=['def table : PartialMachine := fun s => match s.1.val,s.2 with']
    for j in range(12):
        t=raw[3*j:3*j+3]
        if t!='---':base.append(f'  | {j//2},{b(j%2)} => some (some ⟨{b(t[0]=="1")},{b(t[1]=="R")},{ord(t[2])-65}⟩)')
    base+=['  | _,_ => none'];ms={m:j for j,m in enumerate(c)}
    for m,j in ms.items():
        base.append(f'def m{j} : Motif := ⟨{m.q},{m.k},{b(m.right)},{word(m.lp,m.lp_len)},{word(m.rp,m.rp_len)},{word(m.I,m.d)},{word(m.O,m.d)}⟩')
        base.append(f'theorem v{j} : m{j}.Valid table := by\n  refine ⟨by decide,by decide,?_⟩\n  intro L R\n  rfl')
    write(prefix+'Base',['PackedAction122'],base)
    chunks=[];joins=[]
    for j in range(0,len(segs),sz):
        block=segs[j:j+sz];k=len(chunks);a0,a1=block[0][0],block[-1][1];actions=[]
        for t,u,z,w,m in block:
            if m is None:actions.append(f'.prim {u-t}')
            else:
                mot,count=m;idx=ms[mot];actions.append(f'.sweep m{idx} v{idx} {count}')
        body=[f'def c{k} : PZ := {cfg(block[0][2])}',f'def e{k} : PZ := {cfg(block[-1][3])}',f'def a{k} : List (Action table) := ['+', '.join(actions)+']',f'theorem s{k} : prun table {a1-a0} c{k} = some e{k} := by\n  exact runActions_sound a{k} c{k} e{k} (by rfl)']
        mod=prefix+f'Block{k:04}';write(mod,[prefix+'Base'],body);chunks.append(mod)
        if k==0:joins.append(f'theorem j{k} : prun table {a1} ⟨0,0,0⟩ = some e{k} := s{k}')
        else:joins.append(f'theorem j{k} : prun table {a1} ⟨0,0,0⟩ = some e{k} := @pjoin table {a0} {a1-a0} ⟨0,0,0⟩ c{k} e{k} j{k-1} s{k}')
    joinmods=[]
    for j in range(0,len(joins),32):
        mod=prefix+f'Join{j//32:03}';write(mod,([joinmods[-1]] if joinmods else [])+chunks[j:j+32],joins[j:j+32]);joinmods.append(mod)
    write(prefix,[joinmods[-1]],[f'theorem exact_run : prun table {n} ⟨0,0,0⟩ = some e{len(chunks)-1} := j{len(chunks)-1}', '#print axioms exact_run'])
    q,l,r=segs[-1][3];slot=f'({q},{b(l&1)})'
    write('LateCheck'+str(i),[prefix],[
        'open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit',
        f'theorem last_check : zipCheck 6766859 table (.last {n} {slot}) = true := by\n  have h : BB6Coverage.Agent10ZipAudit.zipRead table {n} = some {slot} := packed_read (p:=table) (n:={n}) (z:=e{len(chunks)-1}) exact_run\n  rw [zipCheck.eq_1]\n  simp only [zipQueryOK,h]\n  decide',
        f'theorem bound (m : Machine) (hm : compatible table m) : WeightedBound 6766859 m := by\n  have h : partialCheck 6766859 table (.closed (.last {n} {slot})) = true := last_check\n  have hn : weightedTNFNoAssignedHalt table := by\n    intro ⟨q,b⟩\n    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide\n  have hs := partialSound 6766859 table (.closed (.last {n} {slot})) (by decide) hn h m hm\n  rcases hs with h|⟨e,he,_⟩\n  · exact h\n  · simp [partialResiduals] at he',
        '#print axioms last_check','#print axioms bound'])
    print(i,n,len(segs),len(c),len(chunks))

if __name__=='__main__':
    P=Path(sys.argv[1]);P.mkdir(parents=True,exist_ok=True);i=int(sys.argv[2]);generate(P,i,int(sys.argv[3]) if len(sys.argv)>3 else (256 if i==0 else 32))
