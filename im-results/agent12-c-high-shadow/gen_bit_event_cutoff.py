#!/usr/bin/env python3
"""Generate untrusted Lean event-mask certificates; kernel checks every segment.
No generated assertion uses native_decide, sorry, or a trusted external result.
"""
from dataclasses import dataclass
from pathlib import Path
import argparse

@dataclass(frozen=True)
class State:
    a: int
    k: int
    @property
    def mass(self): return self.a+2*self.k
    @property
    def pair(self): return f'({self.a},{self.k})'
    @property
    def lean(self): return f'⟨{self.a},{self.mass}⟩'

def bounce(k,c):
    if c<4:return None,None
    b=3 if k%2 else 4
    n=0
    while c>2*k+2*b:
        c-=2*k+2*b-3;k=2*k+b;n+=1
    if b==3:return n+2,State(2*k+6-c,c)
    if c==4:return None,State(2*k+2,3)
    if c==5:return None,None
    return n+2,State(2*k+8-c,c-1)

def transition(s):
    a,k=s.a,s.k
    if a==0:
        if k==0:return None,None
        if k==1:return None,State(0,4)
        return None,bounce(1,2*k+1)[1]
    if a==1:
        if k<4:return None,[State(5,1),State(2,3),State(2,5),State(0,7)][k]
        return None,bounce(4,2*k-3)[1]
    if k==0:return None,State(a-2,2)
    if 2*k<=a:return 1,State(a-2*k,2*k+2)
    return bounce(a-1,2*k-a+3)

@dataclass(frozen=True)
class Segment:
    start: State
    end: State
    K: int
    N: int=0
    q: int=0
    R: int=0
    D: int=0
    E: int=0

def segment(s,limit):
    start=s; R=D=E=N=K=0; events=[];good=None
    for _ in range(limit):
        r,t=transition(s)
        if r is None:break
        e=E+1 if r==1 else 1
        if 8*(1<<max(R,r))>start.mass or 40*(1<<max(D,e))>start.mass:break
        N+=r; K+=1;events.append(N);R=max(R,r);D=max(D,e);E=e;s=t
        if 20*(1<<E)<=2*s.k+4:good=(s,N,R,D,E,K)
    if good is None:
        _,t=transition(start)
        if t is None:raise RuntimeError(f'terminal {start}')
        return Segment(start,t,1)
    s,N,R,D,E,K=good
    raw=bytearray((N+7)//8)
    for j in events[:K]:
        bit=N-j;raw[bit//8]|=1<<(bit%8)
    return Segment(start,s,K,N,int.from_bytes(raw,'little'),R,D,E)

def chunks(q):
    h=f'{q:x}'
    hs=[h[max(0,i-1024):i] for i in range(len(h),0,-1024)][::-1]
    return '(['+',\n'.join('0x'+c for c in hs)+'] : List Nat).foldl (fun a b => a*2^4096+b) 0'

HEAD='''import BitEventCertificate
import WordRunnerSource
open BB6.Agent12WordBlock BB6.Agent12BitEventCertificate BB6.Agent46
open BB6.Agent8Section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
'''

def edge(x,i):
    s,t=x.start,x.end
    if not x.N:
        return f'''private theorem edge{i} : BB6.Agent8Section.run secNext 1 (some {s.pair})=some {t.pair} := by
  have h : BB6.Agent12WordRunner.fastNext {s.pair}=some {t.pair} := by decide +kernel
  rw [BB6.Agent12WordRunner.fastNext_eq] at h
  simpa [BB6.Agent8Section.run,h]
'''
    return f'''private def q{i} : Nat := {chunks(x.q)}
private def s{i} : State := {s.lean}
private def t{i} : State := {t.lean}
private def v{i} : Witness := propose s{i} {x.N} q{i}
private theorem check{i} : checked s{i} t{i} {x.N} q{i} {x.R} {x.D} {x.E} {x.K} v{i} := by decide +kernel
private theorem edge{i} : BB6.Agent8Section.run secNext {x.K} (some {s.pair})=some {t.pair} := by
  rw [←BB6.Agent12WordRunner.runNext_eq_source]
  exact certificate secNext BB6.Agent12WordBlock.source_edge_law s{i} t{i} {x.N} q{i} {x.R} {x.D} {x.E} {x.K} v{i} check{i}
'''

def part(path,index,start,count,limit):
    mod=f'BitEventTracePart{index:04d}'
    ns=f'BB6.Agent12BitEventTrace.P{index:04d}'
    s=start;done=0;i=0;single=0
    with (path/f'{mod}.lean').open('w') as f:
        f.write(HEAD+f'namespace {ns}\n')
        while done<count:
            x=segment(s,min(count-done,limit))
            f.write(edge(x,i))
            if i==0:f.write(f'private theorem ep{i} : BB6.Agent8Section.run secNext {x.K} (some {start.pair})=some {x.end.pair} := edge{i}\n')
            else:f.write(f'''private theorem ep{i} : BB6.Agent8Section.run secNext {done+x.K} (some {start.pair})=some {x.end.pair} := by
  rw [←show {done}+{x.K}={done+x.K} by decide,BB6.Agent8Section.run_add,ep{i-1},edge{i}]
''')
            s=x.end;done+=x.K;i+=1;single+=not x.N
        f.write(f'theorem endpoint : BB6.Agent8Section.run secNext {done} (some {start.pair})=some {s.pair} := ep{i-1}\n#print axioms endpoint\nend {ns}\n')
    print(f'{mod}: {done} returns, {i} segments ({single} singles), {start.pair}->{s.pair}, mass {s.mass}',flush=True)
    return mod,ns,s

def main():
    p=argparse.ArgumentParser();p.add_argument('--returns',type=int,default=10000000);p.add_argument('--block',type=int,default=500000);p.add_argument('--group',type=int,default=1000000);p.add_argument('--outdir',type=Path,default=Path(__file__).parent);a=p.parse_args()
    if min(a.returns,a.block,a.group)<=0:raise ValueError('positive bounds required')
    a.outdir.mkdir(parents=True,exist_ok=True)
    start=State(7215288,4780931);s=start;done=0;parts=[]
    while done<a.returns:
        k=min(a.returns-done,a.group)
        mod,ns,t=part(a.outdir,len(parts),s,k,a.block)
        parts.append((mod,ns,s,t,k));s=t;done+=k
    with (a.outdir/'BitEventCutoffGenerated.lean').open('w') as f:
        f.write('import Agent12TerminalCutoff\n'+''.join(f'import {mod}\n' for mod,*_ in parts))
        f.write('open BB6.Agent46 BB6.Agent8Section\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace BB6.Agent12BitEventCutoff\n')
        f.write('private theorem ep0 : BB6.Agent8Section.run secNext 2396378 (some (5,1))=some (7215288,4780931) := BB6.Agent12TerminalCutoff.live_endpoint_16777150\n')
        n=2396378
        for i,(_,ns,_,t,k) in enumerate(parts,1):
            f.write(f'''private theorem ep{i} : BB6.Agent8Section.run secNext {n+k} (some (5,1))=some {t.pair} := by
  rw [←show {n}+{k}={n+k} by decide,BB6.Agent8Section.run_add,ep{i-1},{ns}.endpoint]
''')
            n+=k
        f.write(f'''theorem live_endpoint : BB6.Agent8Section.run secNext {n} (some (5,1))=some {s.pair} := ep{len(parts)}
theorem terminal_cutoff (a k : Nat) (hstop : secNext (a,k)=none) (hrank : a+2*k<{s.mass}) :
    ¬ ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (a,k) :=
  BB6.Agent12TerminalCutoff.terminal_below_live_endpoint {n} {s.a} {s.k} a k live_endpoint hstop (by omega)
#print axioms live_endpoint
#print axioms terminal_cutoff
end BB6.Agent12BitEventCutoff
''')
    print(f'FINAL {n} returns, {s.pair}, mass {s.mass}',flush=True)
if __name__=='__main__':main()
