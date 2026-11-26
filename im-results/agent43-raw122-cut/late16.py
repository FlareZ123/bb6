#!/usr/bin/env python3
"""Emit a kernel-checkable compressed certificate for raw122 kid16_13.
Usage: python late16.py WORK_DIRECTORY
Compile generated Raw122Late16.lean, then LateBound.lean from this dossier,
with Agent29's PackedAction122 dependency closure on LEAN_PATH.
"""
from pathlib import Path
import sys
TABLE='1RB0LA1RC---0RD0RB1LD1RE0LA0LF1LB1LE'
MOVES=[TABLE[i:i+3] for i in range(0,36,3)]
TRANS=[None if a=='---' else (int(a[0]),1 if a[1]=='R' else -1,ord(a[2])-65) for a in MOVES]
# q, cost, direction-right, left anchor, right anchor, input, output;
# all words are least-significant bit first. Lean verifies every motif.
MOTIFS={0:(3,1,False,'','','0','1'),1:(1,2,True,'0','','10','01'),
        3:(4,2,False,'','','11','10'),17:(4,6,True,'010','','10','11')}

def step(z):
    q,l,r=z;a=TRANS[2*q+(l&1)]
    if a is None:return None
    w,d,n=a
    return (n,(r&1)+2*(w+2*(l>>1)),r>>1) if d==1 else (n,l>>1,w+2*r)

def num(x):return sum(int(b)<<i for i,b in enumerate(x))
def rep(x,n):return num(x)*((1<<(len(x)*n))-1)//((1<<len(x))-1)
def apply(i,n,z):
    if i<0:
        for _ in range(n):
            z=step(z);assert z is not None
        return z
    q,l,r=z;mq,k,right,lp,rp,I,O=MOTIFS[i];a,b=len(lp),len(rp);d=len(I)*n;e=len(O)*n
    if q!=mq:return None
    if right:
        if l%(1<<a)!=num(lp) or r%(1<<(b+d))!=num(rp)+(rep(I,n)<<b):return None
        return q,num(lp)+(rep(O,n)<<a)+((l>>a)<<(a+e)),num(rp)+((r>>(b+d))<<b)
    if r%(1<<b)!=num(rp) or l%(1<<(a+d))!=num(lp)+(rep(I,n)<<a):return None
    return q,num(lp)+((l>>(a+d))<<a),num(rp)+(rep(O,n)<<b)+((r>>b)<<(b+e))

def discover():
    z=(0,0,0);t=0;actions=[]
    while step(z) is not None:
        best=None
        for i,m in MOTIFS.items():
            w=apply(i,1,z)
            if w is None:continue
            n=1
            while (v:=apply(i,1,w)) is not None:
                w=v;n+=1
                assert n<100000
            if n>=2 and (best is None or n*m[1]>best[0]):best=(n*m[1],i,n,w)
        if best:
            k,i,n,z=best;t+=k;actions.append((i,n))
        else:
            z=step(z);t+=1
            if actions and actions[-1][0]==-1:actions[-1]=(-1,actions[-1][1]+1)
            else:actions.append((-1,1))
        assert t<=1296924
    assert t==1296924 and z[0]==1 and z[1]&1==1
    assert len(actions)==3597
    return actions,z

def bools(x):return '['+','.join('true' if b=='1' else 'false' for b in x)+']'
def zstr(z):return '⟨'+','.join(map(str,z))+'⟩'
def emit(work):
    actions,end=discover()
    f=['import PackedAction122','set_option maxRecDepth 100000','set_option maxHeartbeats 0',
       'set_option exponentiation.threshold 100000','namespace BB6Coverage.Agent43Raw122Late16',
       'open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun BB6Coverage.Agent10ZipAudit',
       'open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent47PartialAudit',
       'def table : PartialMachine := fun s => match s.1.val,s.2 with']
    for i,a in enumerate(MOVES):
        if a!='---':f.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)')
    f+=['  | _,_ => none']
    for i,(q,k,right,lp,rp,I,O) in MOTIFS.items():
        f += [f'def motif{i} : Motif := ⟨{q},{k},{str(right).lower()},{bools(lp)},{bools(rp)},{bools(I)},{bools(O)}⟩',
              f'theorem valid{i} : (motif{i}).Valid table := by','  refine ⟨by decide, by decide, ?_⟩','  intro L R','  rfl']
    z=(0,0,0);t=0;f+=['def c0 : PZ := ⟨0,0,0⟩'];GROUP=64
    for j,b in enumerate(range(0,len(actions),GROUP)):
        k=0;terms=[]
        for i,n in actions[b:b+GROUP]:
            z=apply(i,n,z);assert z is not None;k+=n*(1 if i<0 else MOTIFS[i][1]);terms.append(f'.prim {n}' if i<0 else f'.sweep motif{i} valid{i} {n}')
        f += [f'def c{j+1} : PZ := {zstr(z)}',f'def acts{j} : List (Action table) := ['+','.join(terms)+']',
              f'theorem block{j} : prun table {k} c{j} = some c{j+1} := by',
              f'  exact runActions_sound acts{j} c{j} c{j+1} (by decide)']
        if j==0:f.append(f'theorem join{j} : prun table {k} c0 = some c{j+1} := block{j}')
        else:f.append(f'theorem join{j} : prun table {t+k} c0 = some c{j+1} := @pjoin table {t} {k} c0 c{j} c{j+1} join{j-1} block{j}')
        t+=k
    assert t==1296924 and z==end and j==56
    f += [f'theorem exact_query : zipRead table {t} = some (1,true) := packed_read join{j}', '#print axioms exact_query','end BB6Coverage.Agent43Raw122Late16']
    work.mkdir(parents=True,exist_ok=True)
    (work/'Raw122Late16.lean').write_text('\n'.join(f)+'\n')

if __name__=='__main__':emit(Path(sys.argv[1]))
