"""Generate independent kernel-checkable certificate segments.

Usage: python generate_chunks.py 350 586 8
Outputs Cert350Data.lean, Cert350Part*.lean, Cert350Proof.lean.
Compile Data, Parts in any order, then Proof with existing source imports.
No generated numerical claim is trusted; each segment is checked by Lean.
"""
import sys
from pathlib import Path

n,K,size=map(int,sys.argv[1:])
P=2**n
Q=7*P-n-3
ns=f'BB6.Agent23FullCone.Cert{n}'
header=['namespace '+ns,'open BB6.Agent23FullCone','set_option maxHeartbeats 0','set_option maxRecDepth 100000']
defs=[f'def p : Nat := {P}',f'def q : Nat := {Q}']
cs=[1]
starts=list(range(0,K,size))+[K]
startset=set(starts)
for j in range(K+1):
    if j in startset:
        defs.append(f'def s{j} : List Nat := {cs}')
    if j==K:
        break
    assert all(v!=2 and v+2*j+2*n+3<7*P for v in cs)
    cs=[w for v in cs for w in ([v//2] if v%2==0 else [])+([(v+Q-j)//2] if (v+Q-j)%2==0 else [])]
assert not cs

def write(name, lines):
    Path(name+'.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')

data=f'Cert{n}Data'
write(data,['import FullConeCertChunks']+header+defs+['end '+ns])
checks=[]
for j,k in zip(starts,starts[1:]):
    a=k-j
    checks += [
        f'theorem safe{j} : prefixSafe p {n} q {j} s{j} {a} = true := by decide',
        f'theorem step{j} : states q {j} s{j} {a} = s{k} := by rfl',
    ]
parts=[]
for i in range(0,len(checks),16):
    name=f'Cert{n}Part{i//16}'
    parts.append(name)
    write(name,['import '+data]+header+checks[i:i+16]+['end '+ns])
joins=[f'theorem c{K} : cert p {n} q {K} s{K} 0 = true := by rfl']
for j,k in reversed(list(zip(starts,starts[1:]))):
    a=k-j
    b=K-k
    joins.append(f'theorem c{j} : cert p {n} q {j} s{j} {K-j} = true := cert_join p {n} q {j} s{j} s{k} {a} {b} safe{j} step{j} c{k}')
joins += [
    f'theorem cert{n} : cert (2^{n}) {n} (7*2^{n}-{n+3}) 0 [1] {K} = true := c0',
    f'theorem source_critical{n}_no_reach : ¬BB6.Agent1.Reach 2 (14*2^{n}-2*{n}-10) := source_critical_reset_no_reach {n} {K} (by decide) (by decide) cert{n}',
    f'#print axioms source_critical{n}_no_reach',
]
write(f'Cert{n}Proof',['import '+p for p in parts]+header+joins+['end '+ns])
