import json,sys
from pathlib import Path
P=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(exist_ok=True,parents=True)
p=json.loads((P/'partition.json').read_text())['open']; rec=json.loads((P/'recipes.json').read_text())
header='''set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent4E0OneLCLate
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
'''
for i,r in rec.items():
    if r[0]!='late' or r[1]<1000:continue
    i=int(i);n,s=r[1:]; t=p[i];assert t.count(24)==1
    stem=f'OneLCLate{i}'; ns=f'namespace H{i}\n'; end=f'end H{i}\nend BB6.Agent4E0OneLCLate\n'
    def write(name,imports,body):
        (out/(name+'.lean')).write_text(''.join(f'import {m}\n' for m in imports)+header+ns+body+end)
    write(stem+'Table',['OneLCNat'],f'def p : PartialMachine := FAR.fromCodes {t}\n')
    q=l=rr=0;chunk=512; group=32; cuts=[0];configs=['⟨0,0,0⟩']
    for k in range(n):
        v=t[2*q+(l&1)];assert v!=24;w=(v>>1)&1;q=v>>2
        if v&1:l=(rr&1)+2*w+4*(l>>1);rr>>=1
        else:l>>=1;rr=w+2*rr
        if (k+1)%chunk==0 or k+1==n:
            cuts.append(k+1);configs.append(f'⟨{q},{hex(l)},{hex(rr)}⟩')
    assert 2*q+(l&1)==s
    def combine(a,b,leaf):
        if b-a==1:return '',leaf(b)
        mid=(a+b)//2;u,un=combine(a,mid,leaf);v,vn=combine(mid,b,leaf);nm=f'join_{a}_{b}'
        return u+v+f'theorem {nm} : runN p {cuts[b]-cuts[a]} c{a} = some c{b} := runN_join {un} {vn}\n',nm
    j=len(cuts)-1; names=[]; ends=[]
    for a in range(0,j,group):
        b=min(a+group,j); name=stem+f'Chunk{len(names):03d}'
        S=f'def c{a} : N0 := {configs[a]}\n' if a==0 else ''
        for k in range(a+1,b+1):
            S+=f'def c{k} : N0 := {configs[k]}\ntheorem e{k} : runN p {cuts[k]-cuts[k-1]} c{k-1} = some c{k} := by decide +kernel\n'
        u,un=combine(a,b,lambda k:f'e{k}');S+=u+f'theorem block{len(names)} : runN p {cuts[b]-cuts[a]} c{a} = some c{b} := {un}\n'
        write(name,[names[-1] if names else stem+'Table'],S);names.append(name);ends.append(b)
    bounds=[0]+ends
    def merge(a,b):
        if b-a==1:return '',f'block{a}'
        m=(a+b)//2;u,un=merge(a,m);v,vn=merge(m,b);aa,bb=bounds[a],bounds[b];nm=f'blocks_{a}_{b}'
        return u+v+f'theorem {nm} : runN p {cuts[bb]-cuts[aa]} c{aa} = some c{bb} := runN_join {un} {vn}\n',nm
    u,un=merge(0,len(names)); slot=f'({s//2},{str(bool(s%2)).lower()})'
    S=u+f'theorem whole : runN p {n} ⟨0,0,0⟩ = some c{j} := {un}\ntheorem read : (knownRun p {n}).map readSlot = some {slot} := read_of_runN whole\ntheorem cover : Cover (WeightedBound 204890) p := last_of_read 204890 p {n} {slot} read (by decide) (by decide) (by decide) (by decide)\n#print axioms cover\n'
    write(stem,[names[-1]],S)
