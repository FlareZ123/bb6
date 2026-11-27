"""Emit independent exact packed-sweep proof chunks for a discovered late query."""
from pathlib import Path
import json,sys
from collections import OrderedDict
src=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
i=int(sys.argv[3]);N=int(sys.argv[4]); assert N>0
A=json.loads((src/f'sweep{i}.json').read_text()); p=json.loads((src/'partition.json').read_text())['open'][i];a=sum(v<<(5*j) for j,v in enumerate(p))
ns=f'namespace BB6.Agent4E0OneLCLate\nopen BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot\nnamespace H{i}Sweep\n'
end=f'end H{i}Sweep\nend BB6.Agent4E0OneLCLate\n'
header='set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'+ns
def write(name,imports,body):
    (out/(name+'.lean')).write_text(''.join(f'import {m}\n' for m in imports)+header+body+end)
def bits(s):return '['+', '.join('true' if x=='1' else 'false' for x in s)+']'
def val(s):return hex(int(s[::-1],2)) if s else '0'
def cfg(z):return f'⟨{z[0]},{val(z[1])},{val(z[2])}⟩'
rules=OrderedDict((tuple(x[1]),None) for x in A if x[0]=='sweep');rules={r:j for j,r in enumerate(rules)}
s=f'def p : PartialMachine := FAR.fromCodes {p}\ndef a : Nat := {a}\ntheorem table : tableCode p a := by unfold tableCode; decide +kernel\n'
for r,ri in rules.items():
    d,q,lp,rp,I,O,k=r
    b=(f'⟨{q},{bits(lp)} ++ L,{bits(rp)} ++ {bits(I)} ++ R⟩' if d else f'⟨{q},{bits(lp)} ++ {bits(I)} ++ L,{bits(rp)} ++ R⟩')
    c=(f'⟨{q},{bits(lp)} ++ {bits(O)} ++ L,{bits(rp)} ++ R⟩' if d else f'⟨{q},{bits(lp)} ++ L,{bits(rp)} ++ {bits(O)} ++ R⟩')
    s+=f'theorem rule{ri} (L R : List Bool) : run0 p {k} {b} = some {c} := by rfl\n'
rules_source=s
config=[A[0][-2]]+[x[-1] for x in A];cost=[0]
for j,x in enumerate(A):assert x[-2]==config[j];cost.append(cost[-1]+(x[1] if x[0]=='finite' else x[1][-1]*x[2]))
assert cost[-1]==N
q,l,r=config[-1];b=l[0]=='1' if l else False;slot=f'({q},{str(b).lower()})'; assert p[2*q+int(b)]==24
boundaries=set(range(0,len(A),32))|{len(A)}
for j in sorted(boundaries): rules_source+=f'def c{j} : Fast := {cfg(config[j])}\n'
write(f'OneLCSweep{i}Rules',['OneLCSweep'],rules_source)

def combine(a,b,leaf,pre='join'):
    if b-a==1:return '',leaf(b)
    m=(a+b)//2;u,un=combine(a,m,leaf,pre);v,vn=combine(m,b,leaf,pre);nm=f'{pre}_{a}_{b}'
    return u+v+f'theorem {nm} : runF a {cost[b]-cost[a]} c{a} = some c{b} := runF_join {un} {vn}\n',nm

names=[];ends=[0]
for start in range(0,len(A),32):
    stop=min(start+32,len(A)); name=f'OneLCSweep{i}Chunk{len(names):03d}'
    s=''
    for j in range(start,stop):
        x=A[j];k=cost[j+1]-cost[j]
        if j+1 not in boundaries:s+=f'def c{j+1} : Fast := {cfg(config[j+1])}\n'
        if x[0]=='finite':proof='by rfl'
        else:
            _,rr,n,b,c=x;d,q,lp,rp,I,O,k1=rr;rn=rules[tuple(rr)];l,r=b[1:];L=l[len(lp)+(0 if d else len(I)*n):];R=r[len(rp)+(len(I)*n if d else 0):]
            proof=f'by exact sweepF{"R" if d else "L"} p a table {q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k1} rule{rn} {n} {val(L)} {val(R)}'
        s+=f'theorem e{j+1} : runF a {k} c{j} = some c{j+1} := {proof}\n'
    u,un=combine(start,stop,lambda k:f'e{k}');s+=u+f'theorem block{len(names)} : runF a {cost[stop]-cost[start]} c{start} = some c{stop} := {un}\n'
    write(name,[f'OneLCSweep{i}Rules'],s);names.append(name);ends.append(stop)

def merge(a,b):
    if b-a==1:return '',f'block{a}'
    m=(a+b)//2;u,un=merge(a,m);v,vn=merge(m,b);aa,bb=ends[a],ends[b];nm=f'blocks_{a}_{b}'
    mm=ends[m]
    return u+v+f'theorem {nm} : runF a {cost[bb]-cost[aa]} c{aa} = some c{bb} := joinExact a {cost[mm]-cost[aa]} {cost[bb]-cost[mm]} {cost[bb]-cost[aa]} c{aa} c{mm} c{bb} rfl {un} {vn}\n',nm
u,un=merge(0,len(names));write(f'OneLCSweep{i}Merge',names+['OneLCJoinExact'],u);j=len(A);s=f'theorem whole : runF a {N} ⟨0,0,0⟩ = some c{j} := {un}\ntheorem read : (knownRun p {N}).map readSlot = some {slot} := read_of_runF table whole\ntheorem cover : Cover (WeightedBound 204890) p := last_of_read 204890 p {N} {slot} read (by decide) (by decide) (by decide) (by decide)\n#print axioms cover\n'
write(f'OneLCSweep{i}',[f'OneLCSweep{i}Merge'],s)
print('emitted',len(names),'chunks',len(rules),'rules')
(out/f'OneLCLate{i}.lean').write_text(f'import OneLCSweep{i}\nnamespace BB6.Agent4E0OneLCLate.H{i}\nopen BB6Coverage BB6.Agent13BlankDelay\nabbrev p : PartialMachine := H{i}Sweep.p\ntheorem cover : Cover (WeightedBound 204890) p := H{i}Sweep.cover\nend BB6.Agent4E0OneLCLate.H{i}\n')
