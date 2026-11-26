"""Emit source-level zipper side-cycle replay for 3863. No native_decide."""
import sys
from collections import deque
from pathlib import Path
codes=[7,10,11,21,14,17,24,16,20,11,3,0]
entry=30522;period=61735;boundary=-169;prefix=93;chunk=512
q=h=0;l=deque();r=deque()
seed=list(range(0,entry,chunk))+[entry]
loop=list(range(entry,entry+period,chunk))+[entry+period]
targets=set(seed+loop);cs={}
for t in range(entry+period+1):
    if t in targets:cs[t]=(q,h,list(l),list(r))
    if t==entry+period:break
    if t>=entry:assert h<=boundary
    code=codes[2*q+(l[0] if l else 0)];assert code<24
    if l:l.popleft()
    if code&1:
        l.appendleft(bool(code&2));l.appendleft(r.popleft() if r else False);h+=1
    else:r.appendleft(bool(code&2));h-=1
    q=code//4
assert cs[entry][0]==cs[entry+period][0]
assert cs[entry+period][1]-cs[entry][1]==-349
assert cs[entry][2]==cs[entry+period][2]
assert cs[entry][3][:prefix]==cs[entry+period][3][:prefix]
assert boundary<=cs[entry][1]+prefix
lines=['import E0LFZipSideCycle','set_option maxRecDepth 1000000','set_option maxHeartbeats 0','namespace BB6.Agent3E0LF3863','open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent3ZipSideCycle',f'def p3863 : PartialMachine := FAR.fromCodes {codes}']
def bits(xs):return '['+','.join('true' if a else 'false' for a in xs)+']'
for t,(q,h,l,r) in cs.items():lines.append(f'def c{t} : Z := ⟨{q},{h},{bits(l)},{bits(r)}⟩')
def section(ts,kind):
    expr='zrun p3863' if kind=='seed' else f'zwindow p3863 ({boundary})'
    joiner='join' if kind=='seed' else 'window_join'
    def merge(ts):
        a,b=ts[0],ts[-1];name=f'{kind}{a}_{b}'
        if len(ts)==2:body='by rfl'
        else:
            mid=len(ts)//2
            left=merge(ts[:mid+1]);right=merge(ts[mid:]);body=f'{joiner} {left} {right}'
        lines.append(f'theorem {name} : {expr} {b-a} c{a} = some c{b} := {body}')
        return name
    return merge(ts)
a=section(seed,'seed');b=section(loop,'loop')
lines += [f'theorem never3863 (m : Machine) (hm : compatible p3863 m) : NeverHalts m :=',f'  zipCycle_never p3863 m hm {entry} {period} ({boundary}) {prefix} c{entry} c{entry+period}',f'    (by decide) {a} {b} (by decide) rfl rfl rfl (by decide)', '#print axioms never3863','end BB6.Agent3E0LF3863']
Path(sys.argv[1]).write_text('\n'.join(lines)+'\n')
