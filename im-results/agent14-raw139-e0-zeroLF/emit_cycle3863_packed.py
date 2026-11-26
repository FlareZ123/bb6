"""Emit packed kernel replay for the exact Agent3 left side-cycle of 3863."""
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
lines=['import PackedZipWindow','set_option maxRecDepth 1000000','set_option maxHeartbeats 0','namespace BB6.Agent14E0LF3863','open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent3ZipSideCycle BB6Coverage.Agent14PackedWindow',f'def ctr : PartialMachine := FAR.fromCodes {codes}']
def bits(xs):return '['+','.join('true' if a else 'false' for a in xs)+']'
def pack(xs):return int('1'+''.join('1' if a else '0' for a in reversed(xs)),2)
for t in [0,entry,entry+period]:
    q,h,l,r=cs[t];lines.append(f'def c{t} : Z := ⟨{q},{h},{bits(l)},{bits(r)}⟩')
for t,(q,h,l,r) in cs.items():
    val=f'pack c{t}' if t in [0,entry,entry+period] else f'⟨{q},{h},{pack(l)},{pack(r)}⟩'
    lines.append(f'private def p{t} : PZ := {val}')
def section(ts,kind):
    guard='none' if kind=='seed' else f'(some ({boundary}))'
    expr=f'prun ctr {guard}'
    def merge(ts):
        a,b=ts[0],ts[-1];name=f'{kind}{a}_{b}'
        if len(ts)==2:body='by decide +kernel'
        else:
            mid=len(ts)//2
            left=merge(ts[:mid+1]);right=merge(ts[mid:]);body=f'prun_join {left} {right}'
        lines.append(f'private theorem {name} : {expr} {b-a} p{a} = some p{b} := {body}')
        return name
    a,b=ts[0],ts[-1];h=merge(ts)
    op='zrun ctr' if kind=='seed' else f'zwindow ctr ({boundary})'
    lines.append(f'theorem {kind} : {op} {b-a} c{a} = some c{b} := replay_sound ctr {guard} {b-a} c{a} c{b} {h}')
section(seed,'seed');section(loop,'loop')
lines += [f'theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=',f'  zipCycle_never ctr m hm {entry} {period} ({boundary}) {prefix} c{entry} c{entry+period}',f'    (by decide) seed loop (by decide) rfl rfl rfl (by decide)', '#print axioms never','end BB6.Agent14E0LF3863']
Path(sys.argv[1]).write_text('\n'.join(lines)+'\n')
