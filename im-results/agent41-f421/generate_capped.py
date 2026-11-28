"""Generate small independent Lean kernel checks for F421 finite-horizon length.
No arithmetic from this script is trusted: each checkpoint equality is checked
with decide +kernel against the exact Lean recurrence.
"""
from pathlib import Path
import argparse

def checkpoints(stride):
    horizon=32750
    xs=[14,30,6,22,14,1,2]
    count=8
    states=[(horizon,count,xs)]
    for k in range(horizon-1,-1,-1):
        d=0; ys=[]
        for x in xs:
            if x==1:
                d+=1
            else:
                v=(x-1)<<d
                if v<=k:
                    ys.append(v)
        v=1<<(d+1)
        if v<=k:
            ys.append(v)
        xs=ys; count+=1-d
        if (horizon-k)%stride==0 or k==0:
            states.append((k,count,xs))
    assert states[-1]==(0,8215,[])
    return states

def literal(state):
    _,count,xs=state
    return f'({count},[{",".join(map(str,xs))}])'

def generate(dest:Path,stride:int,shard:int):
    dest.mkdir(parents=True,exist_ok=True)
    states=checkpoints(stride)
    modules=[]
    for j,start in enumerate(range(0,len(states)-1,shard)):
        end=min(start+shard,len(states)-1)
        module=f'F421CappedCheck{j:02d}'
        modules.append(module)
        lines=['import F421CappedLife','open F421CappedLife','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace F421CappedCertificate']
        for i in range(start,end):
            h=states[i][0]; k=states[i+1][0]; n=h-k
            lhs=literal(states[i]); rhs=literal(states[i+1])
            lines.append(f'theorem step{i:04d} : chunk {n} {k} {lhs} = {rhs} := by decide +kernel')
        h=states[start][0]; k=states[end][0]; lhs=literal(states[start]); rhs=literal(states[end])
        lines.append(f'theorem shard{j:02d} : iter {h} {lhs} = iter {k} {rhs} := by')
        lines.append('  calc')
        for i in range(start,end):
            h=states[i][0]; k=states[i+1][0]; n=h-k
            lhs=literal(states[i]); rhs=literal(states[i+1])
            lines.append(f'    {"iter "+str(h)+" "+lhs if i==start else "_"} = iter {k} {rhs} := by')
            lines.append(f'      rw [show {h} = {k}+{n} by decide, iter_chunk, step{i:04d}]')
        lines.append(f'#print axioms shard{j:02d}')
        lines.append('end F421CappedCertificate')
        (dest/f'{module}.lean').write_text('\n'.join(lines)+'\n')
    lines=[f'import {m}' for m in modules]+['open F421CappedLife','namespace F421CappedCertificate','theorem exact_count : (iter 32750 first).1 = 8215 := by','  have h : iter 32750 first = (8215,[]) := by','    change iter 32750 (8,[14,30,6,22,14,1,2]) = _']
    lines+=['    rw ['+','.join(f'shard{j:02d}' for j in range(len(modules)))+']','  exact congrArg Prod.fst h','#print axioms exact_count','end F421CappedCertificate']
    (dest/'F421CappedCertificate.lean').write_text('\n'.join(lines)+'\n')
    print('checkpoints:',len(states)-1,'shards:',len(modules),'largest active list:',max(len(s[2]) for s in states))

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--stride',type=int,default=100);p.add_argument('--shard',type=int,default=16);p.add_argument('--dest',type=Path,default=Path('.'))
    a=p.parse_args(); assert a.stride>0 and a.shard>0; generate(a.dest,a.stride,a.shard)
