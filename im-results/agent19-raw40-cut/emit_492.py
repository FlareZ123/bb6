#!/usr/bin/env python3
from macro492 import Cfg
LO, HI = -341034, 767307

def word(c, lo, hi, reverse=False):
    if lo>hi:return '[]'
    blocks=[]; x=lo
    for a,b in c.runs:
        a,b=max(lo,a),min(hi,b)
        if a>b:continue
        if a>x:blocks.append(('Z',a-x))
        blocks.append(('U',b-a+1));x=b+1
    if x<=hi:blocks.append(('Z',hi-x+1))
    if reverse:blocks.reverse()
    return '++'.join(f'{s} {n}' for s,n in blocks)

def left(c,x):return word(c,LO,x,True)
def right(c,x):return word(c,x,HI)
def config(c):
    assert LO<=c.h<=HI and all(LO<=a<=b<=HI for a,b in c.runs)
    return f'⟨0,{left(c,c.h)},{right(c,c.h+1)}⟩'

HEADER='''import Raw40A0RC492Core
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A0RC492
open BB6Coverage BB6Coverage.Agent31Pump
private theorem uCons (R : List Bool) : true::R = U 1++R := rfl
private theorem zCons (R : List Bool) : false::R = Z 1++R := rfl
private theorem uMerge (a b : Nat) (R : List Bool) : U a++(U b++R) = U (a+b)++R := by rw [← List.append_assoc,← uAdd]
private theorem zMerge (a b : Nat) (R : List Bool) : Z a++(Z b++R) = Z (a+b)++R := by rw [← List.append_assoc,← zAdd]
private theorem uMergeEnd (a b : Nat) : U a++U b = U (a+b) := (uAdd a b).symm
private theorem zMergeEnd (a b : Nat) : Z a++Z b = Z (a+b) := (zAdd a b).symm
'''
NORMALIZE='uCons,zCons,List.append_assoc,List.append_nil,List.nil_append,show U 0=[] by rfl,show Z 0=[] by rfl,uMerge,zMerge,uMergeEnd,zMergeEnd'

def emit():
    print(HEADER)
    c=Cfg(0,[]);initial=config(c)
    for i in range(115):
        old=Cfg(c.h,c.runs.copy(),c.cost)
        x=old.h;r=old.rlen(x+1);a=r//2
        typ,k=c.accel()
        if typ=='D' and r%2==0 and not old.b(x):
            name,params,L,R='evenEpoch',str(a),left(old,x-1),right(old,x+r+4)
            assert not any(old.b(j) for j in range(x+r+1,x+r+4))
        elif typ=='D' and r%2==1 and not old.b(x):
            name,params,L,R='oddTwo',str(a),left(old,x-1),right(old,x+r+4)
            assert old.b(x+r+3) and not old.b(x+r+2)
        elif typ=='A0odd1':
            name,params,L,R='oddOne',str(a),left(old,x-1),right(old,x+r+3)
        elif typ=='oddD':
            name,params,L,R='oddMany',f'{a} {k}',left(old,x-k),right(old,x+r+3*k+1)
        elif typ=='leftA11':
            name,params,L,R='leftMany',str(k),left(old,x-k),right(old,x+2)
        elif typ=='transfer':
            name,params,L,R='transferMany',str(k),left(old,x-1),right(old,x+k+3)
        else:raise AssertionError((i,typ,old))
        print(f'private theorem e{i} : run0 table {c.cost-old.cost} {config(old)} = some {config(c)} := by')
        print(f'  have h := {name} {params} ({L}) ({R})')
        print(f'  simpa only [{NORMALIZE}] using h\n')
        proof='e0' if i==0 else f'by\n  have h := join0 p{i-1} e{i}\n  rw [show {old.cost}+{c.cost-old.cost}={c.cost} by rfl] at h\n  exact h'
        print(f'private theorem p{i} : run0 table {c.cost} {initial} = some {config(c)} := {proof}\n')
    assert (c.cost,c.h,c.runs)==(497342773250,-341034,[(-341033,767307)])
    print('''theorem entry : run0 table 497342773250 ⟨0,Z 341035,Z 767307⟩ = some ⟨0,Z 1,U 1108341⟩ := p114
#print axioms entry
end BB6.Agent19Raw40.A0RC492''')

if __name__=='__main__':emit()
