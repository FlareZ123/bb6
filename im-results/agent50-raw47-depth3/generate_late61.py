from pathlib import Path
from itertools import groupby
import sys
s='1RB1LA1RC0LF0RD0LE1LD0RC0LA0RB---1LB'
t=[s[i:i+3] for i in range(0,36,3)]
# direction, name, state, left frame, right frame, consumed word, produced word, cost
rules=[('left','a',0,[],[],[1],[1],1),('left','d',3,[],[],[0],[1],1),('left','bf',1,[],[],[1,1],[1,0],2),('right','c',2,[0],[],[1,0],[0,0],2),('right','b',1,[0],[0],[1,1],[1,1],6)]
def enc(xs):
    parts=[]
    for bit,grp in groupby(xs):
        n=len(list(grp)); a='true' if bit else 'false'
        parts.append(f'List.replicate {n} {a}' if n>3 else '['+', '.join([a]*n)+']')
    return ' ++ '.join(parts) or '[]'
def step(z):
    q,l,r=z
    x=t[2*q+(l[0] if l else 0)]
    if x=='---':return None
    w=int(x[0]);d=x[1]=='R';q=ord(x[2])-65
    return (q,[r[0] if r else 0,w]+l[1:],r[1:]) if d else (q,l[1:],[w]+r)
def macro(z):
    q,l,r=z;best=None
    for direction,name,Q,lp,rp,I,O,k in rules:
        if q!=Q or l[:len(lp)]!=lp or r[:len(rp)]!=rp:continue
        w=l[len(lp):] if direction=='left' else r[len(rp):]
        n=0
        while w[n*len(I):(n+1)*len(I)]==I:n+=1
        if n<2:continue
        if direction=='left':z1=(q,lp+w[n*len(I):],rp+O*n+r[len(rp):])
        else:z1=(q,lp+O*n+l[len(lp):],rp+w[n*len(I):])
        if best is None or k*n>best[1]:best=(f'.{direction} {name} {n}',k*n,z1)
    return best
z=(0,[],[]);start=z;cmds=[];cost=0;states=[z];chunks=[];chunkcost=0;raw=0
while cost<200000:
    m=macro(z)
    if m:
        if raw:cmds.append(f'.raw {raw}');raw=0
        cmd,k,z1=m
        # Validate macro using the independent primitive simulator.
        u=z
        for _ in range(k):u=step(u)
        assert u==z1,(cmd,z,u,z1)
        z=z1;cmds.append(cmd);cost+=k;chunkcost+=k
    else:
        u=step(z)
        if u is None:break
        z=u;raw+=1;cost+=1;chunkcost+=1
    if len(cmds)>=40:
        if raw:cmds.append(f'.raw {raw}');raw=0
        chunks.append((chunkcost,cmds));states.append(z);cmds=[];chunkcost=0
if raw:cmds.append(f'.raw {raw}')
if cmds:chunks.append((chunkcost,cmds));states.append(z)
assert cost==143975 and z[0]==5 and (not z[1] or not z[1][0]);print('cost',cost,'commands',sum(len(x) for _,x in chunks),'chunks',len(chunks))
a=[]
a+=['def z0 : Z0 := ⟨0,[],[]⟩']
for i,(q,l,r) in enumerate(states[1:],1):
    k,cs=chunks[i-1]
    a.append(f'def z{i} : Z0 := ⟨{q},{enc(l)},{enc(r)}⟩')
    a.append(f'def cs{i} : List (Cmd p) := ['+', '.join(cs)+']')
    a.append(f'theorem h{i} : run0 p {k} z{i-1} = some z{i} := trace_sound cs{i} z{i-1} z{i} (by decide +kernel)')
cur=[(i-1,i,chunks[i-1][0],f'h{i}') for i in range(1,len(states))]
while len(cur)>1:
    nxt=[]
    for i in range(0,len(cur),2):
        if i+1==len(cur):nxt.append(cur[i]);continue
        lo,mid,n1,pr1=cur[i];mid2,hi,n2,pr2=cur[i+1];assert mid==mid2
        name=f'j{lo}_{hi}';a.append(f'theorem {name} : run0 p {n1+n2} z{lo} = some z{hi} := join0 {pr1} {pr2}');nxt.append((lo,hi,n1+n2,name))
    cur=nxt
_,end,n,pr=cur[0]
a.append(f'theorem run_exact : run0 p 143975 ⟨0,[],[]⟩ = some z{end} := {pr}')
template=Path(__file__).with_name('Raw47Late61Macro.template').read_text()
Path(sys.argv[1]).write_text(template.replace('@@TRACE@@','\n'.join(a)).replace('@@END@@',str(end)))
