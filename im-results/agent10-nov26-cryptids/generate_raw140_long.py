"""Generate original-source exact entry certificates using a proved RLE sweep evaluator."""
from pathlib import Path
from collections import deque
from generate_raw140_extra import codes,local_exit,opt
DIR=Path(__file__).resolve().parent
ROWS=[
 (34,21,5,72972,641914,375,'A'),
 (38,21,2,87704,532426,338,'B'),
 (75,23,12,87676,532398,338,'B'),
 (78,23,5,87742,532342,338,'B'),
 (79,23,9,804131,5028558,1050,'B'),
]
CHUNK=1024
GROUP=32

def pop(S,k):
 if not S:return
 a,n=S.popleft();assert n>=k
 if n>k:S.appendleft((a,n-k))

def push(S,a,k):
 if not S and a==0:return
 if S and S[0][0]==a:
  _,n=S.popleft();k+=n
 S.appendleft((a,k))

def fmt_stack(S):return '['+','.join(f'(S {a},{n})' for a,n in S)+']'
def fmt(state):
 q,d,L,R=state
 return f'⟨{q},{str(d).lower()},{fmt_stack(L)},{fmt_stack(R)}⟩'
def adv(M,state):
 q,d,L,R=state;src=R if d else L;a,n=src[0] if src else (0,1)
 c,q2,d2,b=local_exit(M,q,d,a)
 n=n if (q,d)==(q2,d2) else 1
 pop(src,n);push(L if d2 else R,b,n)
 return c*n,(q2,d2,L,R)

def build(row):
 i,a,f,k,t,n,phase=row
 prefix=f'Raw140Long{i}'
 ns=f'Raw140Long.X{i}'
 M=codes(a,f)
 lines=['import Raw140Sweep',f'namespace {ns}', 'open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Sweep', 'set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'def M : Table := fill {opt(a)} {opt(f)}',f'theorem ext : Extends M := fill_extends {opt(a)} {opt(f)}','def s0 : RState := ⟨2,true,[(S 6,1)],[]⟩']
 state=(2,True,deque([(6,1)]),deque());total=2;done=0;group=0;j=0;groupStart=0;costGroup=0;edges=[];mods=[]
 while done<k:
  length=min(CHUNK,k-done);cost=0
  for _ in range(length):
   c,state=adv(M,state);cost+=c
  j+=1;done+=length;total+=cost;costGroup+=cost
  lines.append(f'def s{j} : RState := {fmt(state)}')
  lines.append(f'theorem e{j} : Raw140Sweep.execute M {length} s{j-1} = some ({cost},s{j}) := by decide +kernel')
  edges.append((j,length,cost))
  if len(edges)==GROUP or done==k:
   lines.append(f'theorem group{group} : run M {costGroup} s{groupStart}.prim = some s{j}.prim := by')
   for z,(jj,le,co) in enumerate(edges):
    term=f'(Raw140Sweep.execute_sound M {le} {co} s{jj-1} s{jj} e{jj})'
    lines.append(f'  have h{z} := '+(f'join h{z-1} {term}' if z else term))
   lines.append(f'  exact h{len(edges)-1}')
   lines.append(f'end {ns}')
   mod=f'{prefix}G{group:03d}'
   (DIR/(mod+'.lean')).write_text('\n'.join(lines)+'\n');mods.append((mod,group,costGroup,j))
   group+=1;groupStart=j;edges=[];costGroup=0
   lines=[f'import {mod}',f'namespace {ns}','open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Sweep','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
 assert total==t and state==(1,True,deque([(5,1)]),deque([(2,n),(1,1),(5,1)] if phase=='A' else [(2,n),(4,1),(2,1)])),(i,total,state)
 lines.append(f'theorem entry : run M {t} primBlank = some (family{phase} {n}) := by')
 lines.append('  have h0 : run M 2 primBlank = some s0.prim := run_ext M ext _ _ _ base_start')
 for mod,g,cost,jj in mods:lines.append(f'  have h{g+1} := join h{g} group{g}')
 lines.append(f'  exact h{len(mods)}')
 lines.append(f'theorem forever (k : Nat) : ∃ c, run M k primBlank = some c := forever{phase} M ext {t} {n} entry k')
 lines.append('#print axioms forever');lines.append(f'end {ns}')
 (DIR/(prefix+'.lean')).write_text('\n'.join(lines)+'\n')
 print(i,len(mods),j,t,flush=True)

if __name__=='__main__':
 import sys
 for row in ROWS:
  if not sys.argv[1:] or str(row[0]) in sys.argv[1:]:build(row)
