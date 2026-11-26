from pathlib import Path
import sys
N=2000
B=108667
rows=Path('rc.open').read_text().splitlines()
core=Path('core')
for i in (77,81,91,94):
 p=[s for group in rows[i].split('_') for s in (group[:3],group[3:])]
 z=(0,0,0); t=0; chunks=[]
 while True:
  q,l,r=z; m=p[2*q+(l%2)]
  if m=='---':
   chunks.append((t,z));break
  if t%N==0: chunks.append((t,z))
  w=int(m[0]);d=m[1];qn=ord(m[2])-65
  z=(qn,(r%2)+2*(w+2*(l//2)),r//2) if d=='R' else (qn,l//2,w+2*r)
  t+=1
 assert q==1 and l%2==1 and p.count('---')==1
 ns=f'BB6.Agent12LateRCM{i}';base=f'Agent12LateRCM{i}Base';root=f'Agent12LateRCM{i}'
 head=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent12PackedRC
'''
 text='import LateRCBridge\n'+head+'def table : PartialMachine := fun s => match s.1.val, s.2 with\n'
 for k,m in enumerate(p):
  if m!='---':text+=f'  | {k//2},{str(bool(k%2)).lower()} => some (some ⟨{str(m[0]=="1").lower()},{str(m[1]=="R").lower()},{ord(m[2])-65}⟩)\n'
 text+='  | _,_ => none\n'
 for j,(t,z) in enumerate(chunks):text+=f'def z{j} : PZ := ⟨{z[0]},{z[1]},{z[2]}⟩\n'
 (core/f'{base}.lean').write_text(text+f'end {ns}\n')
 modules=[base]
 # Separate leaf objects from composition, to prevent reductions from re-running on every join.
 for j in range(0,len(chunks)-1,5):
  mod=f'{root}Chunk{j:02d}';modules.append(mod)
  text=f'import {base}\n'+head
  for k in range(j,min(j+5,len(chunks)-1)):
   text+=f'theorem seg{k} : prun table {chunks[k+1][0]-chunks[k][0]} z{k} = some z{k+1} := by rfl\n'
  (core/f'{mod}.lean').write_text(text+f'end {ns}\n')
 text=''.join(f'import {m}\n' for m in modules)+head+'attribute [local irreducible] prun knownRun\n'
 for j in range(1,len(chunks)):
  t=chunks[j][0]; prev=chunks[j-1][0]
  text+=f'theorem prefix{j} : prun table {t} z0 = some z{j} := by\n'
  if j==1:text+='  exact seg0\n'
  else:text+=f'  have h := joinP (p := table) (n := {prev}) (k := {t-prev}) (a := z0) (b := z{j-1}) (c := z{j}) prefix{j-1} seg{j-1}\n  exact h\n'
 text+=f'''theorem first_query : (knownRun table {t}).map readSlot = some (1,true) := by
  exact known_read prefix{len(chunks)-1}
theorem bound_all : ∀ m, compatible table m → WeightedBound {B} m :=
  bounded_of_query {B} table {t} (1,true) (by decide) first_query (by decide) (by decide) (by decide)
#print axioms first_query
#print axioms bound_all
end {ns}
'''
 (core/f'{root}.lean').write_text(text)
 print(i,t,len(chunks),rows[i]);Path(f'late{i}.order').write_text('\n'.join(modules+[root])+'\n')
