"""Factor closed and residual audits, retaining original leaf semantics.
Usage: python split_partial.py SOURCE_KID.lean OUTPUT_DIRECTORY [max_leaf_chars]
Compile emitted modules in the printed order with the original core and QuickWeight.
"""
import re,sys
from pathlib import Path
src=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(exist_ok=True,parents=True)
limit=int(sys.argv[3]) if len(sys.argv)>3 else 2500
s=src.read_text();header=s[:s.index('\ndef kid')];footer='\nend BB6.Agent43Raw122\n'
m=re.search(r'def (kid\d+_\d+) : PartialAudit := (.*?)\ntheorem \1_checked : partialCheck 7014 (.*?) \1 = true := by',s,re.S);assert m,src
kid,audit,root=m.groups();modules=[];records=[];counter=0
P='1RB---1RC---0RD---1LD1RE---0LF------';PARENT=[P[i:i+3] for i in range(0,36,3)]
MOVES=[f'{w}{d}{q}' for w in '01' for d in 'LR' for q in 'ABCDEF']
table=PARENT.copy();branch,sub=map(int,re.findall(r'\d+',kid));table[11]=MOVES[branch]
slot=re.search(r'\) \((\d+),(true|false)\) \(some',root);assert slot,root
slot=2*int(slot[1])+(slot[2]=='true');table[slot]=MOVES[sub]

def split_args(s):
 depth=0;start=0;result=[]
 for j,c in enumerate(s):
  if c in '([{⟨':depth+=1
  elif c in ')]}⟩':depth-=1
  elif c==',' and depth==0:result.append(s[start:j].strip());start=j+1
  assert depth>=0
 assert depth==0;result.append(s[start:].strip());assert len(result)==24,len(result);return result

def move(i):return f'⟨{str(i>=12).lower()},{str(i%12>=6).lower()},{i%6}⟩'
def emit(name,deps,body):records.append((name,deps,body))
def check(p,decl,partial):return ('partialCheck' if partial else 'zipCheck')+f' 7014 {p} {decl} = true'
def literal(t):
 return 'fun s => match s.1.val,s.2 with\n'+''.join(f'  | {j//2},{str(bool(j%2)).lower()} => some (some {move(MOVES.index(a))})\n' for j,a in enumerate(t) if a!='---')+'  | _,_ => none'

def build(a,p,t,partial):
 global counter
 idx=counter;counter+=1
 name=f'{src.stem}Split{idx:04}';decl=f'{kid}_s{idx:04}'
 if partial and a.startswith('.closed ('):
  child=build(a[9:-1],p,t,False)
  emit(name,[child[0]],f'def {decl} : PartialAudit := .closed {child[1]}\ntheorem {decl}_checked : {check(p,decl,True)} := {child[1]}_checked\n')
  return name,decl
 typ='PartialAudit' if partial else 'Audit'; m=re.fullmatch(r'\.split (\d+) (\([^)]*\)) \(by'+('PartialMove' if partial else 'Move')+r' \[\s*(.*)\s*\]\)',a,re.S)
 if a=='.unresolved':
  assert partial
  emit(name,[],f'def {decl} : PartialAudit := .unresolved\ntheorem {decl}_checked : {check(p,decl,True)} := rfl\n')
 elif (not m) or (len(a)<=limit and not partial):
  assert not partial,a[:100]
  tab=decl+'_table';tab_eq=decl+'_table_eq'
  emit(name,[],f'''def {decl} : Audit := {a}
def {tab} : PartialMachine := {literal(t)}
theorem {tab_eq} : {tab} = {p} := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem {decl}_checked : {check(p,decl,False)} := by
  rw [← {tab_eq}, ← BB6.Agent43QuickWeight.quickPrefix_eq]
  decide
''')
 else:
  n,sl,children=m.groups();children=split_args(children);k=re.fullmatch(r'\((\d+),(true|false)\)',sl);j=2*int(k[1])+(k[2]=='true');assert t[j]=='---',(t,sl)
  kids=[]
  for i,c in enumerate(children):
   u=t.copy();u[j]=MOVES[i];kids.append(build(c,f'(refine {p} {sl} (some {move(i)}))',u,partial))
  ks=decl+'_kids';cases='\n'.join('  · exact '+kids[12*w+6*r+q][1]+'_checked' for q in range(6) for w in range(2) for r in range(2))
  emit(name,[k[0] for k in kids],f'''def {ks} : Move → {typ} := by{'PartialMove' if partial else 'Move'} [{','.join(k[1] for k in kids)}]
theorem {ks}_checked (mv : Move) : {check(f'(refine {p} {sl} (some mv))',f'({ks} mv)',partial)} := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def {decl} : {typ} := .split {n} {sl} {ks}
theorem {decl}_checked : {check(p,decl,partial)} := by
  rw [{decl},{'partialCheck.eq_3' if partial else 'zipCheck.eq_5'}]
  simp only [Bool.and_eq_true]
  exact ⟨by rw [← BB6.Agent43QuickWeight.quickZipQuery_eq]; decide, allMoves_of _ {ks}_checked⟩
''')
 return name,decl
name,decl=build(audit,root,table,True)
emit(src.stem,[name],f'''def {kid} : PartialAudit := {decl}
theorem {kid}_checked : {check(root,kid,True)} := {decl}_checked
#print axioms {kid}_checked
''')
owner={};pending=[]
def flush():
 if not pending:return
 name=src.stem+'Pack'+str(len(modules)).zfill(3);here={r[0] for r in pending};deps=sorted({owner[d] for _,ds,_ in pending for d in ds if d not in here})
 (out/(name+'.lean')).write_text('import QuickWeight\n'+''.join(f'import {d}\n' for d in deps)+header+'\n'+'\n'.join(r[2] for r in pending)+footer)
 modules.append(name);owner.update((r[0],name) for r in pending);pending.clear()
for r in records[:-1]:
 if pending and (len(pending)>=12 or sum(len(x[2]) for x in pending)+len(r[2])>24000):flush()
 pending.append(r)
flush();name,ds,body=records[-1]
(out/(name+'.lean')).write_text(''.join(f'import {owner[d]}\n' for d in ds)+header+'\n'+body+footer);modules.append(name);print('\n'.join(modules))
