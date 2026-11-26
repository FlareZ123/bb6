"""Factor original Raw122 partial audits at their checked query configurations.
Usage: prefix_factor.py INPUT OUTPUT_DIR [max_subtree_chars]
The simulator proposes anchors only; Lean checks every anchored advance, query,
leaf, and original partialCheck conclusion via PrefixCut.
"""
from pathlib import Path
import re,sys
src=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(exist_ok=True,parents=True)
limit=int(sys.argv[3]) if len(sys.argv)>3 else 2500
s=src.read_text();header=s[:s.index('\ndef kid')]+'''\nopen BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit
open BB6.Agent43QuickWeight BB6.Agent43PrefixCut
''';footer='\nend BB6.Agent43Raw122\n'
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
def bits(s):return '['+','.join('true' if b=='1' else 'false' for b in s)+']'
def config(c):q,h,l,r=c;return f'⟨{q},({h}),{bits(l)},{bits(r)}⟩'
start=(0,0,'','')
def advance(t,z,n,tab):
 if n<t:t,z=0,start
 q,h,l,r=z
 for _ in range(t,n):
  a=tab[q*2+int(l[0] if l else '0')];assert a!='---',(q,h,l,r,tab,t,n)
  q=ord(a[2])-65;w=a[0];l=l[1:]
  if a[1]=='R':h+=1;l=(r[0] if r else '0')+w+l;r=r[1:]
  else:h-=1;r=w+r
 return q,h,l,r

def check(p,decl,partial,t,z):return ('fastPartialAt' if partial else 'quickCheckAt')+f' 7014 {p} {t} {z} {decl} = true'
def literal(t):
 return 'fun s => match s.1.val,s.2 with\n'+''.join(f'  | {j//2},{str(bool(j%2)).lower()} => some (some {move(MOVES.index(a))})\n' for j,a in enumerate(t) if a!='---')+'  | _,_ => none'
def build(a,p,tab,partial,t,z,zname,zdep):
 global counter
 idx=counter;counter+=1;name=f'{src.stem}Cut{idx:04}';decl=f'{kid}_c{idx:04}'
 deps=[zdep] if zdep else []
 if partial and a.startswith('.closed ('):
  child=build(a[9:-1],p,tab,False,t,z,zname,zdep)
  emit(name,[child[0]]+deps,f'def {decl} : PartialAudit := .closed {child[1]}\ntheorem {decl}_checked : {check(p,decl,True,t,zname)} := {child[1]}_checked\n');return name,decl
 typ='PartialAudit' if partial else 'Audit';m=re.fullmatch(r'\.split (\d+) (\([^)]*\)) \(by'+('PartialMove' if partial else 'Move')+r' \[\s*(.*)\s*\]\)',a,re.S)
 if a=='.unresolved':
  assert partial;emit(name,deps,f'def {decl} : PartialAudit := .unresolved\ntheorem {decl}_checked : {check(p,decl,True,t,zname)} := rfl\n')
 elif (not m) or (len(a)<=limit and not partial):
  assert not partial,a[:100];tn=decl+'_table'
  emit(name,deps,f'''def {decl} : Audit := {a}
def {tn} : PartialMachine := {literal(tab)}
theorem {tn}_eq : {tn} = {p} := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem {decl}_checked : {check(p,decl,False,t,zname)} := by
  rw [← {tn}_eq]
  decide
''')
 else:
  n,sl,children=m.groups();n=int(n);children=split_args(children);k=re.fullmatch(r'\((\d+),(true|false)\)',sl);j=2*int(k[1])+(k[2]=='true');assert tab[j]=='---',(tab,sl)
  c=advance(t,z,n,tab);assert c[0]*2+int(c[2][0] if c[2] else '0')==j,(c,sl)
  cn=decl+'_anchor';anchor=name+'Anchor';emit(anchor,deps,f'def {cn} : Z := {config(c)}\n')
  kids=[]
  for i,v in enumerate(children):
   u=tab.copy();u[j]=MOVES[i];kids.append(build(v,f'(refine {p} {sl} (some {move(i)}))',u,partial,n,c,cn,anchor))
  ks=decl+'_kids';cases='\n'.join('  · exact '+kids[12*w+6*r+q][1]+'_checked' for q in range(6) for w in range(2) for r in range(2));lemma='fast_partial_split' if partial else 'fast_split'
  emit(name,[k[0] for k in kids]+deps+[anchor],f'''def {ks} : Move → {typ} := by{'PartialMove' if partial else 'Move'} [{','.join(k[1] for k in kids)}]
theorem {ks}_checked (mv : Move) : {check(f'(refine {p} {sl} (some mv))',f'({ks} mv)',partial,n,cn)} := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def {decl} : {typ} := .split {n} {sl} {ks}
theorem {decl}_checked : {check(p,decl,partial,t,zname)} := by
  unfold {decl}
  apply {lemma} (c := {cn})
  · decide
  · decide
  · exact {ks}_checked
''')
 return name,decl
name,decl=build(audit,root,table,True,0,start,'BB6Coverage.Agent31Pump.start',None)
emit(src.stem,[name],f'''def {kid} : PartialAudit := {decl}
theorem {kid}_checked : partialCheck 7014 {root} {kid} = true := by
  exact checked_of_fastPartialAt (t := 0) (z := BB6Coverage.Agent31Pump.start) (by rfl) {decl}_checked
#print axioms {kid}_checked
''')
owner={};pending=[]
def flush():
 if not pending:return
 name=src.stem+'CutPack'+str(len(modules)).zfill(3);here={r[0] for r in pending};deps=sorted({owner[d] for _,ds,_ in pending for d in ds if d not in here})
 (out/(name+'.lean')).write_text('import PrefixCut\n'+''.join(f'import {d}\n' for d in deps)+header+'\n'+'\n'.join(r[2] for r in pending)+footer)
 modules.append(name);owner.update((r[0],name) for r in pending);pending.clear()
for r in records[:-1]:
 if pending and (len(pending)>=14 or sum(len(x[2]) for x in pending)+len(r[2])>24000):flush()
 pending.append(r)
flush();name,ds,body=records[-1]
(out/(name+'.lean')).write_text(''.join(f'import {owner[d]}\n' for d in ds)+header+'\n'+body+footer);modules.append(name);print('\n'.join(modules))
