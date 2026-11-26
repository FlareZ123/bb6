"""Generate exact residual-table coverage obligations from a pinned raw122 kid audit.
Imports checked factored kid modules (or original ones). Does not trust extraction:
Lean checks the roster equality and literal tables, with no simulation or decide oracle.
Usage: python residual_roster.py SOURCE_DIR OUTPUT_DIR BRANCH
"""
from pathlib import Path
import re,sys
src,out,branch=Path(sys.argv[1]),Path(sys.argv[2]),int(sys.argv[3]);out.mkdir(exist_ok=True,parents=True)
MOVES=[f'{w}{d}{q}' for w in '01' for d in 'LR' for q in 'ABCDEF']
P='1RB---1RC---0RD---1LD1RE---0LF------';PARENT=[P[i:i+3] for i in range(0,36,3)]
ORDER=[12*w+6*r+q for q in range(6) for w in range(2) for r in range(2)]
def move(i):return f'⟨{str(i>=12).lower()},{str(i%12>=6).lower()},{i%6}⟩'
def literal(t):
 return 'fun s => match s.1.val,s.2 with\n'+''.join(f'  | {j//2},{str(bool(j%2)).lower()} => some (some {move(MOVES.index(a))})\n' for j,a in enumerate(t) if a!='---')+'  | _,_ => none'
def split_args(s):
 depth=0;start=0;res=[]
 for j,c in enumerate(s):
  if c in '([{⟨':depth+=1
  elif c in ')]}⟩':depth-=1
  elif c==',' and depth==0:res.append(s[start:j].strip());start=j+1
  assert depth>=0
 assert depth==0;res.append(s[start:].strip());assert len(res)==24;return res

def strip_outer(s):
 s=s.strip()
 while s.startswith('(') and s.endswith(')'):
  depth=0;closing=None
  for i,c in enumerate(s):
   if c=='(':depth+=1
   elif c==')':
    depth-=1
    if depth==0:closing=i;break
  if closing==len(s)-1:s=s[1:-1].strip()
  else:break
 return s

def bracket_content(s):
 start=s.find('[')
 assert start>=0,s[:100]
 depth=0
 for i in range(start,len(s)):
  if s[i]=='[':depth+=1
  elif s[i]==']':
   depth-=1
   if depth==0:return s[start+1:i]
 raise ValueError('unterminated byPartialMove list')

def add_definition(table,ambiguous,name,body):
 body=body.strip()
 if name in ambiguous:return
 if name in table and table[name]!=body:
  table.pop(name,None);ambiguous.add(name)
 else:table[name]=body

def collect_definitions(directory):
 partial={};moves={};ambiguous_partial=set();ambiguous_moves=set()
 pa_pat=re.compile(r'\bdef\s+([A-Za-z_]\w*)\s*:\s*PartialAudit\s*:=\s*(.*?)(?=\n(?:theorem|def|end)\b|\Z)',re.S)
 mv_pat=re.compile(r'\bdef\s+([A-Za-z_]\w*)\s*:\s*Move\s*→\s*PartialAudit\s*:=\s*(.*?)(?=\n(?:theorem|def|end)\b|\Z)',re.S)
 for path in directory.glob('*.lean'):
  text=path.read_text()
  for m in pa_pat.finditer(text):add_definition(partial,ambiguous_partial,m.group(1),m.group(2))
  for m in mv_pat.finditer(text):add_definition(moves,ambiguous_moves,m.group(1),m.group(2))
 return partial,moves,ambiguous_partial,ambiguous_moves

def move_children(expr,defs,ambiguous,seen=None):
 if seen is None:seen=set()
 e=strip_outer(expr)
 if e.startswith('byPartialMove'):
  body=strip_outer(e[len('byPartialMove'):].strip())
  return split_args(bracket_content(body))
 name=e.split('.')[-1].strip()
 if name in ambiguous:raise ValueError('ambiguous Move -> PartialAudit alias '+name)
 if name in defs:
  if name in seen:raise ValueError('cyclic Move -> PartialAudit alias '+name)
  return move_children(defs[name],defs,ambiguous,seen|{name})
 raise ValueError('unresolved Move -> PartialAudit alias '+e[:120])

def extract(a,p,t,partial_defs,move_defs,ambiguous_partial,ambiguous_moves,seen=None):
 if seen is None:seen=set()
 a=strip_outer(a)
 if a=='.closed' or a.startswith('.closed '):return []
 if a=='.unresolved':return [(p,t)]
 m=re.fullmatch(r'\.split (\d+) (\([^)]*\)) (.*)',a,re.S)
 if m:
  n,slot,kids_expr=m.groups()
  k=re.fullmatch(r'\((\d+),(true|false)\)',slot);j=2*int(k[1])+(k[2]=='true');assert t[j]=='---'
  kids=move_children(kids_expr,move_defs,ambiguous_moves);res=[]
  for i in ORDER:
   u=t.copy();u[j]=MOVES[i]
   res+=extract(kids[i],f'(refine {p} {slot} (some {move(i)}))',u,partial_defs,move_defs,ambiguous_partial,ambiguous_moves,seen)
  return res
 name=a.split('.')[-1].strip()
 if re.fullmatch(r'[A-Za-z_]\w*',name):
  if name in ambiguous_partial:raise ValueError('ambiguous PartialAudit alias '+name)
  if name in partial_defs:
   if name in seen:raise ValueError('cyclic PartialAudit alias '+name)
   return extract(partial_defs[name],p,t,partial_defs,move_defs,ambiguous_partial,ambiguous_moves,seen|{name})
 raise ValueError('unsupported PartialAudit expression '+a[:160])
header='''import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
'''
partial_defs,move_defs,ambiguous_partial,ambiguous_moves=collect_definitions(src)
mod=f'Raw122Roster{branch:02}';all_leaves=[];kid_leaves=[];roots=[]
for k in range(24):
 nm=f'Raw122Kid{branch:02}_{k:02}';s=(src/(nm+'.lean')).read_text();m=re.search(r'def (kid\d+_\d+) : PartialAudit := (.*?)\ntheorem \1_checked : partialCheck 7014 (.*?) \1 = true := by',s,re.S);assert m,nm
 kid,audit,root=m.groups();root=root.replace("(child ","(BB6.Agent43Raw122.child ");t=PARENT.copy();t[11]=MOVES[branch];sl=re.search(r'\) \((\d+),(true|false)\) \(some',root);j=2*int(sl[1])+(sl[2]=='true');t[j]=MOVES[k];roots.append(root)
 leaves=extract(audit,root,t,partial_defs,move_defs,ambiguous_partial,ambiguous_moves);ls=[];lines=[]
 for p,tab in leaves:
  i=len(all_leaves);decl=f'p{branch:02}_{i:03}';all_leaves.append((decl,''.join(tab)));ls.append(decl)
  lines+=[f'def {decl} : PartialMachine := {literal(tab)}',f'theorem {decl}_eq : {p} = {decl} := by\n  funext s\n  rcases s with ⟨q,b⟩\n  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl']
 kid_leaves.append(ls)
 lines.append(f'theorem {kid}_roster : (partialResiduals {root} {kid}).map Prod.snd = [{",".join(ls)}] := by')
 if leaves:
  lines.append(f'  calc\n    _ = [{",".join(p for p,_ in leaves)}] := rfl\n    _ = _ := by rw [{",".join(x+"_eq" for x in ls)}]')
 else:lines.append('  rfl')
 name=mod+f'Kid{k:02}';(out/(name+'.lean')).write_text(f'import {nm}\n'+header+'\n'.join(lines)+'\nend BB6.Agent43Raw122Roster\n')
lines=[]
for k,ls in enumerate(kid_leaves):
 kid=f'kid{branch:02}_{k:02}';lines.append(f'theorem {kid}_good (C : Nat) (h : ∀ p ∈ [{",".join(ls)}], Covered C p) : Good C {roots[k]} {kid} := good_roster {kid}_roster h')
ps=','.join(x[0] for x in all_leaves);tag=f'{branch:02}';child=f'(BB6.Agent43Raw122.child {move(branch)})'
lines+= [f'def tables{tag} : List PartialMachine := [{ps}]',f'theorem kids{tag}_good (C : Nat) (h : ∀ p ∈ tables{tag}, Covered C p) (mv : Move) : Good C (refine {child} ({j//2},{str(bool(j%2)).lower()}) (some mv)) (kids{tag} mv) := by', '  rcases mv with ⟨w,r,q⟩','  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega','  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl','  all_goals cases w <;> cases r']
for i in ORDER:
 kid=f'kid{tag}_{i:02}';ls=kid_leaves[i]
 lines.append(f'  · apply {kid}_good C\n    intro p hp')
 if ls:lines.append(f'    apply h\n    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp\n    rcases hp with '+('|' .join('rfl' for _ in ls) if len(ls)>1 else 'rfl')+' <;> simp [tables'+tag+']')
 else:lines.append('    simp at hp')
lines += [f'theorem cover{tag} (C : Nat) (hC : 7014 ≤ C) (h : ∀ p ∈ tables{tag}, Covered C p) : Covered C {child} := by',f'  apply cover_of_good (p := {child}) (a := branch{tag}) hC (by decide) (weightedTNFNoAssignedHalt_refine BB6.Agent43Raw122.parent (5,true) _ BB6.Agent43Raw122.parent_nohalt) branch{tag}_checked',f'  exact good_split (kids{tag}_good C h)',f'#print axioms cover{tag}']
(out/(mod+'.lean')).write_text(f'import Raw122Branch{tag}\n'+''.join(f'import {mod}Kid{k:02}\n' for k in range(24))+header+'\n'.join(lines)+'\nend BB6.Agent43Raw122Roster\n')
(out/(mod+'.tsv')).write_text(''.join(f'{p}\t{t}\n' for p,t in all_leaves));print(mod,len(all_leaves))
