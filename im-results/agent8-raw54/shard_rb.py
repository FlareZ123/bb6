#!/usr/bin/env python3
"""Shard the complete generated RB audit without changing its leaves. Run once after generate_rb.py."""
import re,pathlib,argparse
ROOT=pathlib.Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description="Split generated Raw54 RB audit into kernel-checked subtrees")
parser.add_argument("--directory",type=pathlib.Path,default=ROOT)
parser.add_argument("--threshold",type=int,default=50)
args=parser.parse_args()
D=ORIGINAL=args.directory
HEADER='''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit
'''
MOVES=[f'⟨{str(w).lower()},{str(r).lower()},{q}⟩' for w in [False,True] for r in [False,True] for q in range(6)]
ORDER=[12*w+6*r+q for q in range(6) for w in range(2) for r in range(2)]
THRESHOLD=args.threshold
assert THRESHOLD>0
class Node:
 def __init__(self,text,children=(),n=None,s=None):self.text=text;self.children=children;self.n=n;self.s=s;self.size=sum(c.size for c in children) if children else 1

def parse(t,i=0):
 while t[i].isspace():i+=1
 start=i
 m=re.match(r'\.split (\d+) (\(\d+,(?:true|false)\)) \(byMove \[',t[i:])
 if m:
  i+=m.end();children=[]
  for k in range(24):
   c,i=parse(t,i);children.append(c)
   while t[i].isspace():i+=1
   if k!=23:assert t[i]==',',(i,t[i:i+50]);i+=1
  assert t[i:i+2]=='])',(i,t[i:i+20]);i+=2
  return Node(t[start:i],children,m[1],m[2]),i
 # all leaves one line (commas inside structures/arrays not delimiters)
 depth=0
 while i<len(t):
  a=t[i]
  if depth==0 and a in ',\n]':break
  if a in '([⟨':depth+=1
  elif a in ')]⟩':depth-=1
  i+=1
 assert depth==0,(start,i,t[start:i]);return Node(t[start:i].strip()),i

def write(name,imports,body):
 (D/(name+'.lean')).write_text(''.join('import '+m+'\n' for m in sorted(set(imports)))+HEADER+body+'\nend BB6.Agent8Raw54.RB\n')

def checked(name,table,expr):
 return f'''theorem {name}_checked : zipCheck 7014 ({table}) {expr} = true := by
  rw [← checkAt_eq 7014 ({table}) {expr} 0 start rfl]
  decide
'''

def emit(node,table,name,baseimports):
 # large splits get their own module; small branches are grouped in current module.
 assert node.children
 imports=list(baseimports);parts=[];childexpr=[]
 for j,c in enumerate(node.children):
  cn=f'{name}_{j:02d}';p=f'refine ({table}) {node.s} (some {MOVES[j]})'
  if c.size>THRESHOLD:
   imports.append(emit(c,p,cn,baseimports));childexpr.append(cn)
  else:
   parts.append(f'def {cn} : Audit := {c.text}\n'+checked(cn,p,cn));childexpr.append(cn)
 parts.append(f'def {name} : Audit := .split {node.n} {node.s} (byMove [{", ".join(childexpr)}])\n')
 parts.append(f'''theorem {name}_checked : zipCheck 7014 ({table}) {name} = true := by
  change (zipQueryOK 7014 ({table}) {node.n} {node.s} && allMoves (fun mv => zipCheck 7014 (refine ({table}) {node.s} (some mv)) (byMove [{", ".join(childexpr)}] mv))) = true
  simp only [Bool.and_eq_true]
  refine ⟨by decide, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
'''+''.join(f'  · exact {childexpr[j]}_checked\n' for j in ORDER))
 mod='Raw54RBShard'+name.removeprefix('rbShard').replace('_','X');write(mod,imports,'\n'.join(parts));return mod

for k in range(24):
 name=f'Raw54RBKid{k:02d}';p=ORIGINAL/(name+'.lean');source=p.read_text()
 if len(source)<2000:continue
 imports=re.findall(r'^import (\S+)',source,re.M)
 term=source.split(' : PartialAudit := .closed (',1)[1].split('\ntheorem kid',1)[0];node,i=parse(term);assert term[i:].strip()==')',(name,term[i:i+50]);table=f'refine parent (2,true) (some {MOVES[k]})';nm=f'rbShard{k:02d}'
 mod=emit(node,table,nm,imports)
 write(name,[mod],f'''def kid{k:02d} : PartialAudit := .closed {nm}
theorem kid{k:02d}_checked : partialCheck 7014 ({table}) kid{k:02d} = true := {nm}_checked
''')
 print(name,node.size,mod)
