"""Emit a full canonical proof tree with bounded-size kernel check subtrees."""
import json,sys
from pathlib import Path
from generate_two import far,refine,mv,slot,show,support,T
folder=Path(sys.argv[1]); name=sys.argv[2]; B=int(sys.argv[3]); spec=sys.argv[4].replace('_',''); a=tuple(-1 if spec[i]=='-' else int(spec[i])*12+6*(spec[i+1]=='R')+ord(spec[i+2])-65 for i in range(0,36,3)); tree=json.loads((folder/'tree.json').read_text()); opens=(folder/'open.txt').read_text().splitlines(); certs=dict((int(i),code) for i,code in (l.split() for l in (folder/'far.txt').read_text().splitlines())); holdouts={'Raw41LC0LB':{29:'.closed (.proven LC0LB.table LC0LB.never)'},'Raw41LB0LC':{3:'.closed (.proven LB0LC3.table LB0LC3.never)',34:'.closed (.proven LB0LC34.table LB0LC34.never)',42:'.closed (.proven LB0LC42.table LB0LC42.never)'},'Raw41LC0RA':{0:'.closed (.proven LC0RA0.table LC0RA0.never)',1:'.closed (.proven LC0RA2.table LC0RA2.never)',2:'.closed (.proven LC0RA2New.table LC0RA2New.never)'},'Raw41LC1LB':{1:'.closed (.proven (LC1LBPair.table false) (LC1LBPair.never false))',2:'.closed (.proven (LC1LBPair.table true) (LC1LBPair.never true))',7:'.closed (.proven LC1LB7.table LC1LB7.never)'}}.get(name,{})
assert set(certs).isdisjoint(holdouts) and set(certs)|set(holdouts)==set(range(len(opens)))
index=0
header='''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent19CanonicalPartial BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster
'''
end='\nend BB6.Agent47Raw41\n'
imports={'Raw41LC0LB':['Raw41LC0LBSweep'],'Raw41LB0LC':['Raw41LB0LCCounter3','Raw41LB0LCSweep34','Raw41LB0LCSweep42'],'Raw41LC0RA':['Raw41LC0RAGrammar0','Raw41LC0RASweep2','Raw41LC0RACounter2'],'Raw41LC1LB':['Raw41LC1LBSweepPair','Raw41LC1LBSweep7']}.get(name,[])
expr={'Raw41LC0LB':'refine (child ⟨false,false,2⟩) (2,true) (some ⟨false,false,1⟩)','Raw41LB0LC':'refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)','Raw41LC0RA':'refine (child ⟨false,false,2⟩) (2,true) (some ⟨false,true,0⟩)'}.get(name)
if expr is None:
 q=[i for i in range(12) if i!=1 and T[i]<0 and a[i]>=0]
 assert len(q)==1 and all(a[i]==T[i] for i in range(12) if i not in [1,q[0]])
 expr=f'refine (child {mv(a[1])}) {slot(q[0])} (some {mv(a[q[0]])})'
base='import Raw41CanonicalCut\n'+''.join(f'import {m}\n' for m in imports)+header+f'abbrev {name}_p : PartialMachine := {expr}\n'+end
Path(name+'Base.lean').write_text(base)
def size(t):return 1+sum(size(x) for x in t[3]) if t[0]=='split' else 1

def proof_tree(t,p):
 global index
 kind=t[0]
 if kind=='alias':return '.unresolved'
 if kind=='cycle':return f'.closed (.cycle {t[1]} {t[2]} {str(t[3]).lower()} ({t[4]}))'
 if kind=='last':return f'.closed (.last {t[1]} {slot(t[2])})'
 if kind=='open':
  i=index;index+=1;assert opens[i]==t[1]==show(p)
  if i in holdouts:return holdouts[i]
  return '.closed ('+far(certs[i],p)+')'
 if kind=='split':return f'.split {t[1]} {slot(t[2])} (byPartialMove [\n'+',\n'.join(proof_tree(x,refine(p,t[2],i)) for i,x in enumerate(t[3]))+'])'
 raise ValueError(t)

def emit(t,p,expr,id,parts,depth=0):
 n=f'{name}_{id}';pt=n+'_p';parts.append(f'abbrev {pt} : PartialMachine := {expr}\n'); c=support(p)
 if t[0]=='split' and size(t)>72:
  step,s=t[1:3]; cs=[emit(x,refine(p,s,i),f'refine {pt} {slot(s)} (some {mv(i)})',id+f'_{i:02}',parts,depth+1) for i,x in enumerate(t[3])];parts.append(f'def {n} : PartialAudit := .split {step} {slot(s)} (byPartialMove [{",".join(cs)}])\n')
  parts.append(f'''theorem {n}_checked : canonicalCheck {B} {pt} {c} {n} = true := by
  rw [{n},canonicalCheck]
  simp only [Bool.and_eq_true]
  refine ⟨by decide +kernel,allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
''')
  for q in range(6):
   for w,r in [(0,0),(0,1),(1,0),(1,1)]:
    i=12*w+6*r+q;parts.append('  · '+('rfl' if q>c else f'exact {cs[i]}_checked')+'\n')
 else:
  parts.append(f'def {n} : PartialAudit := {proof_tree(t,p)}\ntheorem {n}_checked : canonicalCheck {B} {pt} {c} {n} = true := by decide +kernel\n')
 return n

assert tree[0]=='split'; step,s=tree[1:3]; cs=[]
for i,x in enumerate(tree[3]):
 parts=[f'import {name}Base\n',header];cs.append(emit(x,refine(a,s,i),f'refine {name}_p {slot(s)} (some {mv(i)})',f'branch{i:02}',parts));Path(f'{name}Branch{i:02}.lean').write_text(''.join(parts)+end)
assert index==len(opens)
parts=[f'import {name}Branch{i:02}\n' for i in range(24)]+[header];c=support(a);n=name+'_tree';pt=name+'_p'
parts.append(f'def {n} : PartialAudit := .split {step} {slot(s)} (byPartialMove [{",".join(cs)}])\n')
parts.append(f'''theorem {n}_checked : canonicalCheck {B} {pt} {c} {n} = true := by
  rw [{n},canonicalCheck]
  simp only [Bool.and_eq_true]
  refine ⟨by decide +kernel,allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
''')
for q in range(6):
 for w,r in [(0,0),(0,1),(1,0),(1,1)]:
  i=12*w+6*r+q;parts.append('  · '+('rfl' if q>c else f'exact {cs[i]}_checked')+'\n')
parts.append(f'''
theorem {name}_empty : canonicalResiduals {pt} {c} {n} = [] := by decide +kernel

theorem {name}_bound (m : Machine) (hm : TNFQuotientCompatible {pt} m) : WeightedBound {B} m := by
  have hf : {pt} initialSlot = some (some ⟨true,true,1⟩) := by decide
  have hno : weightedTNFNoAssignedHalt {pt} :=
    weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt)
  have hs : TNFSupport {pt} {c} := supportOK_sound _ _ (by decide)
  rcases canonicalSound {B} {pt} {c} {n} (by decide) hs hf hno {n}_checked m hm with hb | ⟨e,he,_⟩
  · exact hb
  · rw [{name}_empty] at he
    exact False.elim (List.not_mem_nil he)

#print axioms {name}_bound
''');Path(name+'Closed.lean').write_text(''.join(parts)+end)
print('generated',name,'branches',len(cs),'holdouts',len(holdouts),'FAR',len(certs))
