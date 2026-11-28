"""Emit independently kernel-checked two-ray DFA certificates."""
import json,sys,pathlib

def emit(idx,t,L,R,I,ns='BB6.Agent29Raw36Regular'):
 n=f'M{idx}';p=t.replace('_','');rows=[]
 for q in range(6):
  a=[[] for _ in L]
  for qq,l,r in I:
   if qq==q:a[l].append(r)
  rows.append('#['+','.join('['+','.join(map(str,sorted(s)))+']' for s in a)+']')
 tab=[]
 for j in range(12):
  a=p[3*j:3*j+3]
  if a=='---':continue
  tab.append(f'  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)')
 def pred(D):
  P=[[[],[]] for _ in D]
  for i,(a,b) in enumerate(D):P[a][0].append(i);P[b][1].append(i)
  if 0 not in P[0][0]:P[0][0].append(0)
  return '#['+','.join('(['+','.join(map(str,a))+'],['+','.join(map(str,b))+'])' for a,b in P)+']'
 def dfa(D):return '#['+','.join(f'({a},{b})' for a,b in D)+']'
 width=8;count=(len(L)+width-1)//width
 proofs=[]
 def conj(terms):return '⟨'+','.join(terms+['True.intro'])+'⟩'
 for q in range(6):
  names=[];exprs=[]
  for k in range(count):
   name=f'ch{q}_{k}';expr=f'checkBlock cert table {q} {k*width} {width}'
   proofs.append(f'theorem {name} : {expr} = true := by rfl')
   names.append(name);exprs.append(expr)
  expr='true'
  for v in reversed(exprs):expr=f'({v} && {expr})'
  proofs.append(f'theorem q{q} : blocks cert table {q} {width} {count} = true := by\n  change {expr} = true\n  simp only [Bool.and_eq_true]\n  exact '+conj(names))
 expr='true'
 for q in reversed(range(6)):expr=f'(blocks cert table {q} {width} {count} && {expr})'
 proofs.append(f'theorem allBlocks : (List.finRange 6).all (fun q => blocks cert table q {width} {count}) = true := by\n  change {expr} = true\n  simp only [Bool.and_eq_true]\n  exact '+conj([f'q{q}' for q in range(6)]))
 checks='\n'.join(proofs)
 return f'''namespace {ns}.{n}
open BB6Coverage BB6.Agent29FastRegularRay BB6.Agent29ChunkRegularRay

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
'''+ '\n'.join(tab)+f'''
  | _,_ => none

def cert : Certificate := ⟨⟨⟨{dfa(L)}⟩,⟨{dfa(R)}⟩,#[{','.join(rows)}]⟩,⟨{pred(L)}⟩,⟨{pred(R)}⟩⟩

{checks}
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  soundBlocks cert table {width} {count} (by decide) (by decide) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) allBlocks m hm
#print axioms never
end {ns}.{n}
'''
if __name__=='__main__':
 out=pathlib.Path(sys.argv[2]);out.mkdir(exist_ok=True,parents=True)
 for idx,row in enumerate(map(json.loads,open(sys.argv[1]))):
  i,t,L,R,I,stats=row
  if not I:continue
  ns=f'BB6.Agent29Raw36Regular{idx:02d}'
  (out/f'Raw36Regular{idx:02d}.lean').write_text('import ChunkRegularRay\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'+emit(0,t,L,R,I,ns).replace(ns+'.M0',ns))
