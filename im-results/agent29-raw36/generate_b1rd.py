"""Generate the exact canonical Raw36 D1=1LB/B1=0RD cover at bound 85."""
import argparse,json,subprocess,sys
from collections import Counter
from itertools import product
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent31-three-hole-tnf'))
from generate_four_hole import masks,slot,move,refine,parse
MOVES=[w+d+q for w,d,q in product('01','LR','ABCDEF')]
B=85
P='1RB---_1RC0RD_0RD---_0LD1LB_------_------'
NS='BB6.Agent29Raw36B1RD'
OPEN_NS=NS+'Sweep'
HEAD='''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36B1RD
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent29CanonicalFast BB6.Agent29FastZipWeight BB6.Agent29Raw36
open BB6.Agent19CanonicalPartial
'''
END='\nend BB6.Agent29Raw36B1RD\n'
BASE='''abbrev rd : PartialMachine := refine d1 (1,true) (some ⟨false,true,3⟩)
abbrev rdChild (mv : Move) : PartialMachine := refine rd (2,true) (some mv)
theorem rd_root : rd initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem rd_nohalt : weightedTNFNoAssignedHalt rd :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt)
theorem rd_support : TNFSupport rd 4 := supportOK_sound _ _ (by decide)
theorem rdChild_root (mv : Move) : rdChild mv initialSlot = some (some ⟨true,true,1⟩) :=
  refine_preserves_firstOne rd (2,true) (some mv) (by decide) rd_root
theorem rdChild_nohalt (mv : Move) : weightedTNFNoAssignedHalt (rdChild mv) :=
  weightedTNFNoAssignedHalt_refine _ _ _ rd_nohalt
'''
def farterm(p,code):
 rev=int(code[0]);dfa=[int(x,36) for x in code[1:]];d,D,L,R,z=masks(p,rev,dfa)
 return f'.far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩'
def size(t):return 1+sum(size(k) for k in t[3]) if t[0]=='split' else 1

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,default=ROOT);ap.add_argument('--limit',type=int,default=300);ap.add_argument('--tree',type=Path);a=ap.parse_args();out=a.out;out.mkdir(parents=True,exist_ok=True)
 far={parse(p):code for p,code in (l.split() for l in (ROOT/'b1-9-recovered.tsv').read_text().splitlines())}
 sweeps={parse(rec[1]):rec[0] for rec in map(json.loads,(ROOT/'b1-9-sweeps.jsonl').read_text().splitlines())}
 assert len(far)==8 and len(sweeps)==2 and not set(far)&set(sweeps)
 subprocess.run([sys.executable,str(ROOT.parent/'agent7-raw49'/'emit_sweep_recipes.py'),str(ROOT/'b1-9-sweeps.jsonl'),OPEN_NS,str(out/'Raw36B1RDSweeps.lean')],check=True)
 got=json.loads(a.tree.read_text() if a.tree else subprocess.check_output(['node',str(ROOT/'canonical_search.cjs'),P,'4','tree'],text=True))
 assert got['parent']==P and got['cut']==4 and got['stats']['score']==B and got['stats']['open']==5 and got['stats']['nodes']==57565
 used={}
 def render(p,c,t):
  tag,*x=t
  if tag=='skip':raise AssertionError('unexpected retained skip')
  if tag=='cycle':e,k,r,b=x;return f'.cycle {e} {k} {str(r).lower()} ({b})'
  if tag=='last':n,s=x;return f'.last {n} {slot(s)}'
  if tag=='far':return farterm(p,x[0])
  if tag=='open':
   assert p==parse(x[0]) and p not in used
   if p in far:used[p]='FAR';return farterm(p,far[p])
   assert p in sweeps,(p,x);used[p]='sweep';ns=f'{OPEN_NS}.M{sweeps[p]}';return f'.proven {ns}.table {ns}.never'
  assert tag=='split';n,s,kids=x;assert len(kids)==24 and p[s]=='---' and s//2<c
  return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(render(refine(p,s,mv),max(c,i%6+1),k) if i%6<=c else '.last 0 (0,false)' for i,(mv,k) in enumerate(zip(MOVES,kids)))+'])'
 def module(i,t):
  nm=f'rdKid{i:02d}';body=[];counter=0
  def emit(p,c,t,pexpr,name=None):
   nonlocal counter
   if name is None:counter+=1;name=f'{nm}_part{counter}'
   if size(t)<=a.limit:
    body.append(f'def {name} : Audit := {render(p,c,t)}\ntheorem {name}_checked : BB6.Agent29CanonicalFast.check {B} {pexpr} {c} {name} = true := by rfl\n');return name
   assert t[0]=='split';_,n,s,kids=t;assert len(kids)==24 and p[s]=='---' and s//2<c
   terms=[];proofs=[]
   for j,(mv,k) in enumerate(zip(MOVES,kids)):
    if j%6>c:
     assert k==['skip'];terms.append('(.last 0 (0,false))');proofs.append('(by rfl)');continue
    pc=f'(refine {pexpr} {slot(s)} (some {move(mv)}))';cn=emit(refine(p,s,mv),max(c,j%6+1),k,pc);terms.append(cn);proofs.append(cn+'_checked')
   xs='['+','.join(terms)+']'
   body.append(f'def {name} : Audit := .split {n} {slot(s)} (byMove {xs})\ntheorem {name}_checked : BB6.Agent29CanonicalFast.check {B} {pexpr} {c} {name} = true :=\n  split24 {B} {pexpr} {c} {n} {slot(s)} {xs} (by rfl)\n    '+'\n    '.join(proofs)+'\n');return name
  c=max(4,i%6+1);mv=move(MOVES[i]);pexpr=f'(rdChild {mv})';emit(refine(parse(P),5,MOVES[i]),c,t,pexpr,nm)
  body.append(f'theorem {nm}_bound : ∀ m, compatible {pexpr} m → WeightedBound {B} m :=\n  BB6.Agent29CanonicalFast.bound {B} {pexpr} {c} {nm} (by decide) (supportOK_sound _ _ (by decide)) (rdChild_root {mv}) (rdChild_nohalt {mv}) {nm}_checked\n#print axioms {nm}_bound\n')
  (out/f'Raw36RDKid{i:02d}.lean').write_text('import Raw36B1RDBase\nimport Raw36B1RDSweeps\n'+HEAD+'\n'.join(body)+END)
  print(nm,size(t),counter,flush=True)
 (out/'Raw36B1RDBase.lean').write_text('import CanonicalFastAudit\nimport Raw36Cut\n'+HEAD+BASE+END)
 assert got['tree'][:3]==['split',9,5]
 terms=[];proofs=[];imports=[]
 for i,t in enumerate(got['tree'][3]):
  if i%6>4:assert t==['skip'];terms.append('(.last 0 (0,false))');proofs.append('(by rfl)');continue
  module(i,t);terms.append(f'rdKid{i:02d}');proofs.append(f'rdKid{i:02d}_checked');imports.append(f'import Raw36RDKid{i:02d}\n')
 assert set(used)=={parse(p) for p in got['opens']} and Counter(used.values())=={'FAR':4,'sweep':1}
 xs='['+','.join(terms)+']';body=f'''def rdAudit : Audit := .split 9 (2,true) (byMove {xs})
theorem rdAudit_checked : BB6.Agent29CanonicalFast.check {B} rd 4 rdAudit = true :=
  split24 {B} rd 4 9 (2,true) {xs} (by rfl)
    '''+'\n    '.join(proofs)+f'''
theorem rd_bound : ∀ m, compatible rd m → WeightedBound {B} m :=
  BB6.Agent29CanonicalFast.bound {B} rd 4 rdAudit (by decide) rd_support rd_root rd_nohalt rdAudit_checked
theorem rd_cover : Cover (WeightedBound {B}) rd := Cover.leaf rd_bound
#print axioms rd_bound
#print axioms rd_cover
'''
 (out/'Raw36B1RD.lean').write_text(''.join(imports)+HEAD+body+END)
 print('COMPLETE OPEN MATCHES',dict(Counter(used.values())),flush=True)
if __name__=='__main__':main()
