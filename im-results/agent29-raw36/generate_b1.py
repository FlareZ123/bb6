"""Generate source-exact closed canonical B1 descendant audit from literal evidence."""
import argparse,base64,gzip,json,subprocess,sys
from collections import Counter
from itertools import product
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent31-three-hole-tnf'))
from generate_four_hole import masks,slot,move,refine,parse
from regex_to_dfa import inv
from emit_regular import emit
MOVES=[w+d+q for w,d,q in product('01','LR','ABCDEF')]
def header(ns):
 return f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent29CanonicalFast BB6.Agent29FastZipWeight BB6.Agent29Raw36
open BB6.Agent19CanonicalPartial
'''

def base(index,cut,n,s):
 return f'''abbrev b1 : PartialMachine := refine d1 (1,true) (some {move(MOVES[index])})
abbrev b1Child (mv : Move) : PartialMachine := refine b1 {slot(s)} (some mv)
theorem b1_root : b1 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem b1_nohalt : weightedTNFNoAssignedHalt b1 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt)
theorem b1_support : TNFSupport b1 {cut} := supportOK_sound _ _ (by decide)
theorem b1Child_root (mv : Move) : b1Child mv initialSlot = some (some ⟨true,true,1⟩) :=
  refine_preserves_firstOne b1 {slot(s)} (some mv) (by decide) b1_root
theorem b1Child_nohalt (mv : Move) : weightedTNFNoAssignedHalt (b1Child mv) :=
  weightedTNFNoAssignedHalt_refine _ _ _ b1_nohalt
'''
def farterm(p,code):
 rev=int(code[0]);dfa=[int(x,36) for x in code[1:]];d,D,L,R,z=masks(p,rev,dfa)
 return f'.far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩'
def size(t):return 1+sum(size(k) for k in t[3]) if t[0]=='split' else 1

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('index',type=int);ap.add_argument('--out',type=Path,default=ROOT);ap.add_argument('--limit',type=int,default=300);ap.add_argument('--tree',type=Path);a=ap.parse_args();out=a.out;out.mkdir(parents=True,exist_ok=True)
 i=a.index;assert i in [1,4,6,7,8,9,10,12,13,14,16,18,20,22]
 stem=f'Raw36B1{i:02d}';NS=f'BB6.Agent29{stem}';OPEN_NS=NS+'Sweep';HEAD=header(NS);END=f'\nend {NS}\n'
 P='1RB---_1RC'+MOVES[i]+'_0RD---_0LD1LB_------_------';cut=max(4,i%6+1)
 evidence=json.loads(gzip.decompress(base64.b64decode((ROOT/f'd1-{i:02d}-evidence.json.gz.b64').read_text())))
 far={parse(t):code for t,code in evidence['far']};records=evidence['sweep'];sweeps={parse(rec[1]):rec[0] for rec in records};manual={parse(t):ns for t,ns in evidence.get('manual',[])}
 cycles={parse(t):a for t,a in evidence.get('cycle',[])}
 assert not evidence.get('missing'),evidence.get('missing')
 regular={parse(t):j for j,(t,L,R) in enumerate(evidence.get('regular',[]))}
 allsets=[set(far),set(sweeps),set(manual),set(cycles),set(regular)];assert sum(map(len,allsets))==len(set().union(*allsets))
 manual_imports=''.join(f'import {ns.removeprefix("BB6.Agent29")}\n' for ns in sorted(set(manual.values())))
 assert len(far)==len(evidence['far']) and len(sweeps)==len(records) and not set(far)&set(sweeps) and not (set(far)|set(sweeps))&set(manual)
 if 'BB6.Agent29Raw36B1LBCycle' in manual.values():
  from emit_phase0lb import generate
  generate(out/'Raw36B1LBCycle.lean')
 regular_imports=''
 for j,(t,L,R) in enumerate(evidence.get('regular',[])):
  I=inv(t,L,R);assert I,(t,'not closed')
  mod=f'{stem}Regular{j:02d}'
  (out/f'{mod}.lean').write_text('import ChunkRegularRay\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'+emit(j,t,L,R,I,NS+'Regular'))
  regular_imports+=f'import {mod}\n'
 inp=out/f'{stem}SweepRecipes.jsonl';inp.write_text(''.join(json.dumps(r)+'\n' for r in records))
 subprocess.run([sys.executable,str(ROOT.parent/'agent7-raw49'/'emit_sweep_recipes.py'),str(inp),OPEN_NS,str(out/f'{stem}Sweeps.lean')],check=True)
 got=json.loads(a.tree.read_text() if a.tree else subprocess.check_output(['node',str(ROOT/'canonical_search.cjs'),P,str(cut),'tree'],text=True))
 B=evidence['bound'];assert got['parent']==P and got['cut']==cut and got['stats']['score']<=B
 assert {parse(t) for t in got['opens']}==set(far)|set(sweeps)|set(manual)|set(cycles)|set(regular)
 tag,n,s,kids=got['tree'];assert tag=='split' and len(kids)==24
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
   if p in regular:
    used[p]='regular';ns=f'{NS}Regular.M{regular[p]}';return f'.proven {ns}.table {ns}.never'
   if p in cycles:
    used[p]='late-cycle';e,k,r,b=cycles[p];return f'.cycle {e} {k} {str(r).lower()} ({b})'
   if p in manual:used[p]='manual';ns=manual[p];return f'.proven {ns}.table {ns}.never'
   assert p in sweeps,(p,x);used[p]='sweep';ns=f'{OPEN_NS}.M{sweeps[p]}';return f'.proven {ns}.table {ns}.never'
  assert tag=='split';n,s,kids=x;assert len(kids)==24 and p[s]=='---' and s//2<c
  return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(render(refine(p,s,mv),max(c,i%6+1),k) if i%6<=c else '.last 0 (0,false)' for i,(mv,k) in enumerate(zip(MOVES,kids)))+'])'
 def module(i,t):
  nm=f'kid{i:02d}';body=[];counter=0
  def emit(p,c,t,pexpr,name=None):
   nonlocal counter
   if name is None:counter+=1;name=f'{nm}_part{counter}'
   if size(t)<=a.limit:
    body.append(f'def {name} : Audit := {render(p,c,t)}\ntheorem {name}_checked : BB6.Agent29CanonicalFast.check {B} {pexpr} {c} {name} = true := by rw [← BB6.Agent29CanonicalPrefix.prefixCheck_eq]; rfl\n');return name
   assert t[0]=='split';_,n,s,kids=t;assert len(kids)==24 and p[s]=='---' and s//2<c
   terms=[];proofs=[]
   for j,(mv,k) in enumerate(zip(MOVES,kids)):
    if j%6>c:
     assert k==['skip'];terms.append('(.last 0 (0,false))');proofs.append('(by rfl)');continue
    pc=f'(refine {pexpr} {slot(s)} (some {move(mv)}))';cn=emit(refine(p,s,mv),max(c,j%6+1),k,pc);terms.append(cn);proofs.append(cn+'_checked')
   xs='['+','.join(terms)+']'
   body.append(f'def {name} : Audit := .split {n} {slot(s)} (byMove {xs})\ntheorem {name}_checked : BB6.Agent29CanonicalFast.check {B} {pexpr} {c} {name} = true :=\n  split24 {B} {pexpr} {c} {n} {slot(s)} {xs} (by rfl)\n    '+'\n    '.join(proofs)+'\n');return name
  c=max(cut,i%6+1);mv=move(MOVES[i]);pexpr=f'(b1Child {mv})';emit(refine(parse(P),s,MOVES[i]),c,t,pexpr,nm)
  body.append(f'theorem {nm}_bound : ∀ m, compatible {pexpr} m → WeightedBound {B} m :=\n  BB6.Agent29CanonicalFast.bound {B} {pexpr} {c} {nm} (by decide) (supportOK_sound _ _ (by decide)) (b1Child_root {mv}) (b1Child_nohalt {mv}) {nm}_checked\n#print axioms {nm}_bound\n')
  (out/f'{stem}Kid{i:02d}.lean').write_text(f'import {stem}Base\nimport {stem}Sweeps\n'+manual_imports+regular_imports+HEAD+'\n'.join(body)+END)
  print(nm,size(t),counter,flush=True)
 (out/f'{stem}Base.lean').write_text('import CanonicalPrefixFast\nimport Raw36Cut\n'+HEAD+base(a.index,cut,n,s)+END)
 terms=[];proofs=[];imports=[]
 for i,t in enumerate(got['tree'][3]):
  if i%6>cut:assert t==['skip'];terms.append('(.last 0 (0,false))');proofs.append('(by rfl)');continue
  module(i,t);terms.append(f'kid{i:02d}');proofs.append(f'kid{i:02d}_checked');imports.append(f'import {stem}Kid{i:02d}\n')
 assert set(used)=={parse(p) for p in got['opens']}
 xs='['+','.join(terms)+']';body=f'''def audit : Audit := .split {n} {slot(s)} (byMove {xs})
theorem audit_checked : BB6.Agent29CanonicalFast.check {B} b1 {cut} audit = true :=
  split24 {B} b1 {cut} {n} {slot(s)} {xs} (by rfl)
    '''+'\n    '.join(proofs)+f'''
theorem bound : ∀ m, compatible b1 m → WeightedBound {B} m :=
  BB6.Agent29CanonicalFast.bound {B} b1 {cut} audit (by decide) b1_support b1_root b1_nohalt audit_checked
theorem cover : Cover (WeightedBound {B}) b1 := Cover.leaf b1 bound
#print axioms bound
#print axioms cover
'''
 (out/f'{stem}.lean').write_text(''.join(imports)+HEAD+body+END)
 print('COMPLETE OPEN MATCHES',dict(Counter(used.values())),flush=True)
if __name__=='__main__':main()
