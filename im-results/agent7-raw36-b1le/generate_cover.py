"""Emit full B1=1LE canonical audit using exact-key evidence and existing soundness."""
import sys,json,hashlib,base64,lzma
from pathlib import Path
from itertools import product
from stack_candidates import generate
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent7-raw36-transfer'))
from emit import masks
sys.path.insert(0,str(ROOT.parent/'agent7-raw49'))
from emit_sweep_recipes import emit as emit_sweep, HEADER
MOVES=[w+d+q for w,d,q in product('01','LR','ABCDEF')]
NS='BB6.Agent29Raw36B116'; SWEEP='BB6.Agent7Raw36B1LESweep'; STEM='Raw36B116'
HEAD=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent29CanonicalFast BB6.Agent29FastZipWeight BB6.Agent29Raw36
open BB6.Agent19CanonicalPartial
'''
END=f'\nend {NS}\n'
def parse(s):return tuple(s.replace('_','')[i:i+3] for i in range(0,36,3))
def raw(p):return ''.join(p)
def refine(p,s,mv):return p[:s]+(mv,)+p[s+1:]
def slot(s):return f'({s//2},{str(bool(s%2)).lower()})'
def move(mv):return f'⟨{str(mv[0]=="1").lower()},{str(mv[1]=="R").lower()},{ord(mv[2])-65}⟩'
def farterm(p,code):
    rev,n,D,L,R,z=masks(code,raw(p));return f'.far {str(bool(rev)).lower()} {n} ⟨0,{D},{L},{R},{z}⟩'
def size(t):return 1+sum(map(size,t[3])) if t[0]=='split' else 1

def main(treefile,out,limit=300,index=16):
    global NS,SWEEP,STEM,HEAD,END
    STEM=f'Raw36B1{index:02d}';NS='BB6.Agent29'+STEM;SWEEP='BB6.Agent7'+STEM+'Sweep'
    HEAD=HEAD.replace('BB6.Agent29Raw36B116',NS);END=f'\nend {NS}\n'

    out=Path(out);out.mkdir(exist_ok=True,parents=True);got=json.loads(Path(treefile).read_text());fixture=json.loads(lzma.decompress(base64.b64decode((ROOT/('evidence.json.xz.b64' if index==16 else f'evidence{index:02d}.json.xz.b64')).read_text())))
    keys=sorted(t.replace('_','') for t in got['opens']);assert len(keys)==len(set(keys))==len(fixture['data'])
    assert hashlib.sha256('\n'.join(keys).encode()).hexdigest()==fixture['digest'];rows=list(zip(keys,fixture['data']));evidence=dict(rows);B=fixture['bound'];assert B>=got['stats']['score'];P=parse(got['parent']);cut=got['cut'];assert raw(P)=='1RB---1RC'+MOVES[index]+'0RD---0LD1LB------------' and cut==max(4,index%6+1)
    external=generate(rows,out,STEM,'BB6.Agent7'+STEM+'Automata')
    sw=[(i,t,v) for i,(t,v) in enumerate(rows) if v[0]=='s']
    for j in range(0,len(sw),4):
        name=f'{STEM}Sweep{j//4:02d}';ns=f'{SWEEP}{j//4:02d}';body=[]
        for i,t,v in sw[j:j+4]:
            body.append(emit_sweep([i,t,*v[1:]]));external[t]=(name,f'{ns}.M{i}')
        (out/(name+'.lean')).write_text(HEADER.format(ns=ns)+'\n\n'.join(body)+'\nend '+ns+'\n')
    tag,n,s,kids=got['tree'];assert tag=='split' and len(kids)==24
    base=f'''abbrev b1 : PartialMachine := refine d1 (1,true) (some {move(MOVES[index])})
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
    (out/(STEM+'Base.lean')).write_text('import CanonicalPrefixFast\nimport Raw36Cut\n'+HEAD+base+END)
    used=set()
    def module(i,t):
        nm=f'kid{i:02d}';body=[];counter=0;imports=set()
        def render(p,c,t):
            tag,*x=t
            if tag=='cycle':e,k,r,b=x;return f'.cycle {e} {k} {str(r).lower()} ({b})'
            if tag=='last':n,s=x;return f'.last {n} {slot(s)}'
            if tag=='far':return farterm(p,x[0])
            if tag=='open':
                k=raw(p);assert p==parse(x[0]) and k not in used;used.add(k);v=evidence[k]
                if v[0]=='f':return farterm(p,v[1])
                mod,ns=external[k];imports.add(mod);return f'.proven {ns}.table {ns}.never'
            assert tag=='split';n,s,kids=x;assert len(kids)==24 and p[s]=='---' and s//2<c
            return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(render(refine(p,s,mv),max(c,j%6+1),k) if j%6<=c else '.last 0 (0,false)' for j,(mv,k) in enumerate(zip(MOVES,kids)))+'])'
        def emit(p,c,t,pexpr,name=None):
            nonlocal counter
            if name is None:counter+=1;name=f'{nm}_part{counter}'
            if size(t)<=limit:
                body.append(f'def {name} : Audit := {render(p,c,t)}\ntheorem {name}_checked : BB6.Agent29CanonicalFast.check {B} {pexpr} {c} {name} = true := by rw [← BB6.Agent29CanonicalPrefix.prefixCheck_eq]; rfl\n');return name
            assert t[0]=='split';_,n,s,kids=t;assert len(kids)==24 and p[s]=='---' and s//2<c;terms=[];proofs=[]
            for j,(mv,k) in enumerate(zip(MOVES,kids)):
                if j%6>c:assert k==['skip'];terms.append('(.last 0 (0,false))');proofs.append('(by rfl)');continue
                pc=f'(refine {pexpr} {slot(s)} (some {move(mv)}))';cn=emit(refine(p,s,mv),max(c,j%6+1),k,pc);terms.append(cn);proofs.append(cn+'_checked')
            xs='['+','.join(terms)+']';body.append(f'def {name} : Audit := .split {n} {slot(s)} (byMove {xs})\ntheorem {name}_checked : BB6.Agent29CanonicalFast.check {B} {pexpr} {c} {name} = true :=\n  split24 {B} {pexpr} {c} {n} {slot(s)} {xs} (by rfl)\n    '+'\n    '.join(proofs)+'\n');return name
        c=max(cut,i%6+1);mv=move(MOVES[i]);pexpr=f'(b1Child {mv})';emit(refine(P,s,MOVES[i]),c,t,pexpr,nm)
        body.append(f'theorem {nm}_bound : ∀ m, compatible {pexpr} m → WeightedBound {B} m :=\n  BB6.Agent29CanonicalFast.bound {B} {pexpr} {c} {nm} (by decide) (supportOK_sound _ _ (by decide)) (b1Child_root {mv}) (b1Child_nohalt {mv}) {nm}_checked\n#print axioms {nm}_bound\n')
        (out/f'{STEM}Kid{i:02d}.lean').write_text(f'import {STEM}Base\n'+''.join(f'import {m}\n' for m in sorted(imports))+HEAD+'\n'.join(body)+END);print(nm,size(t),counter,flush=True)
    for i,t in enumerate(kids):
        if i%6>cut:assert t==['skip'];continue
        module(i,t)
    assert used==set(keys)
    names=[f'kid{i:02d}' if i%6<=cut else '(.last 0 (0,false))' for i in range(24)];xs='['+','.join(names)+']';proofs=[name+'_checked' if i%6<=cut else '(by rfl)' for i,name in enumerate(names)]
    body=f'''def audit : Audit := .split {n} {slot(s)} (byMove {xs})
theorem audit_checked : BB6.Agent29CanonicalFast.check {B} b1 {cut} audit = true :=
  split24 {B} b1 {cut} {n} {slot(s)} {xs} (by rfl)
    '''+'\n    '.join(proofs)+f'''
theorem bound : ∀ m, compatible b1 m → WeightedBound {B} m :=
  BB6.Agent29CanonicalFast.bound {B} b1 {cut} audit (by decide) b1_support b1_root b1_nohalt audit_checked
theorem cover : Cover (WeightedBound {B}) b1 := Cover.leaf b1 bound
#print axioms bound
#print axioms cover
'''
    (out/f'{STEM}.lean').write_text(''.join(f'import {STEM}Kid{i:02d}\n' for i in range(24) if i%6<=cut)+HEAD+body+END)
    print('complete exact OPEN match',len(used),flush=True)
if __name__=='__main__':main(sys.argv[1],sys.argv[2],int(sys.argv[3]) if len(sys.argv)>3 else 300,int(sys.argv[4]) if len(sys.argv)>4 else 16)
