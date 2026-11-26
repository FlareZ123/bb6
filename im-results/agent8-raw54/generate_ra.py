#!/usr/bin/env python3
"""Raw54 E1=0LE E0=0RA: deterministic complete audit source generation.
Discovery is untrusted; all source modules are checked by Lean's kernel.
The tighter bound 363 uses the original weighted-TNF score convention.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import argparse, hashlib, json, subprocess, sys, tempfile
ROOT = Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent31-three-hole-tnf'))
from generate_four_hole import masks,parse
sys.path.insert(0,str(ROOT.parent/'agent47-raw111-cut'))
from emit_sparse import emit as emit_ngram
PARENT='1RB---_1RC---_0RD---_1LD0LE_0RA0LE_------'
BOUND=363
MOVES=[w+d+q for w,d,q in product('01','LR','ABCDEF')]
ORDER=[12*w+6*r+q for q in range(6) for w in range(2) for r in range(2)]
NS='BB6.Agent8Raw54.RA'
HEADER=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit
'''
PROOFS={**{i:f'Raw54RACounter{i}' for i in (32,40,62,65,67,68,86,94,99)},**{i:f'Raw54RADigit{i}' for i in (1,88,93)},**{i:f'Raw54RARadix{i}' for i in (35,46,66)},11:'Raw54RATernary11',87:'Raw54RASpecial87'}
def sha(s):return hashlib.sha256(s).hexdigest()
def slot(s):return f'({s//2},{str(bool(s%2)).lower()})'
def move(a):return f'⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩'
def bits(xs):return '['+','.join(str(bool(x)).lower() for x in xs)+']'
def zrun(p,n):
    q,h,l,r=0,0,[],[]
    for _ in range(n):
        a=p[2*q+int(l[0] if l else False)];assert a!='---';w=int(a[0]);q=ord(a[2])-65
        if a[1]=='R':h+=1;l=[r[0] if r else 0,w]+l[1:];r=r[1:]
        else:h-=1;l=l[1:];r=[w]+r
    return f'⟨{q},{h},{bits(l)},{bits(r)}⟩'
def table(p):
    return 'fun s => match s.1.val,s.2 with\n'+''.join(f'  | {j//2},{str(bool(j%2)).lower()} => some (some {move(a)})\n' for j,a in enumerate(p) if a!='---')+'  | _,_ => none'
def write(root,name,imports,body):
    (root/(name+'.lean')).write_text(''.join('import '+m+'\n' for m in sorted(set(imports)))+HEADER+body+'\nend '+NS+'\n')
def refine(p,s,a):return p[:s]+(a,)+p[s+1:]
def all_moves(checks):
    return '''  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
'''+''.join(f'  · exact {checks[j]}\n' for j in ORDER)
def fuse_sparse(root,mod):
    paths=[root/(mod+'Data.lean'),*(root/(mod+f'Row{j:02}.lean') for j in range(12)),root/(mod+'.lean')]
    source=paths[0].read_text()
    for p in paths[1:]:source+=''.join(line for line in p.read_text().splitlines(keepends=True) if not line.startswith('import '))
    paths[-1].write_text(source)
    for p in paths[:-1]:p.unlink()

def collect(work,root):
    t=json.loads((work/'tree.json').read_text());raw=(work/'open.txt').read_bytes()
    assert sha(raw)=='88dcd075890d03f76639d093d581673f2ef459e19772baf2858d839ccf137ff2'
    rows=raw.decode().splitlines();assert len(rows)==len(set(rows))==1665
    found={int(i):v for i,v in (line.split(':') for line in (work/'far.txt').read_text().splitlines())};assert len(found)==1563
    misses=[s for j,s in enumerate(rows) if j not in found];assert len(misses)==102
    assert sha(('\n'.join(misses)+'\n').encode())=='674fa7cdf69a3eadcf1e1d30839129c6e2fd641216ec4da62a34cf8464404edb'
    mutated={int(i):v for i,v in (line.split(':') for line in (root/'ra-mutated.txt').read_text().splitlines())};assert len(mutated)==84
    assert set(mutated).isdisjoint(PROOFS) and set(mutated)|set(PROOFS)|{9}==set(range(102))
    far={rows[j]:c for j,c in found.items()};far.update({misses[j]:c for j,c in mutated.items()});certs={};deps={}
    for row,code in far.items():
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,36) for c in code[1:]])
        certs[row]=f'.far {str(code[0]=="1").lower()} {d} ⟨0,{D},{L},{R},{z}⟩'
    for i,mod in PROOFS.items():
        ns=f'BB6.Agent8Raw54.RA.M{i}';certs[misses[i]]=f'.proven {ns}.table {ns}.never';deps[misses[i]]=mod
    ident,data=(work/'n9.txt').read_text().strip().split(maxsplit=1);assert int(ident)==9
    _,_,L,R,_=data.split()
    edges=lambda s:sum(int(a.split(':')[1]).bit_count() for a in s.rstrip(',').split(','))
    mod,ns=emit_ngram(root,9,misses[9],data,width=6,module_name='Raw54RASparse9',expected=(152,edges(L),edges(R)))
    fuse_sparse(root,mod);certs[misses[9]]=f'.proven {ns}.table {ns}.never';deps[misses[9]]=mod
    assert set(certs)==set(rows)
    return t,certs,deps

class Node:
    def __init__(self,t,certs,deps,stats):
        tag,*v=t;stats[tag]+=1;self.tag=tag;self.children=[];self.deps=set();self.size=1
        if tag=='cycle':e,k,r,b=v;self.text=f'.cycle {e} {k} {str(r).lower()} ({b})'
        elif tag=='last':n,s=v;self.text=f'.last {n} {slot(s)}'
        elif tag=='open':
            self.text=certs[v[0]]
            if v[0] in deps:self.deps.add(deps[v[0]])
        else:
            assert tag=='split';self.n,self.s,kids=v;self.children=[Node(k,certs,deps,stats) for k in kids]
            self.size=sum(c.size for c in self.children);self.deps=set().union(*(c.deps for c in self.children))
    def term(self):
        if not self.children:return self.text
        return f'.split {self.n} {slot(self.s)} (byMove [\n'+',\n'.join(c.term() for c in self.children)+'])'

def emit_tree(root,node,p,expr,name,t=0,threshold=50):
    # p is the exact discovered table; expr is the corresponding original Lean
    # refine chain. Each shard is reduced from an exact checked prefix.
    mod='Raw54RAShard'+name.removeprefix('ra').replace('_','X')
    imports={'Raw54RABase'};body=[]
    if node.size<=threshold or not node.children:
        imports.update(node.deps)
        body += [f'def {name} : Audit := {node.term()}']
        # The literal table is definitionally equivalent on the 12 slots;
        # prove equality with the existing finite table checker before use.
        body += [f'def {name}Table : PartialMachine := {table(p)}',
            f'theorem {name}Table_eq : {name}Table = ({expr}) := tableOK_sound _ _ (by decide)',
            f'def {name}Prefix : Z := {zrun(p,t)}',
            f'theorem {name}_checked : zipCheck {BOUND} ({expr}) {name} = true := by',
            f'  rw [← {name}Table_eq, ← checkAt_eq {BOUND} {name}Table {name} {t} {name}Prefix (by rfl)]',
            '  decide']
    else:
        sub=[];checks=[]
        for j,c in enumerate(node.children):
            cn=f'{name}_{j:02d}';p2=refine(p,node.s,MOVES[j]);e2=f'refine ({expr}) {slot(node.s)} (some {move(MOVES[j])})'
            if c.size>threshold:
                imports.add(emit_tree(root,c,p2,e2,cn,node.n,threshold));sub.append(cn);checks.append(cn+'_checked')
            else:
                imports.update(c.deps);sub.append(cn);checks.append(cn+'_checked');body += [f'def {cn} : Audit := {c.term()}',
                    f'def {cn}Table : PartialMachine := {table(p2)}',
                    f'theorem {cn}Table_eq : {cn}Table = ({e2}) := tableOK_sound _ _ (by decide)',
                    f'def {cn}Prefix : Z := {zrun(p2,node.n)}',
                    f'theorem {cn}_checked : zipCheck {BOUND} ({e2}) {cn} = true := by',
                    f'  rw [← {cn}Table_eq, ← checkAt_eq {BOUND} {cn}Table {cn} {node.n} {cn}Prefix (by rfl)]','  decide']
        kids='byMove ['+', '.join(sub)+']'
        body += [f'def {name} : Audit := .split {node.n} {slot(node.s)} ({kids})',
            f'theorem {name}_checked : zipCheck {BOUND} ({expr}) {name} = true := by',
            f'  change (zipQueryOK {BOUND} ({expr}) {node.n} {slot(node.s)} && allMoves (fun mv => zipCheck {BOUND} (refine ({expr}) {slot(node.s)} (some mv)) ({kids} mv))) = true',
            '  simp only [Bool.and_eq_true]', '  refine ⟨by decide, allMoves_of _ ?_⟩',all_moves(checks)]
    write(root,mod,imports,'\n'.join(body));return mod

def generate(root,work,threshold):
    t,certs,deps=collect(work,root);stats=Counter();node=Node(t,certs,deps,stats)
    assert stats==Counter(split=1393,cycle=23428,last=6947,open=1665),stats
    assert t[:3]==['split',10,5]
    write(root,'Raw54RABase',['Raw54Base'],'''abbrev parent : PartialMachine := refine BB6.Agent8Raw54.e1 (4,false) (some ⟨false,true,0⟩)
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)))''')
    # Keep the top-level module small and check the root after all shards.
    mods=[];children=[]
    for j,c in enumerate(node.children):
        cn=f'ra{j:02d}';e=f'refine parent (2,true) (some {move(MOVES[j])})';p=refine(parse(PARENT),5,MOVES[j]);mods.append(emit_tree(root,c,p,e,cn,10,threshold));children.append(cn)
    kids='byMove ['+', '.join(children)+']'
    write(root,'Raw54RACut',mods,f'''def tree : Audit := .split 10 (2,true) ({kids})
theorem checked : zipCheck {BOUND} parent tree = true := by
  change (zipQueryOK {BOUND} parent 10 (2,true) && allMoves (fun mv => zipCheck {BOUND} (refine parent (2,true) (some mv)) ({kids} mv))) = true
  simp only [Bool.and_eq_true]
  refine ⟨by decide, allMoves_of _ ?_⟩
{all_moves([c+'_checked' for c in children])}
theorem cover : ∀ m, compatible parent m → WeightedBound {BOUND} m :=
  (certifiedZip {BOUND} parent tree parent_root parent_nohalt checked).sound
theorem cover7014 : ∀ m, compatible parent m → WeightedBound 7014 m := by
  intro m hm k d hk hd
  exact Nat.le_trans (cover m hm k d hk hd) (by decide)
#print axioms cover
#print axioms cover7014''')
    print(stats,'FAR',len(certs)-len(deps),'proven',len(deps),'shards',len(list(root.glob('Raw54RAShard*.lean'))),flush=True)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT);ap.add_argument('--inputs',type=Path);ap.add_argument('--threshold',type=int,default=50);a=ap.parse_args();assert a.threshold>0
    if a.inputs:generate(a.output,a.inputs,a.threshold);return
    with tempfile.TemporaryDirectory() as d:
        work=Path(d)
        for src,name in [(ROOT.parent/'agent47-raw112-cut'/'enumerate_fast.cpp','enumerate'),(ROOT.parent/'agent8-tnf-six'/'bank.cpp','bank'),(ROOT.parent/'agent47-raw111-cut'/'ngram_sparse.cpp','ngram')]:
            subprocess.run(['g++','-std=c++17','-O3',str(src),'-o',str(work/name)],check=True)
        subprocess.run([str(work/'enumerate'),PARENT],cwd=work,check=True)
        with (work/'far.txt').open('w') as f:subprocess.run([str(work/'bank'),str(ROOT/'bank.txt'),str(work/'open.txt')],stdout=f,check=True)
        found={int(line.split(':')[0]) for line in (work/'far.txt').read_text().splitlines()}
        misses=[s for j,s in enumerate((work/'open.txt').read_text().splitlines()) if j not in found]
        (work/'n9.txt').write_text(subprocess.check_output([str(work/'ngram'),'6'],input=f'9 {misses[9]}\n',text=True))
        generate(a.output,work,a.threshold)
if __name__=='__main__':main()
