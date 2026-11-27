#!/usr/bin/env python3
"""Build complete sharded Raw42/0RB certificates; discovery is untrusted.
Usage: gen_closed42.py REPO SEARCH_DIR OUTPUT_DIR.
SEARCH_DIR contains tree.json, open.txt, far5.txt. FAR indices start at 0;
exceptional TSV indices start at 1 and are checked against the exact table.
"""
import json,sys,subprocess
from pathlib import Path
from collections import Counter
from itertools import product
repo,src,out=map(Path,sys.argv[1:]);out.mkdir(parents=True,exist_ok=True)
raw=repo/'im-results/agent32-raw42'
sys.path.insert(0,str(repo/'im-results/agent31-three-hole-tnf'))
from generate_four_hole import masks
B=1006
opens=src.joinpath('open.txt').read_text().splitlines()
ids={t:i for i,t in enumerate(opens)};assert len(ids)==len(opens)
bank={int(i):c for i,c in (x.split() for x in src.joinpath('far5.txt').read_text().splitlines())}
proof={}; proof_mod={}
for filename,kind,script in [('ngram42rb.tsv','NGram','emit_ngram42.py'),('run42rb.tsv','Run','emit_run42.py')]:
    for row in raw.joinpath(filename).read_text().splitlines():
        i,s,*_=row.split();j=int(i)-1;assert opens[j].replace('_','')==s and j not in bank and j not in proof
        mod=f'Raw42RB{kind}{i}'; ns=f'BB6.Agent32Raw42RB.{kind}.Leaf{i}'
        out.joinpath(mod+'.lean').write_text(subprocess.check_output([sys.executable,str(raw/script)],input=row+'\n',text=True).replace('Agent32Raw42RA','Agent32Raw42RB'))
        proof[j]=f'.proven {ns}.table {ns}.live';proof_mod[j]=mod
late={292:'.cycle 618 19 false (-8)',1569:'.last 565 (4,false)'}
assert set(bank)|set(proof)|set(late)==set(range(len(opens))) and len(bank)+len(proof)+len(late)==len(opens)
def parse(t):
    t=t.replace('_','');return [t[i:i+3] for i in range(0,36,3)]
def show(p):return '_'.join(''.join(p[i:i+2]) for i in range(0,12,2))
def move(i):return str(i//12)+('R' if i%12>=6 else 'L')+chr(65+i%6)
def mv(i):return f'⟨{str(bool(i//12)).lower()},{str(i%12>=6).lower()},{i%6}⟩'
def slot(i):return f'({i//2},{str(bool(i%2)).lower()})'
def far(c,p):
    rev=int(c[0]);n,D,L,R,z=masks(tuple(p),rev,list(map(int,c[1:])))
    return f'.far {str(bool(rev)).lower()} {n} ⟨0,{D},{L},{R},{z}⟩'
HEADER='''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42RB.Closed
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent32PartialCut BB6.Agent32PackedClosed BB6.Agent32Raw59QuickWeight
'''
FOOT='\nend BB6.Agent32Raw42RB.Closed\n'
def write(mod,imports,lines):
    out.joinpath(mod+'.lean').write_text(''.join(f'import {x}\n' for x in sorted(set(imports)))+HEADER+'\n'.join(lines)+FOOT)
parent=parse('1RB---_1RC0RB_0RD---_1LD0LB_------_------')
root='Raw42RBClosedBase';write(root,['TNFPackedClosed','Raw42Cut'],[f'abbrev p := BB6.Agent32Raw42.child {mv(7)}'])
sizes={}
def size(t):
    v=1+sum(size(k) for k in t[3]) if t[0]=='split' else 1;sizes[id(t)]=v;return v
seen=set(); stats=Counter()
def render(t,p,cut,imports):
    tag=t[0];stats[tag]+=1
    if tag=='skip':return '.keep'
    if tag=='cycle':return f'.closed (.cycle {t[1]} {t[2]} {str(t[3]).lower()} ({t[4]}))'
    if tag=='last':return f'.closed (.last {t[1]} {slot(t[2])})'
    if tag=='open':
        assert t[1]==show(p);j=ids[t[1]];assert j not in seen;seen.add(j)
        if j in bank:v=far(bank[j],p)
        elif j in proof:v=proof[j];imports.add(proof_mod[j])
        else:v=late[j]
        return f'.closed ({v})'
    assert tag=='split';n,s,kids=t[1:];assert p[s]=='---' and len(kids)==24
    ans=[]
    for i,k in enumerate(kids):
        assert (k[0]=='skip')==(i%6>cut)
        ans.append(render(k,p[:s]+[move(i)]+p[s+1:],cut+(i%6==cut),imports))
    return f'.split {n} {slot(s)} (byMoveCut [\n'+',\n'.join(ans)+'])'
def join(lines,name,n,s,cut):
    kids=[f'{name}_{i:02}' for i in range(24)]
    lines.extend([f'def k{name} : Move → Cut := byMoveCut [{",".join("t"+x for x in kids)}]',f'def t{name} : Cut := .split {n} {slot(s)} k{name}',f'theorem q{name} : quickPackedQuery {B} p{name} {n} {slot(s)} = true := by decide',f'''theorem ck{name} (m : Move) : (if m.next.val ≤ {cut} then closedCheck {B} (advanceCut {cut} m) (refine p{name} {slot(s)} (some m)) (k{name} m) else true) = true := by
  rcases m with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r'''])
    for q,w,r in product(range(6),range(2),range(2)):
        k=kids[12*w+6*r+q];lines.append('  · '+('rfl' if q>cut else f'exact c{k}'))
    lines.append(f'theorem c{name} : closedCheck {B} {cut} p{name} t{name} = true := split_checked _ _ _ _ _ _ q{name} ck{name}')
def small(t,p,cut,name,expr,lines,imports):
    lines.append(f'abbrev p{name} := {expr}')
    if t[0]=='skip':lines.append(f'def t{name} : Cut := .keep');return
    if sizes[id(t)]<=100:
        lines.append(f'def t{name} : Cut := {render(t,p,cut,imports)}')
        lines.append(f'theorem c{name} : closedCheck {B} {cut} p{name} t{name} = true := by decide')
        return
    n,s,kids=t[1:]
    for i,k in enumerate(kids):small(k,p[:s]+[move(i)]+p[s+1:],cut+(i%6==cut),f'{name}_{i:02}',f'refine p{name} {slot(s)} (some {mv(i)})',lines,imports)
    join(lines,name,n,s,cut)
def generate(t,p,cut,name,expr):
    mod='Raw42RBClosed'+name;lines=[];imports={root}
    if sizes[id(t)]<=1000:small(t,p,cut,name,expr,lines,imports)
    else:
        n,s,kids=t[1:];lines.append(f'abbrev p{name} := {expr}')
        for i,k in enumerate(kids):
            sub=f'{name}_{i:02}';e=f'refine ({expr}) {slot(s)} (some {mv(i)})';pp=p[:s]+[move(i)]+p[s+1:];cc=cut+(i%6==cut)
            if sizes[id(k)]>500:imports.add(generate(k,pp,cc,sub,e))
            else:small(k,pp,cc,sub,e,lines,imports)
        join(lines,name,n,s,cut)
    write(mod,imports,lines);return mod
tree=json.loads(src.joinpath('tree.json').read_text());size(tree)
mod=generate(tree,parent,4,'Root','p');assert len(seen)==len(opens)
write('Raw42RBClosedCover',[mod],['''theorem root_support : TNFSupport p 4 := by
  intro s t h
  rcases s with ⟨q,b⟩
  have hv : ∀ q : Fin 6, ∀ b : Bool, ∀ t : Transition,
      p (q,b) = some t → q.val < 4 ∧
      ∀ mv, t = some mv → mv.next.val < 4 := by decide
  exact hv q b t h
''',f'''theorem cover : Cover (WeightedBound {B}) p :=
  closedCover {B} 4 p tRoot (by decide) root_support (by decide)
    (weightedTNFNoAssignedHalt_refine _ _ _ BB6.Agent32Raw42.parent_nohalt) cRoot
#print axioms cover'''])
print('open',len(seen),'modules',len(list(out.glob('*.lean'))),'leaf stats',stats)
