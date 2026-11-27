#!/usr/bin/env python3
"""Generate exact modular Raw42 closed Covers from a complete discovery partition.
Inputs are untrusted; every tree branch and witness is checked by Lean.
Usage: gen_assembly42.py REPO BRANCH SEARCH_DIR OUTPUT_DIR
"""
import json,sys,subprocess
from pathlib import Path
from collections import Counter
from itertools import product
repo=Path(sys.argv[1]);branch=sys.argv[2];src,out=map(Path,sys.argv[3:]);out.mkdir(parents=True,exist_ok=True)
assert branch in ('0LA','0LE','0RA','0RB','0RE','1LA','1LB','1LC','1LE','1RA','1RB','1RE')
raw=repo/'im-results/agent32-raw42'
sys.path.insert(0,str(repo/'im-results/agent31-three-hole-tnf'))
from generate_four_hole import masks
B=1006 if branch in ('0RA','0RB') else 100006
opens=src.joinpath('open.txt').read_text().splitlines()
ids={t:i for i,t in enumerate(opens)};assert len(ids)==len(opens)
bank={};proof={};proof_mod={};late={}
for file in ['far5.txt','far6.txt']:
    if (src/file).exists():
        for row in (src/file).read_text().splitlines():
            i,c=row.split();j=int(i);assert j not in bank and j<len(opens);bank[j]=c
def register_proof(j,v,mod):
    assert j not in bank and j not in proof and j not in late
    proof[j]=v;proof_mod[j]=mod
def leafproof(row,kind,script,one_based):
    i,s,*rest=row.split();j=int(i)-int(one_based);assert opens[j].replace('_','')==s
    mod=f'Raw42{branch}{kind}{j}'; ns=f'BB6.Agent32Raw42{branch}.{kind}.Leaf{j}'
    inputrow=' '.join([str(j),s,*rest])+'\n'
    code=subprocess.check_output([sys.executable,str(raw/script)],input=inputrow,text=True)
    out.joinpath(mod+'.lean').write_text(code.replace('Agent32Raw42RA','Agent32Raw42'+branch))
    register_proof(j,f'.proven {ns}.table {ns}.live',mod)
if branch in ('0RA','0RB'):
    suffix='' if branch=='0RA' else 'rb'
    for filename,kind,script in [(f'ngram42{suffix}.tsv','NGram','emit_ngram42.py'),(f'run42{suffix}.tsv','Run','emit_run42.py')]:
        for row in raw.joinpath(filename).read_text().splitlines():
            leafproof(row,kind,script,True)
    if branch=='0RA':
        for i,alt in [(1582,'false'),(1665,'true')]:
            ns='BB6.Agent32Raw42RA.TwinGrowth';register_proof(i-1,f'.proven ({ns}.table {alt}) ({ns}.never {alt})','Raw42RATwinGrowth')
        register_proof(1658,'.proven BB6.Agent32Raw42RA.Leaf1659.table BB6.Agent32Raw42RA.Leaf1659.never','Raw42Leaf1659Invariant')
        late={309:'.cycle 311 656 false 9',496:'.last 622 (4,true)',1654:'.cycle 2101 842 true 1'}
    else:late={292:'.cycle 618 19 false (-8)',1569:'.last 565 (4,false)'}
else:
    from emit_block42 import emit_cases
    hard={int(i):code for i,code in (line.split() for line in (src/'hard.txt').read_text().splitlines())}
    rows=[x for x in json.loads((raw/'block42_witnesses.json').read_text()) if x['branch']==branch and x['id'] in hard]
    assert len({x['id'] for x in rows})==len(rows)
    for x in rows:
        i=x['id'];assert x['code']==hard[i]==opens[i].replace('_','')
    assert set(hard)=={x['id'] for x in rows}, f'unresolved discovery leaves: {set(hard)-{x["id"] for x in rows}}'
    for x,mod in zip(rows,emit_cases(repo,out,rows)):
        i=x['id'];ns=f'BB6.Agent32Raw42{branch}.Block.Leaf{i}'
        register_proof(i,f'.proven {ns}.table {ns}.live',mod)
    for filename,kind,script in [('ngram.txt','NGram','emit_ngram42.py'),('run.txt','Run','emit_run42.py')]:
        for row in src.joinpath(filename).read_text().splitlines():leafproof(row,kind,script,False)
    for row in (src/'known.txt').read_text().splitlines():
        i,v=row.split();group,name=v.split(':')
        assert group in ('Wide','Nested')
        ns=f'BB6.Agent32Raw42{group}.{name}'
        register_proof(int(i),f'.proven {ns}.p {ns}.never',f'Raw42{group}Growth')
    for row in (src/'late.txt').read_text().splitlines():
        i,k,*args=row.split();j=int(i)
        assert j not in bank and j not in proof
        if k=='cycle':
            e,k,d,b=map(int,args);late[j]=f'.cycle {e} {k} {str(bool(d)).lower()} ({b})'
        else:
            assert k=='last'
            n,s=map(int,args);late[j]=f'.last {n} ({s//2},{str(bool(s%2)).lower()})'
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
HEADER=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42{branch}.Closed
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent32PartialCut BB6.Agent32PackedClosed BB6.Agent32Raw59QuickWeight
'''
FOOT=f'\nend BB6.Agent32Raw42{branch}.Closed\n'
def write(mod,imports,lines):
    out.joinpath(mod+'.lean').write_text(''.join(f'import {x}\n' for x in sorted(set(imports)))+HEADER+'\n'.join(lines)+FOOT)
parent=parse('1RB---_1RC'+branch+'_0RD---_1LD0LB_------_------')
cut0=max(4,ord(branch[2])-64)
branch_mv=(int(branch[0])*12+(branch[1]=='R')*6+ord(branch[2])-65)
prefix=f'Raw42{branch}Closed'
root=prefix+'Base';write(root,['Raw42AssemblyCore'],[f'abbrev p := BB6.Agent32Raw42.child {mv(branch_mv)}'])
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
    if sizes[id(t)]<=64:
        lines.append(f'def t{name} : Cut := {render(t,p,cut,imports)}')
        lines.append(f'theorem c{name} : closedCheck {B} {cut} p{name} t{name} = true := by decide')
        return
    n,s,kids=t[1:]
    for i,k in enumerate(kids):small(k,p[:s]+[move(i)]+p[s+1:],cut+(i%6==cut),f'{name}_{i:02}',f'refine p{name} {slot(s)} (some {mv(i)})',lines,imports)
    join(lines,name,n,s,cut)
def generate(t,p,cut,name,expr):
    mod=prefix+name;lines=[];imports={root}
    if sizes[id(t)]<=400:small(t,p,cut,name,expr,lines,imports)
    else:
        n,s,kids=t[1:];lines.append(f'abbrev p{name} := {expr}')
        siblings=[]; sibling_imports={root}
        for i,k in enumerate(kids):
            sub=f'{name}_{i:02}';e=f'refine ({expr}) {slot(s)} (some {mv(i)})';pp=p[:s]+[move(i)]+p[s+1:];cc=cut+(i%6==cut)
            if sizes[id(k)] >200:imports.add(generate(k,pp,cc,sub,e))
            else:small(k,pp,cc,sub,e,siblings,sibling_imports)
        if siblings:
            sib=mod+'Small';write(sib,sibling_imports,siblings);imports.add(sib)
        join(lines,name,n,s,cut)
    write(mod,imports,lines);return mod
tree=json.loads(src.joinpath('tree.json').read_text());size(tree)
mod=generate(tree,parent,cut0,'Root','p');assert len(seen)==len(opens)
write(prefix+'Cover',[mod],[f'''theorem root_support : TNFSupport p {cut0} := by
  intro s t h
  rcases s with ⟨q,b⟩
  have hv : ∀ q : Fin 6, ∀ b : Bool, ∀ t : Transition,
      p (q,b) = some t → q.val < {cut0} ∧
      ∀ mv, t = some mv → mv.next.val < {cut0} := by decide
  exact hv q b t h
''',f'''theorem cover : Cover (WeightedBound {B}) p :=
  closedCover {B} {cut0} p tRoot (by decide) root_support (by decide)
    (weightedTNFNoAssignedHalt_refine _ _ _ BB6.Agent32Raw42.parent_nohalt) cRoot
#print axioms cover'''])
print('open',len(seen),'modules',len(list(out.glob('*.lean'))),'leaf stats',stats)

# Assign independent bottom-level tree modules by their actual imported source cost.
roots=[p for p in out.glob(prefix+'Root*.lean') if not any(l.startswith('import '+prefix+'Root') for l in p.read_text().splitlines())]
if not roots:roots=[out/(prefix+'Root.lean')]
groups={str(i):[] for i in range(min(8,len(roots)))}
sizes=[0]*len(groups)
def weight(p):
    imports=[line.split()[1] for line in p.read_text().splitlines() if line.startswith('import ')]
    return p.stat().st_size+sum((out/(m+'.lean')).stat().st_size for m in imports if (out/(m+'.lean')).is_file() and not m.endswith('Base'))
for p in sorted(roots,key=lambda p:(-weight(p),p.name)):
    i=min(range(len(groups)),key=lambda j:sizes[j]);groups[str(i)].append(p.stem);sizes[i]+=weight(p)
(out/'shards.json').write_text(json.dumps({'artifact_prefix':'raw42-assembly-shard','groups':groups},indent=2)+'\n')
(out/'matrix.json').write_text(json.dumps(list(groups))+'\n')
print('shard weights',sizes,'groups',len(groups),flush=True)
