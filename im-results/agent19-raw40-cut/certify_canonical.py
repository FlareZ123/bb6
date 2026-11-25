import json,sys,os
from pathlib import Path

# Reuse exact FAR saturation and move spelling from the raw sharded generator.
exec(Path(__file__).with_name('certify_shards.py').read_text().split('src=Path')[0])
src=Path(sys.argv[1]);output=Path(sys.argv[2]);output.mkdir(parents=True,exist_ok=True)
parent=parse(sys.argv[3]);tree=json.loads((src/'tree.json').read_text());B=int(sys.argv[4]);mod=sys.argv[5]
bank={int(i):c for i,c in (x.split() for x in (src/'far5.txt').read_text().splitlines())}
if (src/'far_extra.txt').exists():
    bank.update({int(i):c for i,c in (x.split() for x in (src/'far_extra.txt').read_text().splitlines())})
proven=dict(x.split() for x in (src/'proven.txt').read_text().splitlines()) if (src/'proven.txt').exists() else {}
late={code:(int(n),int(s)) for code,n,s in (x.split() for x in (src/'late.txt').read_text().splitlines())} if (src/'late.txt').exists() else {}
opens=(src/'open.txt').read_text().splitlines();it=iter(enumerate(opens));threshold=int(sys.argv[6]) if len(sys.argv)>6 else 96

def support(p):return max([2]+[max(i//2,ord(v[2])-65)+1 for i,v in enumerate(p) if v!='---'])
def size(t):return 1+sum(map(size,t[3])) if t[0]=='split' else 1

def ordinary(t,p):
    if t[0]=='cycle':return f'.cycle {t[1]} {t[2]} {str(t[3]).lower()} ({t[4]})'
    if t[0]=='last':return f'.last {t[1]} {slot(t[2])}'
    if t[0]=='open':
        i,code=next(it);assert t[1]==code==show(p)
        if code in late:
            n,s=late[code]
            return f'.last {n} {slot(s)}'
        if code in proven:
            pr=proven[code]
            return f'.proven {pr}.table {pr}.never'
        pumps={'1RB0RC_1RC1RE_0RD1LB_1LD1LA_1LF0RF_---0LB':'RC1LB','1RB0RB_1RC0RC_0RD0LE_1LD1LA_0LF---_1LC0RB':'RB0RC'}
        if code in pumps:return f'.proven BB6.Agent19Raw40.{pumps[code]}.table BB6.Agent19Raw40.{pumps[code]}.never'
        extra={'1RB0RB_1RC1RC_0RD0LE_1LD1LA_---1LF_1LC0RF':('RB1RC.table','RB1RC.never'),
               '1RB1RB_1RC0RC_0RD0LE_1LD1LA_1RB1LF_---1LC':('A10RC.table A10RC.rb','A10RC.neverRB'),
               '1RB0RD_1RC0RC_0RD0LE_1LD1LA_1RB1LF_---1LC':('A10RC.table A10RC.rd','A10RC.neverRD'),
               '1RB1RC_1RC1RE_0RD1LB_1LD1LA_1LF0RF_---0LB':('OneRC1LB.table','OneRC1LB.never'),
               '1RB1LC_1RC1RD_0RD0RE_1LD1LA_1RC0LF_1LE---':('LC1RD.table','LC1RD.never'),
               '1RB1LC_1RC1RD_0RD1LE_1LD1LA_0LA1RF_---0RE':('LC1RDAlt.table','LC1RDAlt.never')}
        if code in extra:
            table,proof=extra[code];return f'.proven ({table}) ({proof})'
        return far(bank[i],p)
    assert t[0]=='split';n,s,children=t[1:];assert p[s]=='---' and len(children)==24
    return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(ordinary(k,p[:s]+[move(i)]+p[s+1:]) for i,k in enumerate(children))+'])'

def gen(t,p,cut):
    if t[0]=='alias':return '.unresolved'
    if cut==6 or t[0]!='split':return f'.closed ({ordinary(t,p)})'
    n,s,children=t[1:];assert len(children)==24 and p[s]=='---'
    return f'.split {n} {slot(s)} (byPartialMove [\n'+',\n'.join(gen(k,p[:s]+[move(i)]+p[s+1:],max(cut,i%6+1)) for i,k in enumerate(children))+'])'

head=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.{mod}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier
'''
foot=f'\nend BB6.Agent19Raw40.{mod}\n'
cut=support(parent)
imports='import CanonicalPartial\n' if os.environ.get('RAW40_STANDALONE')=='1' else 'import Raw40CanonicalCut\nimport Raw40TwoSided\nimport Raw40MoreTwoSided\nimport Raw40ThirdSweeps\n'
if any('.Auto.Leaf' in v for v in proven.values()):imports+='import Raw40AutoPump\n'
if any('.Auto2.Leaf' in v for v in proven.values()):imports+='import Raw40AutoPump2\n'
if any('.Auto3.Leaf' in v for v in proven.values()):imports+='import Raw40AutoPump3\n'
if any('CounterVariants' in v for v in proven.values()):imports+='import Raw40CounterVariants\n'
if any('BinaryCarry' in v for v in proven.values()):imports+='import Raw40BinaryCarry\n'
if any('Counter17' in v for v in proven.values()):imports+='import Raw40Counter17\n'
base=imports+head+f'-- {show(parent)}\ndef p : PartialMachine := fun s =>\n  match s.1.val,s.2 with\n'
for i,v in enumerate(parent):
    if v!='---':base+=f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(v[0]=="1").lower()},{str(v[1]=="R").lower()},{ord(v[2])-65}⟩)\n'
base+='  | _,_ => none\n'
base+=f'''theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem supported : TNFSupport p {cut} := supportOK_sound _ _ (by decide)
'''+foot
(output/f'{mod}Base.lean').write_text(base)

# All split nodes above threshold get separately checked children.
# Once all 6 states are introduced, use original prefix checker for compact subtrees.
def gen_shard(t,p,cut,name,expr,lines):
    lines.append(f'abbrev p{name} := {expr}')
    if size(t)<=threshold:
        lines.append(f'def t{name} : PartialAudit := {gen(t,p,cut)}')
        lines.append(f'theorem c{name} : canonicalCheck {B} p{name} {cut} t{name} = true := by decide +kernel')
        return
    assert t[0]=='split';n,s,children=t[1:];names=[]
    for i,k in enumerate(children):
        nm=f'{name}_{i:02}';names.append(nm)
        gen_shard(k,p[:s]+[move(i)]+p[s+1:],max(cut,i%6+1),nm,f'refine p{name} {slot(s)} (some {mv(i)})',lines)
    lines.extend(combine(name,n,s,cut,names))

def combine(name,n,s,cut,names):
    xs=[f'def k{name} : Move → PartialAudit := byPartialMove [{",".join("t"+nm for nm in names)}]',
        f'def t{name} : PartialAudit := .split {n} {slot(s)} k{name}',
        f'theorem q{name} : zipQueryOK {B} p{name} {n} {slot(s)} = true := by decide']
    proof=f'''theorem ck{name} (m : Move) : (if m.next.val ≤ {cut} then canonicalCheck {B} (refine p{name} {slot(s)} (some m)) (max {cut} (m.next.val+1)) (k{name} m) else true) = true := by
  rcases m with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
'''
    for q in range(6):
        for w in range(2):
            for r in range(2):
                proof+=f'  · '+(f'exact c{names[12*w+6*r+q]}' if q<=cut else 'rfl')+'\n'
    xs.append(proof.rstrip());xs.append(f'''theorem c{name} : canonicalCheck {B} p{name} {cut} t{name} = true := by
  simp only [t{name},canonicalCheck,q{name},Bool.true_and]
  exact allMoves_of _ ck{name}''')
    return xs
n,s,children=tree[1:]
for i,k in enumerate(children):
    q=parent[:s]+[move(i)]+parent[s+1:];lines=[]
    gen_shard(k,q,max(cut,i%6+1),str(i),f'refine p {slot(s)} (some {mv(i)})',lines)
    (output/f'{mod}Kid{i:02}.lean').write_text(f'import {mod}Base\n'+head+'\n'.join(lines)+foot)
assert next(it,None) is None
end=''.join(f'import {mod}Kid{i:02}\n' for i in range(24))+head+'abbrev ptop := p\n'+'\n'.join(combine('top',n,s,cut,[str(i) for i in range(24)]))
end+=f'''

theorem nores : canonicalResiduals p {cut} ttop = [] := by decide +kernel

theorem all_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound {B} m := by
  intro m hm
  rcases canonicalSound {B} p {cut} ttop (by decide) supported root nohalt ctop m hm with hb | ⟨e,he,_⟩
  · exact hb
  · rw [nores] at he; contradiction

theorem all : ∀ m, compatible p m → WeightedBound {B} m := by
  intro m hm
  exact all_quotient m (compatible_quotient hm)

#print axioms all_quotient
#print axioms all
'''+foot
(output/f'{mod}All.lean').write_text(end)
