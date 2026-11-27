import json,sys
from pathlib import Path
from collections import Counter
root=Path(__file__).resolve().parent
idx=int(sys.argv[1]);B=7014
pcode=(root/'r49.open').read_text().splitlines()[idx]
parent=[pcode.replace('_','')[i:i+3] for i in range(0,36,3)]
tree=json.loads((root/f'trials/{idx}.json').read_text());opens=(root/f'trials/{idx}.open').read_text().splitlines();bank={opens[int(i)]:c for i,c in (x.split() for x in (root/f'trials/{idx}.far').read_text().splitlines())}
known_proven={
    "1RB0LE_1RC0LA_0RD0LB_1LD1RC_0LB0LF_---0LB": "BB6.Agent7Raw49NextSweeps.M90003",
    "1RB0LE_1RC0LA_0RD0LB_1LD1RC_0LB1LF_---0RA": "BB6.Agent7Raw49NextSweeps.M90012",
    "1RB1LE_1RC0LA_0RD0LB_1LD1RC_0LB0LF_---0LB": "BB6.Agent7Raw49NextSweeps.M90096",
    "1RB1LE_1RC0LA_0RD0LB_1LD1RC_0LB0LF_---1LB": "BB6.Agent7Raw49NextSweeps.M90097",
    "1RB1LE_1RC0LA_0RD0LB_1LD1RC_0LB0LF_---1LD": "BB6.Agent7Raw49NextSweeps.M90098",
    "1RB1LE_1RC0LA_0RD0LB_1LD1RC_0LF0LE_0LB---": "BB6.Agent7Raw49NextSweeps.M90111",
    "1RB1LE_1RC0LA_0RD0LB_1LD1RC_1LB0LF_---0LB": "BB6.Agent7Raw49NextSweeps.M90181",
    "1RB1LE_1RC0LA_0RD0LB_1LD1RC_1LB0LF_---1LD": "BB6.Agent7Raw49NextSweeps.M90184",
    "1RB1LE_1RC0LA_0RD0LB_1LD1RC_1LB1LF_---0LB": "BB6.Agent7Raw49NextSweeps.M90197",
    "1RB1LE_1RC0LA_0RD0LB_1LD1RC_1LF0LE_1LB---": "BB6.Agent7Raw49NextSweeps.M90217",
    "1RB1LE_1RC0LA_0RD0LB_1LD1RC_1LF0RE_1LC---": "BB6.Agent7Raw49NextSweeps.M90223",
    "1RB1LE_1RC0LA_0RD0LB_1LD1RC_1RE0LF_---0LB": "BB6.Agent7Raw49NextSweeps.M90243",
    "1RB0LE_1RC0RE_0RD0LB_1LD1RC_1RA0LF_1LA---": "BB6.Agent7Raw49NextSweeps.M110140",
    "1RB0LE_1RC0RE_0RD0LB_1LD1RC_1RA1LF_0LA---": "BB6.Agent7Raw49NextSweeps.M110141",
    "1RB---_1RC1LE_0RD0LB_1LD1RC_0LF0LB_0LA1LA": "BB6.Agent7Raw49NextSweeps.M130007",
    "1RB0LD_1RC1LE_0RD0LB_1LD1RC_1RF1RA_---1RE": "BB6.Agent7Raw49NextSweeps.M131063",
    "1RB0RD_1RC1LE_0RD0LB_1LD1RC_1RF1RA_---1RE": "BB6.Agent7Raw49NextSweeps.M131094",
    "1RB1LE_1RC1RF_0RD0LA_1LD1RC_0LB0LE_1RB---": "BB6.Agent7Raw49C6Counters.M600",
    "1RB1LE_1RC1RF_0RD0LA_1LD1RC_0RB0LE_1RB---": "BB6.Agent7Raw49MutatedFAR.M601",
    "1RB1LE_1RC1LF_0RD0LA_1LD1RC_0LB0LF_0LA---": "BB6.Agent7Raw49MutatedFAR.M602",
    "1RB1LE_1RC0RA_0RD0LA_1LD1RC_0RB0LF_0LB---": "BB6.Agent7Raw49AutoSweeps.M603",
    "1RB1LE_1RC---_0RD0LA_1LD1RC_0RC0LF_0LB0LF": "BB6.Agent7Raw49AutoSweeps.M604",
    "1RB1LE_1RC---_0RD0LA_1LD1RC_1RD0LF_0LB0LE": "BB6.Agent7Raw49MutatedFAR.M605",
    "1RB1LE_1RC---_0RD0LA_1LD1RC_1RD0LF_0LB0LF": "BB6.Agent7Raw49MutatedFAR.M606",
    "1RB1LE_1RC0RF_0RD0LA_1LD1RC_---0LF_1LA1RB": "BB6.Agent7Raw49AutoSweeps.M607",
    "1RB1LE_1RC1RA_0RD0LA_1LD1RC_---0LF_1LA1LC": "BB6.Agent7Raw49C6Counters.M608",
    "1RB1LE_1RC0LC_0RD0LA_1LD1RC_0LF1LA_---1LD": "BB6.Agent7Raw49AutoSweeps.M609",
    "1RB1LE_1RC0RE_0RD0LA_1LD1RC_1RF1LA_---0LC": "BB6.Agent7Raw49AutoSweeps.M610",
    "1RB1LE_1RC---_0RD0LA_1LD1RC_1RF1LB_1RD0RE": "BB6.Agent7Raw49MutatedFAR.M611",
    "1RB1LE_1RC---_0RD0LA_1LD1RC_0RF1LC_1RA1RE": "BB6.Agent7Raw49MutatedFAR.M612",
    "1RB1LE_1RC0RF_0RD0LA_1LD1RC_0LE1RB_0RB---": "BB6.Agent7Raw49C6Counters.M613",
    "1RB1LE_1RC---_0RD0LA_1LD1RC_0RF1RE_0RB0LD": "BB6.Agent7Raw49MutatedFAR.M614",
    "1RB1LE_1RC---_0RD0LA_1LD1RC_0RC1RF_0LB0LF": "BB6.Agent7Raw49MutatedFAR.M615",
    "1RB1LE_1RC---_0RD0LA_1LD1RC_1RD1RF_0LB0LF": "BB6.Agent7Raw49AutoSweeps.M616",
    "1RB0LE_1RC---_0RD0LA_1LD1RC_0LA0LF_0RF1RA": ("BB6.Agent7Raw49C1Guard.table .la0 false","BB6.Agent7Raw49C1Guard.never .la0 false"),
    "1RB0LE_1RC---_0RD0LA_1LD1RC_0LA0LF_1RF1RA": ("BB6.Agent7Raw49C1Guard.table .la0 true","BB6.Agent7Raw49C1Guard.never .la0 true"),
    "1RB0LE_1RC---_0RD0LA_1LD1RC_0LD0LF_0RF1RA": ("BB6.Agent7Raw49C1Guard.table .ld0 false","BB6.Agent7Raw49C1Guard.never .ld0 false"),
    "1RB0LE_1RC---_0RD0LA_1LD1RC_0LD0LF_1RF1RA": ("BB6.Agent7Raw49C1Guard.table .ld0 true","BB6.Agent7Raw49C1Guard.never .ld0 true"),
    "1RB0LE_1RC---_0RD0LA_1LD1RC_0RD0LF_0RF1RA": ("BB6.Agent7Raw49C1Guard.table .rd0 false","BB6.Agent7Raw49C1Guard.never .rd0 false"),
    "1RB0LE_1RC---_0RD0LA_1LD1RC_0RD0LF_1RF1RA": ("BB6.Agent7Raw49C1Guard.table .rd0 true","BB6.Agent7Raw49C1Guard.never .rd0 true"),
    "1RB0LE_1RC---_0RD0LA_1LD1RC_1LA0LF_0RF1RA": ("BB6.Agent7Raw49C1Guard.table .la1 false","BB6.Agent7Raw49C1Guard.never .la1 false"),
    "1RB0LE_1RC---_0RD0LA_1LD1RC_1LA0LF_1RF1RA": ("BB6.Agent7Raw49C1Guard.table .la1 true","BB6.Agent7Raw49C1Guard.never .la1 true"),
    "1RB0LE_1RC---_0RD0LA_1LD1RC_1LD0LF_0RF1RA": ("BB6.Agent7Raw49C1Guard.table .ld1 false","BB6.Agent7Raw49C1Guard.never .ld1 false"),
    "1RB0LE_1RC---_0RD0LA_1LD1RC_1LD0LF_1RF1RA": ("BB6.Agent7Raw49C1Guard.table .ld1 true","BB6.Agent7Raw49C1Guard.never .ld1 true"),
    "1RB0LE_1RC0RF_0RD0LA_1LD1RC_0LE1LA_1RA---": "BB6.Agent7Raw49MutatedFAR.M110",
    "1RB0LE_1RC0RF_0RD0LA_1LD1RC_1RD1LA_1RA---": "BB6.Agent7Raw49MutatedFAR.M111",
    "1RB0LE_1RC1LE_0RD0LA_1LD1RC_1RF1LB_0RA---": "BB6.Agent7Raw49AutoSweeps.M112",
    "1RB0LE_1RC0RE_0RD0LA_1LD1RC_1RF1LC_1RA---": "BB6.Agent7Raw49AutoSweeps.M113",
    "1RB0LE_1RC---_0RD0LA_1LD1RC_0LF1LE_0LA1RA": "BB6.Agent7Raw49MutatedFAR.M114",
    "1RB0LE_1RC1LF_0RD0LA_1LD1RC_0RA1LF_0LB---": "BB6.Agent7Raw49MutatedFAR.M115",
    "1RB0LE_1RC0RA_0RD0LA_1LD1RC_0RF1LF_1LA---": "BB6.Agent7Raw49AutoSweeps.M116",
    "1RB0LE_1RC---_0RD0LA_1LD1RC_1RB1LF_1LB0RA": "BB6.Agent7Raw49MutatedFAR.M117",
    "1RB0LE_1RC---_0RD0LA_1LD1RC_1RB1LF_1LB0RF": "BB6.Agent7Raw49AutoSweeps.M118",
    "1RB0LE_1RC---_0RD0LA_1LD1RC_1RB1LF_1LB1RA": "BB6.Agent7Raw49MutatedFAR.M119",
    "1RB0LE_1RC---_0RD0LA_1LD1RC_1RB1LF_1LB1RD": "BB6.Agent7Raw49MutatedFAR.M120",
    "1RB0LE_1RC0RF_0RD0LA_1LD1RC_1LA1RE_1RB---": "BB6.Agent7Raw49MutatedFAR.M121",
    "1RB0LE_1RC0LF_0RD0LA_1LD1RC_1RA1RE_---1LB": "BB6.Agent7Raw49Doubling",
    "1RB0LE_1RC1LF_0RD0LA_1LD1RC_0RA1RF_0LB---": "BB6.Agent7Raw49MutatedFAR.M123",
    "1RB0LE_1RC---_0RD0LA_1LD1RC_1LA1RF_1RF0RB": "BB6.Agent7Raw49MutatedFAR.M124",
    "1RB1RA_1RC0LE_0RD0LA_1LD1RC_0LA0LF_---1LB": ("BB6.Agent7Raw49C7Sweeps.Triple.table .a","BB6.Agent7Raw49C7Sweeps.Triple.never .a"),
    "1RB1RA_1RC0LE_0RD0LA_1LD1RC_1LB0LF_---1LB": ("BB6.Agent7Raw49C7Sweeps.Triple.table .b","BB6.Agent7Raw49C7Sweeps.Triple.never .b"),
    "1RB1RA_1RC0LE_0RD0LA_1LD1RC_1LB1LF_---0RB": ("BB6.Agent7Raw49C7Sweeps.Triple.table .c","BB6.Agent7Raw49C7Sweeps.Triple.never .c"),
    "1RB1RA_1RC1LE_0RD0LA_1LD1RC_0LF0LB_---0LB": ("BB6.Agent7Raw49C7Sweeps.Double.table false","BB6.Agent7Raw49C7Sweeps.Double.never false"),
    "1RB1RA_1RC1LE_0RD0LA_1LD1RC_1LF0LB_---1LB": ("BB6.Agent7Raw49C7Sweeps.Double.table true","BB6.Agent7Raw49C7Sweeps.Double.never true"),
    "1RB0RE_1RC0LE_0RD0LA_1LD1RC_1RB1LF_0LE---": ("BB6.Agent7Raw49SixSweeps.EDouble.table","BB6.Agent7Raw49SixSweeps.EDouble.never"),
    "1RB0RE_1RC1LF_0RD0LA_1LD1RC_1RE0LB_0LC---": ("BB6.Agent7Raw49SixSweeps.Alternating.table .c3","BB6.Agent7Raw49SixSweeps.Alternating.never .c3"),
    "1RB1LA_1RC1RE_0RD0LA_1LD1RC_---0RF_1RA0LF": ("BB6.Agent7Raw49SixSweeps.Ones.table false","BB6.Agent7Raw49SixSweeps.Ones.never false"),
    "1RB1LA_1RC1RE_0RD0LA_1LD1RC_---1RF_1RA1RB": ("BB6.Agent7Raw49SixSweeps.Ones.table true","BB6.Agent7Raw49SixSweeps.Ones.never true"),
    "1RB1RE_1RC1LE_0RD0LA_1LD1RC_1RF0LC_---0LB": ("BB6.Agent7Raw49SixSweeps.Alternating.table .c8a","BB6.Agent7Raw49SixSweeps.Alternating.never .c8a"),
    "1RB1RE_1RC0LC_0RD0LA_1LD1RC_1RF1LB_---0LE": ("BB6.Agent7Raw49SixSweeps.Alternating.table .c8b","BB6.Agent7Raw49SixSweeps.Alternating.never .c8b"),
    "1RB---_1RC---_0RD0RC_1LD1RC_------_------": ("BB6.Agent7Raw49Sweep.table .direct","BB6.Agent7Raw49Sweep.never .direct"),
    "1RB0RC_1RC---_0RD0RA_1LD1RC_------_------": ("BB6.Agent7Raw49Sweep.table .viaA","BB6.Agent7Raw49Sweep.never .viaA"),
    "1RB---_1RC0RC_0RD0RB_1LD1RC_------_------": ("BB6.Agent7Raw49Sweep.table .viaB","BB6.Agent7Raw49Sweep.never .viaB"),
    "1RB---_1RC---_0RD0RE_1LD1RC_---0RC_------": ("BB6.Agent7Raw49Sweep.table .viaE","BB6.Agent7Raw49Sweep.never .viaE"),
    "1RB0LB_1RC0RE_0RD0LA_1LD1RC_1LF0RF_1LA---": "BB6.Agent7Raw49Alternating",
    "1RB0RA_1RC0LE_0RD0LA_1LD1RC_1LC0LF_1LE---": ("BB6.Agent7Raw49ThreeSweeps.LeftE.table","BB6.Agent7Raw49ThreeSweeps.LeftE.never"),
    "1RB0RA_1RC0RE_0RD0LA_1LD1RC_1LF---_0LF0LD": ("BB6.Agent7Raw49ThreeSweeps.RightE.table false","BB6.Agent7Raw49ThreeSweeps.RightE.never false"),
    "1RB0RA_1RC1RE_0RD0LA_1LD1RC_1LF---_1LD0LF": ("BB6.Agent7Raw49ThreeSweeps.RightE.table true","BB6.Agent7Raw49ThreeSweeps.RightE.never true"),
}
if idx>=15:
    for line in (root/'sweep_recipes.jsonl').read_text().splitlines():
        i,s,*_=json.loads(line)
        known_proven['_'.join(s[j:j+6] for j in range(0,36,6))]=f'BB6.Agent7Raw49BulkRecipes.M{i}'
if idx>=15:
    for fn,ns in [('rest_sweep_recipes.jsonl','BB6.Agent7Raw49RestSweeps'),('rle_recipes.jsonl','BB6.Agent7Raw49RLE')]:
        if (root/fn).exists():
            for line in (root/fn).read_text().splitlines():
                i,s,*_=json.loads(line)
                known_proven['_'.join(s[j:j+6] for j in range(0,36,6))]=f'{ns}.M{i}'
proven={t:v for t,v in known_proven.items() if t in set(opens)}
assert set(opens)==set(bank)|set(proven),set(opens)-set(bank)-set(proven)
mod=f'Raw49C{idx}';out=root/f'child{idx}';out.mkdir(exist_ok=True)
def support(p):return max([2]+[max(i//2,ord(v[2])-65)+1 for i,v in enumerate(p) if v!='---'])
def move(i):return str(i//12)+('R' if i%12>=6 else 'L')+chr(65+i%6)
def mv(i):return f'⟨{str(bool(i//12)).lower()},{str(i%12>=6).lower()},{i%6}⟩'
def slot(i):return f'({i//2},{str(bool(i%2)).lower()})'
def show(p):return '_'.join(''.join(p[i:i+2]) for i in range(0,12,2))
def far(code,p):
    rev=int(code[0]);D=list(map(int,code[1:]));n=len(D)//2;N=6*n+1;H=N-1;halt=1<<H;T=[0]*(2*N);T[H]=T[N+H]=halt;rules=[]
    for l in range(n):
        for q in range(6):
            for a in range(2):
                m=p[2*q+a];dst=a*N+6*l+q
                if m=='---': T[dst]=halt;continue
                w,r,k=int(m[0]),m[1]=='R',ord(m[2])-65
                if r!=rev:T[dst]=1<<(6*D[2*l+w]+k)
                else:
                    for j in range(n):
                        for b in range(2):
                            if D[2*j+b]==l:rules.append((dst,b*N+6*j+k,w*N))
    while True:
        z=halt
        while True:
            old=z
            for j in range(N):
                if T[j]&z:z|=1<<j
            assert not z&1, (code,p)
            if old==z:break
        changed=False
        for dst,src,off in rules:
            v=T[dst];bits=T[src]
            while bits:
                k=(bits&-bits).bit_length()-1;v|=T[off+k];bits&=bits-1
            if v!=T[dst]:T[dst]=v;changed=True
        if not changed:return f'.far {str(bool(rev)).lower()} {n} ⟨0,{D},{T[:N]},{T[N:]},{z}⟩'
def table(p):
    a='fun s =>\n  match s.1.val,s.2 with\n'
    for i,v in enumerate(p):
        if v!='---':a+=f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(v[0]=="1").lower()},{str(v[1]=="R").lower()},{ord(v[2])-65}⟩)\n'
    return a+'  | _,_ => none'
def ordinary(t,p):
    if t[0]=='cycle':return f'.cycle {t[1]} {t[2]} {str(bool(t[3])).lower()} ({t[4]})'
    if t[0]=='last':return f'.last {t[1]} {slot(t[2])}'
    if t[0]=='open':
        assert t[1]==show(p)
        if t[1] in proven:
            pr=proven[t[1]]
            if isinstance(pr,tuple):return f'.proven ({pr[0]}) ({pr[1]})'
            return f'.proven {pr}.table {pr}.never'
        return far(bank[t[1]],p)
    assert t[0]=='split';n,s,cs=t[1:];assert len(cs)==24 and p[s]=='---'
    return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(ordinary(c,p[:s]+[move(i)]+p[s+1:]) for i,c in enumerate(cs))+'])'
def gen(t,p,cut):
    if t[0]=='alias':return '.unresolved'
    if cut==6 or t[0]!='split':return f'.closed ({ordinary(t,p)})'
    n,s,cs=t[1:];assert len(cs)==24 and p[s]=='---'
    return f'.split {n} {slot(s)} (byPartialMove [\n'+',\n'.join(gen(c,p[:s]+[move(i)]+p[s+1:],max(cut,i%6+1)) for i,c in enumerate(cs))+'])'
def size(t):return 1+sum(map(size,t[3])) if t[0]=='split' else 1
head=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7.{mod}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot
''';foot=f'\nend BB6.Agent7.{mod}\n'
cut=support(parent)
base=f'''import Raw40Nores
import Raw49Sweep
import Raw49Alternating
import Raw49ThreeSweeps
import Raw49SixSweeps
import Raw49C7Sweeps
import Raw49C1Guard
import Raw49AutoSweeps
import Raw49MutatedFAR
import Raw49Doubling
import Raw49C6Counters
import Raw49NextSweeps
{'import Raw49BulkRecipes' if idx>=15 else ''}
{'import Raw49RestSweeps' if any(isinstance(v,str) and v.startswith("BB6.Agent7Raw49RestSweeps.") for v in proven.values()) else ''}
{'import Raw49RLE' if any(isinstance(v,str) and v.startswith("BB6.Agent7Raw49RLE.") for v in proven.values()) else ''}
{head}
def p : PartialMachine := {table(parent)}
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem supported : TNFSupport p {cut} := supportOK_sound _ _ (by decide)
{foot}'''
(out/f'{mod}Base.lean').write_text(base)
manifest=[(f'{mod}Base',[])];counter=0

def cases():return '''  rcases m with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
'''
def combine(n,s,cut,ids,name):
    a=f'def k{name} : Move → PartialAudit := byPartialMove [{",".join("t"+i for i in ids)}]\ndef t{name} : PartialAudit := .split {n} {slot(s)} k{name}\ntheorem q{name} : zipQueryOK {B} p{name} {n} {slot(s)} = true := by decide\n'
    a+=f'theorem ck{name} (m : Move) : (if m.next.val ≤ {cut} then canonicalCheck {B} (refine p{name} {slot(s)} (some m)) (max {cut} (m.next.val+1)) (k{name} m) else true) = true := by\n'+cases()
    for q in range(6):
        for w in range(2):
            for r in range(2):a+='  · '+(f'exact c{ids[12*w+6*r+q]}' if q<=cut else 'rfl')+'\n'
    a+=f'''theorem c{name} : canonicalCheck {B} p{name} {cut} t{name} = true := by
  simp only [t{name},canonicalCheck,q{name},Bool.true_and]
  exact allMoves_of _ ck{name}
theorem nr{name} : canonicalResiduals p{name} {cut} t{name} = [] := by
  unfold t{name}
  apply noresSplit
  intro m h
'''+cases()
    for q in range(6):
        for w in range(2):
            for r in range(2):a+='  · '+(f'exact nr{ids[12*w+6*r+q]}' if q<=cut else f'change {q} ≤ {cut} at h; omega')+'\n'
    return a

def sub(t,p,cut,name,expr,lines):
    lines.append(f'abbrev p{name} := {expr}')
    if size(t)<=96:
        lines.append(f'def t{name} : PartialAudit := {gen(t,p,cut)}')
        lines.append(f'theorem c{name} : canonicalCheck {B} p{name} {cut} t{name} = true := by decide +kernel')
        if t[0]!='alias':lines.append(f'theorem nr{name} : canonicalResiduals p{name} {cut} t{name} = [] := by decide +kernel')
        return
    n,s,cs=t[1:];ids=[]
    for i,k in enumerate(cs):
        nm=f'{name}_{i:02}';ids.append(nm);sub(k,p[:s]+[move(i)]+p[s+1:],max(cut,i%6+1),nm,f'refine p{name} {slot(s)} (some {mv(i)})',lines)
    lines.append(combine(n,s,cut,ids,name))
n,s,cs=tree[1:];ids=[]
for i,k in enumerate(cs):
    name=f'{i:02}';ids.append(name);lines=[]
    sub(k,parent[:s]+[move(i)]+parent[s+1:],max(cut,i%6+1),name,f'refine p {slot(s)} (some {mv(i)})',lines)
    nm=f'{mod}Kid{i:02}';(out/f'{nm}.lean').write_text(f'import {mod}Base\n'+head+'\n'.join(lines)+foot);manifest.append((nm,[f'{mod}Base']))
allname=f'{mod}All';end=''.join(f'import {mod}Kid{i:02}\n' for i in range(24))+head+'abbrev ptop := p\n'+combine(n,s,cut,ids,'top')+f'''
theorem all_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound {B} m := by
  intro m hm
  rcases canonicalSound {B} p {cut} ttop (by decide) supported root nohalt ctop m hm with hb | ⟨e,he,_⟩
  · exact hb
  · rw [nrtop] at he; contradiction

theorem all : ∀ m, compatible p m → WeightedBound {B} m := by
  intro m hm
  exact all_quotient m (compatible_quotient hm)

#print axioms all_quotient
#print axioms all
'''+foot
(out/f'{allname}.lean').write_text(end);manifest.append((allname,[f'{mod}Kid{i:02}' for i in range(24)]));(out/'manifest.json').write_text(json.dumps(manifest))
