from pathlib import Path
from itertools import product
from collections import Counter
import sys,json
ROOT=Path(__file__).parent
MOVES=[w+d+q for q,w,d in product("ABCDEF","01","LR")]
ORDER=[4*q+2*w+r for w,r,q in product(range(2),range(2),range(6))]
def parse(s):
    s=s.replace("_","")
    return [24 if s[i:i+3]=="---" else MOVES.index(s[i:i+3]) for i in range(0,36,3)]
def masks(p,rev,D):
    d=len(D)//2
    N=6*d+1
    h=1<<(N-1)
    T=[0]*(2*N)
    T[N-1]=T[2*N-1]=h
    rules=[]
    for b,l,q in product(range(2),range(d),range(6)):
        a=p[2*q+b]; dst=b*N+6*l+q
        if a==24:
            T[dst]=h;continue
        n,w,r=a//4,(a//2)%2,a%2
        if r!=rev:
            T[dst]=1<<(6*D[2*l+w]+n)
        else:
            for j,x in product(range(d),range(2)):
                if D[2*j+x]==l:
                    rules.append((dst,x*N+6*j+n,w*N))
    while True:
        change=False
        for dst,src,off in rules:
            v=T[src]; new=T[dst]
            while v:
                t=v&-v;v-=t
                new|=T[off+t.bit_length()-1]
            if new!=T[dst]:
                T[dst]=new;change=True
        if not change:break
    z=h
    while True:
        old=z
        for i in range(N):
            if T[i]&z:z|=1<<i
        if old==z:break
    assert z&1==0,(p,rev,D)
    return f'.far {str(bool(rev)).lower()} {d} ⟨0,{D},{T[:N]},{T[N:]},{z}⟩'
def slot(s):return f'({s//2}, {str(bool(s%2)).lower()})'
def move(a):return f'⟨{str(bool(a&2)).lower()}, {str(bool(a&1)).lower()}, {a//4}⟩'
tag=sys.argv[1]
PARENT="1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---"+tag
maxn,*expected=next(list(map(int,x.split()[1:])) for x in (ROOT/'census.txt').read_text().splitlines() if x.startswith(tag+" "))
B=maxn+6
over={};pumpids={}
pumpcodes={i:c for i,c,*_ in json.loads((ROOT/'pumps.json').read_text())}
active=False
for line in (ROOT/'dfa-overrides.txt').read_text().splitlines():
    if line.startswith('['):
        active=line=='['+tag+']';continue
    if not active:continue
    rev,dfa,ids=line.split()
    for i in ids.split(','):
        if rev=='pump':pumpids[int(i)]=int(dfa)
        else:over[int(i)]=(int(rev),[int(x,36) for x in dfa])
lines=iter(Path(sys.argv[2]).read_text().splitlines())
counts=Counter()
opened=0
def read(p):
    global opened
    k,*args=next(lines).split()
    counts[k]+=1
    if k=="C":
        n,t,b,z=map(int,args)
        return f'.cycle {n} {t} {str(bool(b)).lower()} ({z})'
    if k=="L":
        n,s=map(int,args)
        assert p.count(24)==1 and p[s]==24 and n<=maxn
        return f'.last {n} {slot(s)}'
    if k=="O":
        opened+=1
        assert parse(args[0])==p
        if opened in pumpids:
            i=pumpids[opened]; assert parse(pumpcodes[i])==p
            return f'.proven BB6.Agent7F1Pumps.p{i} BB6.Agent7F1Pumps.p{i}_never'
        rev,D=over.get(opened,(0,list(map(int,"0102030400"))))
        return masks(p,rev,D)
    assert k=="S"
    n,s=map(int,args)
    assert p[s]==24 and n<=maxn
    kids=[]
    for a in range(24):
        c=p.copy();c[s]=a;kids.append(read(c))
    return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(kids[a] for a in ORDER)+'])'
header='namespace BB6.Agent7F1'+tag+'\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
end='\nend BB6.Agent7F1'+tag+'\n'
p=parse(PARENT)
kind,n,s=next(lines).split(); assert kind=="S"; n,s=int(n),int(s)
counts["S"]+=1
(ROOT/f'F1{tag}Base.lean').write_text('import ThreeHoleAudit\nimport F1SiblingPumps\n'+header+f'''
abbrev wideParent : PartialMachine := fromCodes {p}
theorem wide_root : wideParent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem wide_nohalt : weightedTNFNoAssignedHalt wideParent :=
  BB6.Agent7FAR.DepthEight.fromCodes_noAssignedHalt _
abbrev wideChild (mv : Move) : PartialMachine := refine wideParent {slot(s)} (some mv)
theorem wideQuery : BB6.Agent31ThreeHole.queryOK {B} wideParent {n} {slot(s)} = true := by decide
'''+end)
for a in range(24):
    c=p.copy();c[s]=a; kid=read(c)
    name=f'kid{a:02}'
    (ROOT/f'F1{tag}Kid{a:02}.lean').write_text(f'import F1{tag}Base\n'+header+
       f'def {name} : Audit := {kid}\ntheorem check{a:02} : check {B} (wideChild {move(a)}) {name} = true := by decide\n'+end)
assert next(lines,None) is None
assert counts==Counter(dict(zip("SCLO",expected))),counts
assert opened==expected[-1]
imports=''.join(f'import F1{tag}Kid{a:02}\n' for a in range(24))
kids=','.join(f'kid{a:02}' for a in ORDER)
cases='\n'.join(f'  · exact check{a:02}' for a in range(24))
(ROOT/f'F1{tag}Data.lean').write_text(imports+header+f'''
def kids : Move → Audit := byMove [{kids}]
theorem kids_checked (mv : Move) : check {B} (wideChild mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree : Audit := .split {n} {slot(s)} kids
theorem tree_checked : check {B} wideParent tree = true := by
  change (BB6.Agent31ThreeHole.queryOK {B} wideParent {n} {slot(s)} &&
    BB6.Agent31ThreeHole.allMoves (fun mv => check {B} (wideChild mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨wideQuery, BB6.Agent31ThreeHole.allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate {B} wideParent 6 :=
  certified {B} wideParent tree wide_root wide_nohalt tree_checked
theorem all_completions_weighted : ∀ m, compatible wideParent m → WeightedBound {B} m :=
  certificate.sound
#print axioms tree_checked
#print axioms all_completions_weighted
'''+end)
print(counts)
