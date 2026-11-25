import json,sys
from pathlib import Path

def parse(code): return [code.replace('_','')[i:i+3] for i in range(0,36,3)]
def show(p): return '_'.join(''.join(p[i:i+2]) for i in range(0,12,2))
def move(i): return str(i//12)+('R' if i%12>=6 else 'L')+chr(65+i%6)
def mv(i): return f'⟨{str(bool(i//12)).lower()},{str(i%12>=6).lower()},{i%6}⟩'
def slot(i): return f'({i//2},{str(bool(i%2)).lower()})'
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

src=Path(sys.argv[1]);output=Path(sys.argv[2]);output.mkdir(exist_ok=True);parent=parse(sys.argv[3]);tree=json.loads((src/'tree.json').read_text());bank={int(i):c for i,c in (x.split() for x in (src/'far5.txt').read_text().splitlines())};opens=(src/'open.txt').read_text().splitlines();it=iter(enumerate(opens));B=int(sys.argv[4]);mod=sys.argv[5]

if (src/'far_extra.txt').exists():
    bank.update({int(i):c for i,c in (x.split() for x in (src/'far_extra.txt').read_text().splitlines())})

def gen(t,p):
    if t[0]=='cycle':return f'.cycle {t[1]} {t[2]} {str(t[3]).lower()} ({t[4]})'
    if t[0]=='last':return f'.last {t[1]} {slot(t[2])}'
    if t[0]=='open':
        i,code=next(it);assert t[1]==code==show(p)
        if mod=='Raw40RE1RE' and code=='1RB1RE_1RC0RF_0RD1RB_1LD1LA_1LF1RE_---0LA':
            return '.proven BB6.Agent19Raw40.RE1RE584.table BB6.Agent19Raw40.RE1RE584.never'
        return far(bank[i],p)
    assert t[0]=='split';n,s,children=t[1:];assert p[s]=='---' and len(children)==24
    return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(gen(k,p[:s]+[move(i)]+p[s+1:]) for i,k in enumerate(children))+'])'

base=('import Raw40RE1RE584\n' if mod=='Raw40RE1RE' else '')+f'''import ZipPrefixAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.{mod}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit
-- {show(parent)}
def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
'''
for i,v in enumerate(parent):
    if v!='---':base+=f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(v[0]=="1").lower()},{str(v[1]=="R").lower()},{ord(v[2])-65}⟩)\n'
base+='  | _,_ => none\n'
base+='''theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
end BB6.Agent19Raw40.'''+mod+'\n'
(output/f'{mod}Base.lean').write_text(base)
n,s,children=tree[1:];assert len(children)==24
def size(t):return 1+sum(map(size,t[3])) if t[0]=='split' else 1

def gen_sharded(t,p,name,expr,lines):
    lines.append(f'abbrev p{name} := {expr}')
    if size(t)<=(120 if mod=='Raw40RE1RE' else 180):
        lines.append(f'def t{name} : Audit := {gen(t,p)}')
        lines.append(f'theorem c{name} : zipCheck {B} p{name} t{name} = true := by\n  rw [← prefixCheck_eq]\n  decide')
        return
    assert t[0]=='split';n,s,children=t[1:];names=[]
    for i,k in enumerate(children):
        nm=f'{name}_{i:02}';names.append(nm)
        gen_sharded(k,p[:s]+[move(i)]+p[s+1:],nm,f'refine p{name} {slot(s)} (some {mv(i)})',lines)
    lines.append(f'def k{name} : Move → Audit := byMove [{",".join("t"+nm for nm in names)}]')
    lines.append(f'def t{name} : Audit := .split {n} {slot(s)} k{name}')
    lines.append(f'theorem q{name} : zipQueryOK {B} p{name} {n} {slot(s)} = true := by decide')
    proof=f'theorem ck{name} (m : Move) : zipCheck {B} (refine p{name} {slot(s)} (some m)) (k{name} m) = true := by\n  rcases m with ⟨w,r,q⟩\n  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl\n  all_goals cases w <;> cases r\n'
    for q in range(6):
        for w in range(2):
            for r in range(2):proof+=f'  · exact c{names[12*w+6*r+q]}\n'
    lines.append(proof.rstrip())
    lines.append(f'theorem c{name} : zipCheck {B} p{name} t{name} = true := by\n  simp only [t{name},zipCheck,q{name},Bool.true_and]\n  exact allMoves_of _ ck{name}')

for i,k in enumerate(children):
    q=parent[:s]+[move(i)]+parent[s+1:];lines=[]
    gen_sharded(k,q,str(i),f'refine p {slot(s)} (some {mv(i)})',lines)
    txt=f'''import {mod}Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.{mod}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit
'''+"\n".join(lines)+f'\nend BB6.Agent19Raw40.{mod}\n';(output/f'{mod}Kid{i:02}.lean').write_text(txt)
assert next(it,None) is None
end=''.join(f'import {mod}Kid{i:02}\n' for i in range(24))+f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.{mod}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit

def kids : Move → Audit := byMove [{','.join('t'+str(i) for i in range(24))}]
def tree : Audit := .split {n} {slot(s)} kids

theorem query : zipQueryOK {B} p {n} {slot(s)} = true := by decide

theorem kids_checked (m : Move) : zipCheck {B} (refine p {slot(s)} (some m)) (kids m) = true := by
  rcases m with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
'''
for q in range(6):
    for w in range(2):
        for r in range(2):end+=f'  · exact c{12*w+6*r+q}\n'
end+=f'''
theorem checked : zipCheck {B} p tree = true := by
  simp only [tree,zipCheck,query,Bool.true_and]
  exact allMoves_of _ kids_checked

noncomputable def certificate : WeightedTNFCertificate {B} p 6 :=
  certifiedZip {B} p tree root nohalt checked

theorem all : ∀ m, compatible p m → WeightedBound {B} m := certificate.sound

#print axioms checked
#print axioms all
end BB6.Agent19Raw40.{mod}
'''
(output/f'{mod}All.lean').write_text(end)
