"""Generate exact weighted parent certificates for the 17 pump-closed D3 cylinders.

Run from any directory: python generate_pump_parents.py OUTPUTDIR
All searches are only witness discovery; the generated prefixCheck equality
is the trusted coverage test.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile
here=Path(__file__).resolve().parent
repo=here.parents[1]
out=Path(sys.argv[1]).resolve()
out.mkdir(parents=True,exist_ok=True)
ids=[29,97,109,116,171,176,216,237,260,303,351,517,597,933,1039,1050,1060]
raw=(here/'raw47-depth3.open').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d'
rows=raw.decode().splitlines()
hard=[line.split()[2] for line in (here/'hard30.txt').read_text().splitlines()]
pumpids=[int(line.split()[0]) for line in (here/'pump-recipes.txt').read_text().splitlines()]
pumps={hard[i]:i for i in pumpids}

def b(x):return str(bool(x)).lower()
def slot(s):return f'({s//2},{b(s%2)})'
def far(code,table):
    rev=int(code[0]);D=list(map(int,code[1:]));n=len(D)//2
    assert rev in (0,1) and 1<=n<=5 and len(D)==2*n and D[0]==0 and all(0<=x<n for x in D)
    N=6*n+1;H=N-1;halt=1<<H;T=[0]*(2*N);T[H]=T[N+H]=halt;rules=[]
    p=table.replace('_','');p=[p[i:i+3] for i in range(0,36,3)]
    for l in range(n):
        for q in range(6):
            for a in range(2):
                m=p[2*q+a];dst=a*N+6*l+q
                if m=='---':T[dst]=halt;continue
                w,r,k=int(m[0]),m[1]=='R',ord(m[2])-65
                if r!=bool(rev):T[dst]=1<<(6*D[2*l+w]+k)
                else:
                    for j in range(n):
                        for e in range(2):
                            if D[2*j+e]==l:rules.append((dst,e*N+6*j+k,w*N))
    while True:
        z=halt
        while True:
            old=z
            for j in range(N):
                if T[j]&z:z|=1<<j
            if old==z:break
        assert not z&1
        changed=False
        for dst,src,off in rules:
            v,bits=T[dst],T[src]
            while bits:
                k=(bits&-bits).bit_length()-1;v|=T[off+k];bits&=bits-1
            if v!=T[dst]:T[dst]=v;changed=True
        if not changed:return f'.far {b(rev)} {n} ⟨0,{D},{T[:N]},{T[N:]},{z}⟩'

with tempfile.TemporaryDirectory() as temp:
    work=Path(temp)
    subprocess.run(['g++','-O3','-std=c++20',str(here.parent/'agent32-linear-side-cycle/enumerate_tnf.cpp'),'-o',str(work/'enum')],check=True)
    subprocess.run(['g++','-O3','-std=c++20',str(here.parent/'agent19-raw40-cut/farbank.cpp'),'-o',str(work/'far')],check=True)
    trees={}; leaves=[]
    for i in ids:
        subprocess.run([str(work/'enum'),rows[i],'10000'],cwd=work,stdout=subprocess.DEVNULL,check=True)
        trees[i]=json.loads((work/'tree.json').read_text())
        leaves.extend((i,t) for t in (work/'open.txt').read_text().splitlines())
    assert len(leaves)==57
    residual=[(i,t) for i,t in leaves if t not in pumps]
    assert len(residual)==34
    inp=''.join(f'{j} {t.replace("_","")}\n' for j,(_,t) in enumerate(residual))
    run=subprocess.run([str(work/'far'),'5'],input=inp,text=True,capture_output=True,check=True)
    bank={int(line.split()[0]):line.split()[1] for line in run.stdout.splitlines()}
    assert len(bank)==len(residual),run.stderr
    cert={(i,t):bank[j] for j,(i,t) in enumerate(residual)}

def emit(t,i):
    tag,*a=t
    if tag=='cycle':return f'.cycle {a[0]} {a[1]} {b(a[2])} ({a[3]})'
    if tag=='last':return f'.last {a[0]} {slot(a[1])}'
    if tag=='split':return f'.split {a[0]} {slot(a[1])} (byMove [\n'+',\n'.join(emit(x,i) for x in a[2])+'\n])'
    if tag=='open':
        row=a[0]
        if row in pumps:
            h=f'BB6.Agent50Raw47Pumps.H{pumps[row]}'
            return f'.proven {h}.ctr {h}.never'
        return far(cert[i,row],row)
    raise ValueError(t)

with (out/'Raw47Pumps.lean').open('w') as f:
    subprocess.run([sys.executable,str(here/'generate_pumps.py')],stdout=f,check=True)

for i in ids:
    p=rows[i].replace('_',''); r=[]
    for s in range(12):
        x=p[3*s:3*s+3]
        if x!='---':r.append(f'  | {s//2},{b(s%2)} => some (some ⟨{b(int(x[0]))},{b(x[1]=="R")},{ord(x[2])-65}⟩)')
    source=f'''import ZipPrefixAudit
import Raw47Pumps
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent50.Raw47D3P{i}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent50TNFPilot

def p : PartialMachine := fun s => match s.1.val,s.2 with
'''+ '\n'.join(r)+f'''
  | _,_ => none
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

def tree : Audit := {emit(trees[i],i)}
theorem checked : prefixCheck 10006 p tree = true := by decide
theorem bound (m : Machine) (hm : compatible p m) : WeightedBound 10006 m :=
  (certifiedZip 10006 p tree root nohalt (by simpa only [prefixCheck_eq] using checked)).sound m hm
#print axioms bound
end BB6.Agent50.Raw47D3P{i}
'''
    (out/f'Raw47D3P{i}.lean').write_text(source)
print(f'Generated {len(ids)} complete parent certificates, {len(residual)} FAR and {len(leaves)-len(residual)} pump leaves.')
