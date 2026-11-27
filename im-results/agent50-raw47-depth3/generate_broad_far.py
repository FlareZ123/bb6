"""Source-checked broad FAR-only parent proofs, fixed 674 candidates, 8 shards."""
from pathlib import Path
import base64,lzma,hashlib,json,subprocess,sys,tempfile
here=Path(__file__).resolve().parent
out=Path(sys.argv[1]).resolve()
out.mkdir(parents=True,exist_ok=True)
shard=int(sys.argv[2])
assert 0<=shard<8
mask=base64.b64decode((here/'broad-far-parents.b64').read_text())
assert len(mask)==1212 and set(mask)=={0,1} and sum(mask)==674
ids=[i for i,v in enumerate(mask) if v][shard::8]
raw=(here/'raw47-depth3.open').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d'
rows=raw.decode().splitlines()
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
    bdata=lzma.decompress(base64.b64decode((here/'broad-far-bank.xz.b64').read_text()))
    codes=bdata.decode().split()
    assert len(codes)==len(set(codes))==332
    assert all(c[0] in '01' and len(c)%2==1 and c[1]=='0' and all(0<=int(x)<(len(c)-1)//2 for x in c[1:]) for c in codes)
    (work/'bank').write_bytes(bdata)
    subprocess.run(['g++','-O3','-std=c++20',str(here.parent/'agent32-linear-side-cycle/enumerate_tnf.cpp'),'-o',str(work/'enum')],check=True)
    subprocess.run(['g++','-O3','-std=c++20',str(here.parent/'agent19-raw40-cut/farbank.cpp'),'-o',str(work/'far')],check=True)
    trees={}; leaves=[]
    for i in ids:
        subprocess.run([str(work/'enum'),rows[i],'10000'],cwd=work,stdout=subprocess.DEVNULL,check=True)
        trees[i]=json.loads((work/'tree.json').read_text())
        leaves.extend((i,t) for t in (work/'open.txt').read_text().splitlines())
    inp=''.join(f'{j} {t.replace("_","")}\n' for j,(_,t) in enumerate(leaves))
    run=subprocess.run([str(work/'far'),'0',str(work/'bank')],input=inp,text=True,capture_output=True,check=True)
    bank={int(line.split()[0]):line.split()[1] for line in run.stdout.splitlines()}
    assert len(bank)==len(leaves),run.stderr
    cert={(i,t):bank[j] for j,(i,t) in enumerate(leaves)}
def emit(t,i):
    tag,*a=t
    if tag=='cycle':return f'.cycle {a[0]} {a[1]} {b(a[2])} ({a[3]})'
    if tag=='last':return f'.last {a[0]} {slot(a[1])}'
    if tag=='split':return f'.split {a[0]} {slot(a[1])} (byMove [\n'+',\n'.join(emit(x,i) for x in a[2])+'\n])'
    if tag=='open':return far(cert[i,a[0]],a[0])
    raise ValueError(t)
for i in ids:
    p=rows[i].replace('_',''); r=[]
    for s in range(12):
        x=p[3*s:3*s+3]
        if x!='---':r.append(f'  | {s//2},{b(s%2)} => some (some ⟨{b(int(x[0]))},{b(x[1]=="R")},{ord(x[2])-65}⟩)')
    source=f'''import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent50.Raw47D3FAR{i}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent50TNFPilot BB6.Agent47CanonicalFrontier

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
theorem all_quotient (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 10006 m :=\n  quotientSafe root bound m hm\n#print axioms all_quotient
end BB6.Agent50.Raw47D3FAR{i}
'''
    (out/f'Raw47D3FAR{i}.lean').write_text(source)

(out/'ids.txt').write_text('\n'.join(map(str,ids))+'\n')
print(f'Shard {shard}: {len(ids)} complete parent certificates, {len(leaves)} FAR leaves.')
