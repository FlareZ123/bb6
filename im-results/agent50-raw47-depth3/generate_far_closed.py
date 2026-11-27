"""Regenerate FAR-augmented complete Raw47 depth-three cylinders from exact cut source.
Usage: python generate_far_closed.py WORKDIR OUTPUTDIR
WORKDIR contains d3.open, d3.json, full.json (cut depth 7), and farbank executable.
"""
import json,pathlib,sys,subprocess,hashlib,collections
root=pathlib.Path(sys.argv[1]).resolve();out=pathlib.Path(sys.argv[2]).resolve();out.mkdir(parents=True,exist_ok=True)
assert hashlib.sha256((root/'d3.open').read_bytes()).hexdigest()=='4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d'
tables=(root/'d3.open').read_text().splitlines()
d3=json.loads((root/'d3.json').read_text());full=json.loads((root/'full.json').read_text());roots=[]
def collect(a,b):
    if a[0]=='open': roots.append(b)
    elif a[0]=='split':
        assert a[:3]==b[:3]
        for x,y in zip(a[3],b[3]):collect(x,y)
collect(d3,full);assert len(roots)==len(tables)==1212
def leaves(t):
    if t[0]=='open':yield t[1]
    elif t[0]=='split':
        for x in t[3]:yield from leaves(x)
small=[]
for i,t in enumerate(roots):
    xs=list(leaves(t))
    if 0<len(xs)<=5:small.extend((i,x) for x in xs)
assert len(small)==441
inp=''.join(f'{j} {x.replace("_","")}\n' for j,(_,x) in enumerate(small))
run=subprocess.run([str(root/'farbank'),'5'],input=inp,text=True,capture_output=True,check=True)
(out/'small.far').write_text(run.stdout)
bank={int(line.split()[0]):line.split()[1] for line in run.stdout.splitlines()}
assert len(bank)==410
bad={i for j,(i,x) in enumerate(small) if j not in bank}
good=sorted({i for i,x in small}-bad)
assert len(good)==143
cert={(i,x):bank[j] for j,(i,x) in enumerate(small) if j in bank}
def b(x):return str(bool(x)).lower()
def slot(s):return f'({s//2},{b(s%2)})'
def far(code,table):
    rev=int(code[0]);D=list(map(int,code[1:]));n=len(D)//2
    assert 1<=n<=5 and len(D)==2*n and 0<=rev<=1 and all(0<=x<n for x in D)
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
def emit(t,i):
    tag,*a=t
    if tag=='cycle':return f'.cycle {a[0]} {a[1]} {b(a[2])} ({a[3]})'
    if tag=='last':return f'.last {a[0]} {slot(a[1])}'
    if tag=='split':return f'.split {a[0]} {slot(a[1])} (byMove [\n'+',\n'.join(emit(x,i) for x in a[2])+'\n])'
    if tag=='open':return far(cert[i,a[0]],a[0])
    raise ValueError(t)
for i in good:
    table=tables[i];rows=[]
    for s in range(12):
        x=table.replace('_','')[3*s:3*s+3]
        if x!='---':rows.append(f'  | {s//2},{b(s%2)} => some (some ⟨{b(int(x[0]))},{b(x[1]=="R")},{ord(x[2])-65}⟩)')
    source=f'''import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50.Raw47D3F{i}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
'''+ '\n'.join(rows)+'''
  | _,_ => none
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

def tree : Audit := '''+emit(roots[i],i)+'''
theorem checked : prefixCheck 1006 p tree = true := by decide
theorem bound (m : Machine) (hm : compatible p m) : WeightedBound 1006 m :=
  (certifiedZip 1006 p tree root nohalt (by simpa only [prefixCheck_eq] using checked)).sound m hm
theorem all_quotient (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 1006 m :=
  quotientSafe root bound m hm
#print axioms all_quotient
end BB6.Agent50.Raw47D3F'''+str(i)+'\n'
    (out/f'Raw47D3F{i}.lean').write_text(source)
print('complete FAR-augmented parents:',len(good))
