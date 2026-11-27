"""Generate parent coverage using FAR and Agent12 run-graph certificates.
Each generated graph is checked in Lean; no discovery result is trusted.
Usage: generate_graph_parents.py OUT parent_id [parent_id ...]
"""
from pathlib import Path
import base64,lzma,hashlib,json,subprocess,sys,tempfile
here=Path(__file__).resolve().parent
out=Path(sys.argv[1]).resolve()
out.mkdir(parents=True,exist_ok=True)
ids=list(map(int,sys.argv[2:]))
assert len(set(ids))==len(ids)>0 and all(0<=i<1212 for i in ids)
mask=base64.b64decode((here/'broad-far-parents.b64').read_text())
hard={int(x.split()[1]) for x in (here/'hard30.txt').read_text().splitlines()}
assert all(not mask[i] and i not in hard for i in ids)
graph_here=here.parent/'agent12-raw47-rungraph'
# Exact table-keyed original-semantics proofs, never matched by a scan ID alone.
# The .proven checker independently compares each literal table with ctr.
hard_specs={
    3312: ('Raw47Ternary3312','BB6.Agent2Raw47Ternary3312.ctr','BB6.Agent2Raw47Ternary3312.never',173),
    3932: ('Raw47Senary3932','BB6.Agent2Raw47Senary3932.ctr','BB6.Agent2Raw47Senary3932.never',187),
    23138: ('Raw47Binary23138','BB6.Agent2Raw47Binary23138.ctr','BB6.Agent2Raw47Binary23138.never',841),
    27039: ('Raw47QuaternaryPair','(BB6.Agent2Raw47QuaternaryPair.ctr true)','(BB6.Agent2Raw47QuaternaryPair.never true)',1062),
    27050: ('Raw47QuaternaryPair','(BB6.Agent2Raw47QuaternaryPair.ctr false)','(BB6.Agent2Raw47QuaternaryPair.never false)',1062),
}
hard_bank={}
for line in (graph_here/'hard10.txt').read_text().splitlines():
    n,t=line.split(); n=int(n)
    if n in hard_specs:
        module,partial,proof,parent=hard_specs[n]
        assert (parent,t) not in hard_bank
        hard_bank[parent,t]=(module,partial,proof,n)
assert len(hard_bank)==len(hard_specs)

# Nine previously kernel-checked source recurrences from Agent12. Keep
# the concrete table in the ledger; the Lean .proven gate checks it.
pump_specs = {
    13006: (667,'1RB1LE1RC0LA0RD1LE1LD0RC0LB0LF---0RC'),
    13224: (668,'1RB---1RC0LE0RD1LE1LD0RC0LB1LF---0LD'),
    16274: (694,'1RB0LD1RC---0RD1LE1LD0RC0LF1LA1RC0LE'),
    16326: (695,'1RB---1RC0RF0RD1LE1LD0RC0LF1LC1RA0LF'),
    19433: (775,'1RB1LE1RC0RD0RD1LE1LD0RC1LA1LF---0LB'),
    19504: (775,'1RB1LE1RC1RB0RD1LE1LD0RC1LA0LF---0LD'),
    25862: (957,'1RB1RE1RC0LA0RD1RA1LD0RC1LB1RF---0RB'),
    25895: (959,'1RB1RE1RC0RF0RD1RA1LD0RC1LF0LC---0LA'),
    25918: (959,'1RB1RE1RC0RF0RD1RA1LD0RC1LF1RB---0LA'),
}
for n,(parent,t) in pump_specs.items():
    prefix=f'BB6.Agent12Raw47Pumps.H{n}'
    assert len(t)==36 and (parent,t) not in hard_bank
    hard_bank[parent,t]=('Raw47NewPumps',prefix+'.ctr',prefix+'.never',n)
assert len(hard_bank)==len(hard_specs)+len(pump_specs)

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
    cert={(i,t):bank[j] for j,(i,t) in enumerate(leaves) if j in bank}
    # Stable identifiers independent of parent selection and batching.
    counts={}
    miss={}
    used_hard={}
    for j,(i,t) in enumerate(leaves):
        index=counts.get(i,0); counts[i]=index+1
        assert index<100000, (i,index)
        if j not in bank:
            key=(i,t.replace('_',''))
            if key in hard_bank:
                used_hard[i,t]=hard_bank[key]
            else:
                g=2000000+100000*i+index
                assert g not in miss
                miss[g]=(i,t)
    subprocess.run(['g++','-O3','-std=c++20',str(graph_here/'run_search.cpp'),'-o',str(work/'run_search')],check=True)
    def search(args,inp):
        run=subprocess.run([str(work/'run_search'),*args],input=inp,text=True,capture_output=True,check=True)
        return run.stdout,run.stderr
    inp=''.join(f'{g} {t.replace("_","")}\n' for g,(i,t) in miss.items())
    cheap,left=search(['10000','150'],inp)
    deep,left=search(['80000','999999'],left)
    # Exact soundness is independent of which search proposes the graph.
    # Use asymmetric candidates only for the remaining failures.
    asym,left=search(['asym','5000','50000'],left) if left.strip() else ('','')
    hits=cheap+deep+asym
    (out/'unresolved.txt').write_text(left)
    assert not left.strip(),left
    # Persist the compact witnesses, exact parent association and emitted proof source.
    (out/'graph-hits.txt').write_text(hits)
    (out/'graph-parents.json').write_text(json.dumps(miss,indent=2))
    (out/'hard-parents.json').write_text(json.dumps([
        {'parent':i,'table':t,'module':v[0],'partial':v[1],'proof':v[2],'historical_id':v[3]}
        for (i,t),v in sorted(used_hard.items())],indent=2)+'\n')
    graph={miss[int(line.split()[0])]:int(line.split()[0]) for line in hits.splitlines()}
    assert len(graph)==len(miss)
    assert len(leaves)==len(cert)+len(graph)+len(used_hard)
    with (out/'graphs.txt').open('w') as fp:
        subprocess.run([str(work/'run_search'),'emit'],input=hits,text=True,stdout=fp,check=True)
    subprocess.run([sys.executable,str(graph_here/'emit_graph.py'),str(out/'graphs.txt'),str(out)],check=True)
    print(f'Graph parents {ids}: {len(leaves)} open leaves, {len(cert)} FAR, {len(graph)} run-graph, {len(used_hard)} exact carry proofs')
def emit(t,i):
    tag,*a=t
    if tag=='cycle':return f'.cycle {a[0]} {a[1]} {b(a[2])} ({a[3]})'
    if tag=='last':return f'.last {a[0]} {slot(a[1])}'
    if tag=='split':return f'.split {a[0]} {slot(a[1])} (byMove [\n'+',\n'.join(emit(x,i) for x in a[2])+'\n])'
    if tag=='open':
        if (i,a[0]) in cert: return far(cert[i,a[0]],a[0])
        if (i,a[0]) in used_hard:
            _,partial,proof,_=used_hard[i,a[0]]
            return f'.proven {partial} {proof}'
        n=f'BB6.Agent12Raw47.Run{graph[i,a[0]]}'
        return f'.proven {n}.parent {n}.never'
    raise ValueError(t)
for i in ids:
    p=rows[i].replace('_',''); r=[]
    for s in range(12):
        x=p[3*s:3*s+3]
        if x!='---':r.append(f'  | {s//2},{b(s%2)} => some (some ⟨{b(int(x[0]))},{b(x[1]=="R")},{ord(x[2])-65}⟩)')
    modules=sorted(g for (j,t),g in graph.items() if j==i)
    hard_modules=sorted({v[0] for (j,t),v in used_hard.items() if j==i})
    source=''.join(f'import {m}\n' for m in hard_modules)+''.join(f'import Run{g}\n' for g in modules)+f'''import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent50.Raw47D3G{i}
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
end BB6.Agent50.Raw47D3G{i}
'''
    (out/f'Raw47D3G{i}.lean').write_text(source)

(out/'ids.txt').write_text('\n'.join(map(str,ids))+'\n')
print(f'Generated {len(ids)} complete mixed FAR/graph parent certificates.')
