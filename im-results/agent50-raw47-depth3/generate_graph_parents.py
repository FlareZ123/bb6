"""Generate parent coverage using FAR and Agent12 run-graph certificates.
Each generated graph is checked in Lean; no discovery result is trusted.
Usage: generate_graph_parents.py OUT [--partial] parent_id [parent_id ...]
"""
from pathlib import Path
import base64,lzma,hashlib,json,subprocess,sys,tempfile,functools
from shard_mixed_prefix import write_sharded
here=Path(__file__).resolve().parent
out=Path(sys.argv[1]).resolve()
out.mkdir(parents=True,exist_ok=True)
partial_mode='--partial' in sys.argv[2:]
ids=list(map(int,[x for x in sys.argv[2:] if x!='--partial']))
assert len(set(ids))==len(ids)>0 and all(0<=i<1212 for i in ids)
mask=base64.b64decode((here/'broad-far-parents.b64').read_text())
hard={int(x.split()[1]) for x in (here/'hard30.txt').read_text().splitlines()}
assert all(not mask[i] and i not in hard for i in ids)
graph_here=here.parent/'agent12-raw47-rungraph'
# Exact table-keyed original-semantics proofs, never matched by a scan ID alone.
# The .proven checker independently compares each literal table with ctr.
hard_specs={
    5258: ('Raw47Growth5258','BB6.Agent12Raw47Growth5258.ctr','BB6.Agent12Raw47Growth5258.never',207),
    9918: ('Raw47ParityTriple','(BB6.Agent12Raw47ParityTriple.ctr BB6.Agent12Raw47ParityTriple.Kind.ra)','(BB6.Agent12Raw47ParityTriple.never BB6.Agent12Raw47ParityTriple.Kind.ra)',547),
    9919: ('Raw47ParityTriple','(BB6.Agent12Raw47ParityTriple.ctr BB6.Agent12Raw47ParityTriple.Kind.rc)','(BB6.Agent12Raw47ParityTriple.never BB6.Agent12Raw47ParityTriple.Kind.rc)',547),
    9920: ('Raw47ParityTriple','(BB6.Agent12Raw47ParityTriple.ctr BB6.Agent12Raw47ParityTriple.Kind.lc)','(BB6.Agent12Raw47ParityTriple.never BB6.Agent12Raw47ParityTriple.Kind.lc)',547),
    3423: ('Raw47Complement3423','BB6.Agent12Raw47Complement3423.ctr','BB6.Agent12Raw47Complement3423.never',174),
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

# Agent2 shared binary counter, exact one-hole tables. The two variants
# have identical macro orbit; the undefined row is never read.
binary_specs = {
    95200006: (932, '1RB1LB1RC0LE0RD1RA1LD0RC0LF---0RD1RB', 'true'),
    95700003: (937, '1RB1LE1RC---0RD1RA1LD0RC0LF0LE0RD1RB', 'false'),
}
for n,(parent,t,v) in binary_specs.items():
    prefix='BB6.Agent2Raw47Binary932937'
    assert len(t)==36 and (parent,t) not in hard_bank
    hard_bank[parent,t]=('Raw47Binary932937',f'({prefix}.ctr {v})',f'({prefix}.never {v})',n)
assert len(hard_bank)==len(hard_specs)+len(pump_specs)+len(binary_specs)

raw=(here/'raw47-depth3.open').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d'
rows=raw.decode().splitlines()
def b(x):return str(bool(x)).lower()
def slot(s):return f'({s//2},{b(s%2)})'
@functools.lru_cache(maxsize=None)
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
    subprocess.run(['g++','-O3','-std=c++20',str(here/'run_portfolio.cpp'),'-o',str(work/'run_portfolio')],check=True)
    def search(args,inp):
        exe='run_portfolio' if args[0]=='portfolio' else 'run_search'
        run=subprocess.run([str(work/exe),*args],input=inp,text=True,capture_output=True,check=True)
        return run.stdout,run.stderr
    inp=''.join(f'{g} {t.replace("_","")}\n' for g,(i,t) in miss.items())
    portfolio,left=search(['portfolio',str(here/'graph-portfolio.txt'),'10000'],inp)
    cheap,left=search(['10000','150'],left)
    deep,left=search(['80000','999999'],left)
    # Exact soundness is independent of which search proposes the graph.
    # Use asymmetric candidates only for the remaining failures.
    asym,left=search(['asym','5000','50000'],left) if left.strip() and not partial_mode else ('',left)
    hits=portfolio+cheap+deep+asym
    print(f'Portfolio: {len(portfolio.splitlines())}/{len(miss)} novel graph candidates',flush=True)
    (out/'unresolved.txt').write_text(left)
    if not partial_mode: assert not left.strip(),left
    # Persist the compact witnesses, exact parent association and emitted proof source.
    (out/'graph-hits.txt').write_text(hits)
    (out/'graph-parents.json').write_text(json.dumps(miss,indent=2))
    (out/'hard-parents.json').write_text(json.dumps([
        {'parent':i,'table':t,'module':v[0],'partial':v[1],'proof':v[2],'historical_id':v[3]}
        for (i,t),v in sorted(used_hard.items())],indent=2)+'\n')
    graph={miss[int(line.split()[0])]:int(line.split()[0]) for line in hits.splitlines()}
    unresolved={miss[int(line.split()[0])] for line in left.splitlines()}
    assert set(graph).isdisjoint(unresolved)
    assert set(graph)|unresolved==set(miss.values())
    assert len(leaves)==len(cert)+len(graph)+len(used_hard)+len(unresolved)
    (out/'unresolved-parents.json').write_text(json.dumps([
        {'parent':i,'table':t} for i,t in sorted(unresolved)],indent=2)+'\n')
    with (out/'graphs.txt').open('w') as fp:
        subprocess.run([str(work/'run_search'),'emit'],input=hits,text=True,stdout=fp,check=True)
    graph_names={}
    if hits.strip():
        subprocess.run([sys.executable,str(graph_here/'emit_graph.py'),str(out/'graphs.txt'),str(out)],check=True)
        for line in hits.splitlines():
            g=int(line.split()[0])
            old=f'Run{g}'
            # Same table/parameters keep the same module identity. A different
            # proof proposal never collides with a prior partial export.
            name=old+'_'+hashlib.sha256(line.encode()).hexdigest()[:16]
            src=out/(old+'.lean')
            (out/(name+'.lean')).write_text(src.read_text().replace('.'+old,'.'+name))
            src.unlink()
            graph_names[g]=name
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
        n='BB6.Agent12Raw47.'+graph_names[graph[i,a[0]]]
        return f'.proven {n}.parent {n}.never'
    raise ValueError(t)
def packed_key(t):
    t=t.replace('_','')
    assert len(t)==36
    return sum((25 if t[j:j+3]=='---' else 4*(ord(t[j+2])-65)+2*int(t[j])+(t[j+1]=='R'))*26**(j//3)
               for j in range(0,36,3))

def unknown_count(t,i):
    tag,*a=t
    if tag=='split': return sum(unknown_count(c,i) for c in a[2])
    return int(tag=='open' and (i,a[0]) in unresolved)

def emit_partial(t,i):
    if unknown_count(t,i)==0: return '.closed ('+emit(t,i)+')'
    tag,*a=t
    if tag=='open': return '.unresolved'
    assert tag=='split'
    return f'.split {a[0]} {slot(a[1])} (byPartialMove [\n'+',\n'.join(emit_partial(c,i) for c in a[2])+'\n])'

full_ids=[]
partial_ids=[]
for i in ids:
    nleft=unknown_count(trees[i],i)
    assert nleft==sum(j==i for j,_ in unresolved)
    if nleft: partial_ids.append((i,nleft))
    else: full_ids.append(i)
    p=rows[i].replace('_',''); r=[]
    for s in range(12):
        x=p[3*s:3*s+3]
        if x!='---':r.append(f'  | {s//2},{b(s%2)} => some (some ⟨{b(int(x[0]))},{b(x[1]=="R")},{ord(x[2])-65}⟩)')
    modules=sorted(g for (j,t),g in graph.items() if j==i)
    hard_modules=sorted({v[0] for (j,t),v in used_hard.items() if j==i})
    kind='U' if nleft else 'G'
    source=''.join(f'import {m}\n' for m in hard_modules)+''.join(f'import {graph_names[g]}\n' for g in modules)+('import PartialPrefixAudit\nimport FastKey\n' if nleft else '')+f'''import CanonicalPartial
import QuickPrefixAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent50.Raw47D3{kind}{i}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent50TNFPilot BB6.Agent47CanonicalFrontier
{'open BB6.Agent50PartialPrefix BB6.Agent47PartialAudit' if nleft else ''}

def p : PartialMachine := fun s => match s.1.val,s.2 with
'''+ '\n'.join(r)+f'''
  | _,_ => none
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

'''
    if nleft:
        expected_keys=sorted(packed_key(t) for j,t in unresolved if j==i)
        assert len(expected_keys)==nleft and len(set(expected_keys))==nleft
        source+=f'''def tree : PartialAudit := {emit_partial(trees[i],i)}
theorem quickChecked : BB6.Agent50QuickPrefix.quickPartialCheck 10006 p tree = true := by decide +kernel
theorem checked : partialPrefixCheck 10006 p tree = true := (BB6.Agent50QuickPrefix.quickPartialCheck_eq 10006 p tree).symm.trans quickChecked
def remaining := partialResiduals p tree
theorem remaining_count : remaining.length = {nleft} := by decide
def remainingKeys := remaining.map fun e => BB6.Agent50FastKey.tableCode e.2
def expectedKeys : List Nat := {expected_keys}
theorem remaining_key_set :
    remainingKeys.all (fun k => expectedKeys.contains k) = true ∧
    expectedKeys.all (fun k => remainingKeys.contains k) = true := by decide +kernel
theorem local_sound (m : Machine) (hm : TNFQuotientCompatible p m) :
    WeightedBound 10006 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m :=
  partialQuotientSound 10006 p tree root nohalt checked m hm
#print axioms remaining_count
#print axioms remaining_key_set
#print axioms local_sound
'''
    else:
        source+=f'''def tree : Audit := {emit(trees[i],i)}
theorem quickChecked : BB6.Agent50QuickPrefix.quickCheck 10006 p tree = true := by decide +kernel
theorem checked : prefixCheck 10006 p tree = true := (BB6.Agent50QuickPrefix.quickCheck_eq 10006 p tree).symm.trans quickChecked
theorem bound (m : Machine) (hm : compatible p m) : WeightedBound 10006 m :=
  (certifiedZip 10006 p tree root nohalt (by simpa only [prefixCheck_eq] using checked)).sound m hm
theorem all_quotient (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 10006 m :=\n  quotientSafe root bound m hm\n#print axioms all_quotient
'''
    source+=f'end BB6.Agent50.Raw47D3{kind}{i}\n'
    if len(source)>45000 and trees[i][0]=='split':
        write_sharded(out,i,trees[i],source,kind,emit,emit_partial)
    else:
        (out/f'Raw47D3{kind}{i}.lean').write_text(source)

(out/'ids.txt').write_text(''.join(f'{i}\n' for i in full_ids))
(out/'partial-ids.txt').write_text(''.join(f'{i} {n}\n' for i,n in partial_ids))
print(f'Generated {len(full_ids)} complete and {len(partial_ids)} partial mixed FAR/graph parent certificates.')
