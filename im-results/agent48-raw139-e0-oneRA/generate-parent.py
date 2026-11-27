#!/usr/bin/env python3
"""Generate a complete source candidate from the fixed witness manifest.
Run from the repository root, with the existing package6.py and blockcert.py
directories on PYTHONPATH. The emitted finite checks must pass Lean.
"""
import base64,collections,functools,hashlib,inspect,json,lzma,pathlib,re,sys
import package6

base=pathlib.Path(__file__).resolve().parent
part,spec=map(lambda p:json.loads(pathlib.Path(p).read_text()),sys.argv[1:3])
work=pathlib.Path(sys.argv[3]);imports=work/'imports';ext=work/'extern';original=work/'ordinary'
for d in (imports,ext,original):d.mkdir(parents=True,exist_ok=True)
raw=lzma.decompress(base64.b64decode((base/'sparse-models.json.xz.b64').read_text()))
assert hashlib.sha256(raw).hexdigest()=='175ac21a37d5fe0202399d8c485cc545cc36c61be0ef369e1738691ce7c37bb7'
for name,code in json.loads(raw).items():
    assert re.fullmatch(r'OneRASparse(?:Block)?[234]\.lean',name)
    (ext/name).write_text(code)

def pack(xs,b):return sum(x<<(b*i) for i,x in enumerate(xs))
def packed_tree(name,rows):
    chunks=[]
    for i in range(0,len(rows),16):
        vals=rows[i:i+16];bits=max(1,max(vals).bit_length())
        chunks.append((bits,pack(vals,bits)))
    def tree(lo,hi):
        if hi-lo==1:
            b,v=chunks[lo];return f'({b},{hex(v)})'
        mid=(lo+hi)//2;return f'if i < {mid} then ({tree(lo,mid)}) else ({tree(mid,hi)})'
    return f'def {name}Chunks (i : Nat) : Nat × Nat := {tree(0,len(chunks))}\ndef {name} (i : Nat) : Nat := if i < {len(rows)} then let p := {name}Chunks (i/16); (p.2 >>> (p.1*(i%16))) % (2^p.1) else 0\n'

recipes={i:r for r,ids in spec['block_groups'] for i in ids}
assert len(recipes)==sum(len(ids) for _,ids in spec['block_groups'])
assert len(recipes)=={'Raw139E0OneRA':8205,'Raw139E0OneLD':17501}[spec['prefix']]
def sparse_source(i,t,c):
    w=c['width'];A=2**w;D,N=c['left_states'],c['right_nodes'];d,n=D-1,N-1
    ns=f'BB6.Agent48F1OneRABlocks.H{i}'
    flip=recipes[i][4]
    push,ctrl,aux,pred,edges,zn=(c[k] for k in ('push','ctrl','aux','pred','edges','zeroNext'))
    L=f'namespace {ns}\nopen BB6.Agent48Sparse{w}\n'
    L+='def machine : BB6BlockFAR.Table := fun q b =>\n  match q.val,b with\n'
    for j,m in enumerate(c['moves']):
        L+=f'  | {j//2},{str(bool(j%2)).lower()} => '+('none' if m is None else f'some ⟨{str(bool(m[0])).lower()},{str(bool(m[1])).lower()},{m[2]}⟩')+'\n'
    L+='  | _,_ => none\n'
    L+='def unpack : Nat → Nat → Nat → List Nat\n  | 0,_,_ => []\n  | k+1,b,x => if x = 0 then [] else (x % 2^b).pred :: unpack k b (x >>> b)\n'
    L+=f'def pairs (fuel bits code : Nat) : List (Nat × Nat) := (unpack fuel bits code).map fun x => (x%{A},x/{A}+1)\n'
    bits=max(D,N).bit_length()+w
    L+=packed_tree('pushData',[pack([a+A*(v-1)+1 for a,v in enumerate(push[l*A:l*A+A]) if v],bits) for l in range(D)])
    L+=f'def pushRows (l : Nat) : List (Nat × Nat) := pairs {A} {bits} (pushData l)\n'
    L+=packed_tree('ctrlData',ctrl)+packed_tree('auxData',aux)+packed_tree('zeroNextCodes',zn)
    pb=(D*A).bit_length();pc=max(1,max(map(len,pred)))
    L+=packed_tree('predData',[pack([x+1 for x in row],pb) for row in pred])
    L+=f'def predecessorCodes (l : Nat) : List Nat := unpack {pc} {pb} (predData l)\n'
    eb=N.bit_length();ec=max(1,max(map(len,edges)));rowbits=w+eb*ec+1
    L+=packed_tree('edgeData',[pack([a+A*pack([v+1 for v in row],eb)+1 for a in range(A) if (row:=edges[v*A+a])],rowbits) for v in range(N)])
    L+=f'def edgeRows (v : Nat) : List (Nat × List Nat) := (unpack {A} {rowbits} (edgeData v)).map fun x => (x%{A},unpack {ec} {eb} (x/{A}))\n'
    zeros=sum(1<<v for v in c['zero_states'])
    L+=f'def cert : ActiveData {d} {n} := {{ start := 0, pushRows := pushRows, controlCodes := ctrlData, auxiliaryCodes := auxData, predecessorCodes := predecessorCodes, edgeRows := edgeRows, zeroCodes := {zeros}, zeroNextCodes := zeroNextCodes }}\n'
    L+='theorem base_ok : cert.baseCheck = true := by decide +kernel\n'
    for label,fn in [('pred','cert.fastPredAt'),('rows','(cert.fastRowsAt machine)')]:
        def proof(lo,length):
            nonlocal L
            tag=f'{label}_{lo}_{length}'
            if length<=8:L+=f'theorem {tag} : rangeCheck {d} {fn} {lo} {length} = true := by decide +kernel\n'
            else:
                m=length//2;a=proof(lo,m);b=proof(lo+m,length-m)
                L+=f'theorem {tag} : rangeCheck {d} {fn} {lo} {length} = true := rangeCheck_join {d} {fn} {lo} {m} {length-m} {a} {b}\n'
            return tag
        tag=proof(0,D);L+=f'theorem {label}_full : (List.finRange {D}).all {fn} = true := rangeCheck_full _ _ {tag}\n'
    L+='theorem valid : cert.Valid machine := ⟨base_ok,pred_full,rows_full⟩\n'
    L+='theorem forever : ∀ k, ∃ c, BB6BlockFAR.run machine k BB6BlockFAR.primBlank = some c := cert.sound machine valid\n'
    L+=f'def ctr : BB6Coverage.PartialMachine := BB6Coverage.FAR.fromCodes {t}\n'
    L+='theorem same : '+('BB6Coverage.FAR.reflectPartial ctr' if flip else 'ctr')+' = BB6BlockFAR.partialTable machine := BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide +kernel)\n'
    L+='theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible ctr m) : BB6Coverage.NeverHalts m := '
    if flip:L+='BB6Coverage.FAR.reflectNever m (BB6BlockFAR.transfer_never machine _ (by simpa only [← same] using BB6Coverage.FAR.reflectCompatible ctr m hm) forever)\n'
    else:L+='BB6BlockFAR.transfer_never machine m (by simpa only [← same] using hm) forever\n'
    return L+f'end {ns}\n'

# Reuse the checked parent-tree emitter, only switching the block witness
# representation and allowing mirrored witnesses. No alteration to split order,
# first-hole replay or checker semantics.
spec.setdefault('external_module_by_namespace',{'BB6Coverage.Agent48.H4620':'H4620'})
package6.block_source=sparse_source
src=inspect.getsource(package6.make)
old='            assert not f  # block_source transfers the unreflected table\n'
assert src.count(old)==1
src=src.replace(old,'')
exec(compile(src,'package6.make with sparse emitter','exec'),package6.__dict__)
package6.make(spec,part,original)
for p in original.glob(spec['prefix']+'Block*.lean'):
    p.write_text('import OneRASparse2\nimport OneRASparse3\nimport OneRASparse4\n'+p.read_text())

# The existing weighted-prefix transformer uses literal table matching.
# Reuse it with the distinct OneRA long-leaf namespace.
transform=(base.parent/'agent48-raw139-e0-1la'/'transform-graft.py').read_text()
family=spec['prefix'].removeprefix('Raw139E0')
transform=transform.replace('OneLALate',family+'Late')
argv=sys.argv[:]
sys.argv=['transform',str(original),str(imports),argv[1],argv[2],'10000']
exec(compile(transform,'OneRA weighted-prefix transform','exec'),{'__name__':'__main__'})
sys.argv=argv

# Balance independent root child modules by source closure size. This is
# scheduling, not evidence or pruning.
prefix=spec['prefix']
root=imports/(prefix+'Cover.lean')
def deps(p):return [m for l in p.read_text().splitlines() if l.startswith('import ') for m in l.split()[1:]]
allfiles={p.stem:p for p in imports.glob('*.lean')}
roots=[m for m in deps(root) if m in allfiles]
@functools.cache
def closure(m):
    if m not in allfiles:return frozenset()
    seen={m}
    for q in deps(allfiles[m]):seen|=closure(q)
    return frozenset(seen)
closures={m:closure(m) for m in roots}
assert set().union(*closures.values())==set(allfiles)-{root.stem}
groups=[[] for _ in range(min(12,len(roots)))];weights=[0]*len(groups)
size={m:sum(allfiles[q].stat().st_size for q in closures[m]) for m in roots}
for m in sorted(roots,key=lambda m:size[m],reverse=True):
    i=min(range(len(groups)),key=lambda i:weights[i]);groups[i].append(m);weights[i]+=size[m]
assert len(groups)==12 and all(groups)
(work/'shard-plan.json').write_text(json.dumps(groups)+'\n')
print('Sharded source bytes:',weights)
