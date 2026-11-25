"""Replay archived exact witness bundles and generate original-source Lean audits."""
import base64,zlib,json,sys,hashlib,subprocess
from pathlib import Path
from itertools import product
from functools import lru_cache
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks,slot,move,parse
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
def shape(s):
    q,w=s.split(":")
    a,b,c,d,e,f=w.split(",")
    return f'⟨{q},(word "{a}" "{b}" "{c}"),(word "{d}" "{e}" "{f}")⟩'
def mword(s):
    a,b=s.split(";")
    ps=[]
    for x in b.split(",") if b else []:
        i,c,d=x.split(":")
        ps.append(f'⟨bits "{c}",bits "{d}",{i}⟩')
    return f'⟨bits "{a}",[{",".join(ps)}]⟩'
def compile_ops(spec,is_multi):
    ops=[]
    for x in spec.split():
        if x.isdigit():ops.extend([".step"]*int(x))
        elif x.startswith("W"):
            if is_multi:ops.append((".rewriteL " if x[1]=="0" else ".rewriteR ")+mword(x[3:]))
            else:ops.append(".rewrite "+shape(x[1:]))
        else:
            k,c,v=x[1:].split(",")
            ops.append(f'.{"left" if x[0]=="L" else "right"} {k} {c} (bits "{v}")')
    return "["+",".join(ops)+"]"
def generate(bundle):
    b=bundle["branch"];B=bundle["bound"];stem="Raw124B"+b
    prefix="BB6.Agent2"+stem
    header=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {prefix}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
    def emit(name,imports,body):
        (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+header+body+"\nend "+prefix+"\n")
    parent="1RB---_1RC---_0RD---_1LD1RE_---1LF_---"+b
    subprocess.run([str(ROOT/"enumerate"),parent],cwd=ROOT,check=True)
    raw=(ROOT/"open.txt").read_bytes();rawtree=(ROOT/"tree.json").read_bytes()
    assert hashlib.sha256(raw).hexdigest()==bundle["hash"]
    assert hashlib.sha256(rawtree).hexdigest()==bundle["tree_hash"]
    opens=raw.decode().splitlines();index={s:i for i,s in enumerate(opens)}
    assert len(index)==len(opens)==len(bundle["far"])
    tree=json.loads(rawtree)
    single={int(i):v for i,v in bundle["single"].items()}
    multi={int(i):v for i,v in bundle["multi"].items()}
    long={int(i):v for i,v in bundle["long"].items()}
    nested={int(i):v for i,v in bundle.get("nested",{}).items()}
    extra_tree=bundle.get("extra_tree",{})
    extra_indices={index[code] for code in extra_tree}
    pool=bundle["pool"];far={i:pool[k] for i,k in enumerate(bundle["far"]) if k>=0}
    assert sum(map(len,(single,multi,long,far,nested)))+len(extra_tree)==len(opens)
    assert set(single)|set(multi)|set(long)|set(far)|set(nested)|extra_indices==set(range(len(opens)))
    def table(i):
        return "["+",".join("none" if a=="---" else "some (some "+move(a)+")" for a in parse(opens[i]))+"]"
    body="""open BB6Coverage.Agent50Pump BB6.Agent2MultiPump
def fromRows (xs : List (Option (Option Move))) : PartialMachine :=
  fun s => (xs[2*s.1.val+s.2.toNat]?).getD none
"""
    for is_multi,wits in [(False,single),(True,multi)]:
        for i,(entry,sh,spec) in sorted(wits.items()):
            if is_multi:
                q,l,r=sh.split()
                sh=f'⟨{q},{mword(l)},{mword(r)}⟩'
            else:sh=shape(sh)
            typ="MCertificate" if is_multi else "Certificate"
            body+=f"""
def pumpTable{i} : PartialMachine := fromRows {table(i)}
def pumpCert{i} : {typ} := ⟨{entry},{sh},{compile_ops(spec,is_multi)}⟩
theorem pumpCheck{i} : pumpCert{i}.check pumpTable{i} = true := by decide
theorem pumpNever{i} : ∀ m, compatible pumpTable{i} m → NeverHalts m :=
  {typ}.never pumpTable{i} pumpCert{i} pumpCheck{i}
#print axioms pumpNever{i}
"""
    imports=["ThreeHoleAudit","BlockPump","Agent2MultiPump"]
    for i,(module,table_name,proof_name) in sorted(nested.items()):
        imports.append(module)
        body+=f"\nabbrev pumpTable{i} : PartialMachine := {table_name}\ntheorem pumpNever{i} : ∀ m, compatible pumpTable{i} m → NeverHalts m := {proof_name}\n"
    emit(stem+"Pumps",list(dict.fromkeys(imports)),body)
    emit(stem+"Base",[stem+"Pumps"],f"""
abbrev p124 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev pBranch : PartialMachine := refine p124 (5,true) (some {move(b)})
theorem p124_nohalt : weightedTNFNoAssignedHalt p124 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem pBranch_root : pBranch initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pBranch_nohalt : weightedTNFNoAssignedHalt pBranch :=
  weightedTNFNoAssignedHalt_refine _ _ _ p124_nohalt
""")
    def build(node):
        tag,*v=node
        if tag=="open":
            code=v[0]
            if code in extra_tree:return build(extra_tree[code])
            i=index[code]
            if i in single or i in multi or i in nested:return f".proven pumpTable{i} pumpNever{i}"
            if i in long:
                a,*v=long[i]
                if a=="hole":
                    assert code.count("---")==1
                    tag="last"
                else:
                    assert a=="cycle"
                    tag="cycle"
            else:
                rev,dfa=far[i];d,D,L,R,z=masks(parse(code),rev,dfa)
                return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        if tag=="cycle":
            e,k,r,h=v
            return f".cycle {e} {k} {str(bool(r)).lower()} ({h})"
        if tag=="last":
            n,s=v;return f".last {n} {slot(s)}"
        assert tag=="split"
        n,s,kids=v;assert len(kids)==24
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
    def size(node):
        if node[0]=="open" and node[1] in extra_tree:return size(extra_tree[node[1]])
        return 1+sum(map(size,node[3])) if node[0]=="split" else 1
    counter=0
    def assemble(n,s,pname,tag,childtags):
        kids="kids"+tag;theorem="check"+tag
        cases="\n".join(f"  · exact check{childtags[12*w+6*r+q]}" for q,w,r in product(range(6),range(2),range(2)))
        return f"""
def {kids} : Move → Audit := byMove [{",".join("tree"+t for t in childtags)}]
theorem {kids}_checked (mv : Move) : check {B} (refine {pname} {slot(s)} (some mv)) ({kids} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree{tag} : Audit := .split {n} {slot(s)} {kids}
theorem {theorem} : check {B} {pname} tree{tag} = true := by
  change (queryOK {B} {pname} {n} {slot(s)} && allMoves (fun mv => check {B} (refine {pname} {slot(s)} (some mv)) ({kids} mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ {kids}_checked⟩
"""
    def recursive(node,pname,tag):
        nonlocal counter
        if node[0]=="open" and node[1] in extra_tree:node=extra_tree[node[1]]
        if node[0]!="split" or size(node)<=500:
            return f"def tree{tag} : Audit := {build(node)}\ntheorem check{tag} : check {B} {pname} tree{tag} = true := by decide\n"
        _,n,s,ks=node
        out="";ts=[]
        for k,m in zip(ks,MOVES):
            counter+=1;t=str(counter);ts.append(t);pn="pNode124" if t=="124" else "p"+t
            out+=f"abbrev {pn} : PartialMachine := refine {pname} {slot(s)} (some {move(m)})\n"
            out+=recursive(k,pn,t)
        return out+assemble(n,s,pname,tag,ts)
    mods=[stem+"Base"];body=""
    if tree[0]=="split":
        _,n,s,kids=tree;tags=[]
        for i,(k,m) in enumerate(zip(kids,MOVES)):
            t=f"K{i:02}";tags.append(t);pn="p"+t;mod=stem+"Kid"+t
            code=f"abbrev {pn} : PartialMachine := refine pBranch {slot(s)} (some {move(m)})\n"+recursive(k,pn,t)
            emit(mod,[stem+"Base"],code);mods.append(mod)
        body=assemble(n,s,"pBranch","Root",tags)
    else:body=recursive(tree,"pBranch","Root")
    body+=f"""
noncomputable def certificate : WeightedTNFCertificate {B} pBranch 6 :=
  certified {B} pBranch treeRoot pBranch_root pBranch_nohalt checkRoot
theorem bound_all : ∀ m, compatible pBranch m → WeightedBound {B} m := certificate.sound
#print axioms checkRoot
#print axioms bound_all
"""
    emit(stem+"Data",mods,body)
    print(b,B,len(opens),len(single),len(multi),len(long),len(far),len(extra_tree),flush=True)
def longcycle_bundle(branch):
    """Build a recursive exact 0LB leaf partition from half-tape witnesses."""
    assert branch == "0LB"
    parent = "1RB---_1RC---_0RD---_1LD1RE_---1LF_---0LB"
    subprocess.run([str(ROOT/"enumerate"), parent], cwd=ROOT, check=True)
    raw = (ROOT/"open.txt").read_bytes()
    rawtree = (ROOT/"tree.json").read_bytes()
    opens = raw.decode().splitlines()
    assert opens
    subprocess.run(
        ["g++", "-std=c++20", "-O3", str(ROOT/"longcycle.cpp"), "-o", str(ROOT/"longcycle")],
        check=True,
    )

    terminal = {}
    splits = {}
    pending = list(opens)
    cap, lookback = 100000, 128
    max_query = 0
    rounds = 0

    def display(compact):
        assert len(compact) == 36
        return "_".join(compact[6*i:6*(i+1)] for i in range(6))

    deferred = set()
    while pending or deferred:
        if not pending:
            if cap < 1000000:
                cap = min(cap * 10, 1000000)
            elif lookback < 1024:
                lookback = min(lookback * 4, 1024)
            else:
                sample = sorted(deferred)[:3]
                raise AssertionError(("unresolved 0LB leaves", len(deferred), sample, cap, lookback))
            pending = sorted(t for t in deferred if t not in terminal and t not in splits)
            deferred.clear()
            print(
                f"0LB retry escalation: pending={len(pending)} cap={cap} lookback={lookback}",
                flush=True,
            )
            continue

        rounds += 1
        from concurrent.futures import ThreadPoolExecutor
        workers = min(2, len(pending))
        chunks = [pending[i::workers] for i in range(workers)]

        def run_chunk(chunk):
            indexed = "".join(f"{i} {table.replace('_', '')}\n" for i, table in enumerate(chunk))
            result = subprocess.run(
                [str(ROOT/"longcycle"), str(cap), str(lookback)],
                cwd=ROOT, input=indexed, text=True, stdout=subprocess.PIPE, check=True,
            )
            rows = [line.split() for line in result.stdout.splitlines()]
            assert len(rows) == len(chunk), (len(chunk), len(rows), rounds)
            ids = [int(row[0]) for row in rows]
            assert len(set(ids)) == len(ids) and set(ids) == set(range(len(chunk)))
            by_id = {int(row[0]): row for row in rows}
            return [(table, by_id[i]) for i, table in enumerate(chunk)]

        with ThreadPoolExecutor(max_workers=workers) as pool:
            classified = [item for part in pool.map(run_chunk, chunks) for item in part]
        next_pending = []
        for table, row in classified:
            if row[1] == "cycle":
                assert len(row) == 6, row
                terminal[table] = ["cycle", int(row[2]), int(row[3]), int(row[4]), int(row[5])]
            elif row[1] == "hole":
                assert len(row) == 4, row
                n, slot_id = int(row[2]), int(row[3])
                max_query = max(max_query, n)
                if table.count("---") == 1:
                    terminal[table] = ["last", n, slot_id]
                else:
                    compact = table.replace("_", "")
                    assert len(compact) == 36 and compact[3*slot_id:3*slot_id+3] == "---"
                    children = [display(compact[:3*slot_id] + mv + compact[3*slot_id+3:]) for mv in MOVES]
                    splits[table] = ["split", n, slot_id, children]
                    next_pending.extend(children)
            elif row[1] == "open":
                deferred.add(table)
            else:
                raise AssertionError(("unknown longcycle result", row))

        pending = list(dict.fromkeys(
            t for t in next_pending
            if t not in terminal and t not in splits and t not in deferred
        ))
        print(
            f"0LB recursive pass {rounds}: terminal={len(terminal)} split={len(splits)} "
            f"pending={len(pending)} deferred={len(deferred)} cap={cap} lookback={lookback}",
            flush=True,
        )
    from functools import lru_cache
    @lru_cache(None)
    def build_tree(table):
        if table in terminal:
            return terminal[table]
        n, slot_id, children = splits[table][1:]
        return ["split", n, slot_id, [build_tree(child) for child in children]]

    extra_tree = {table: build_tree(table) for table in opens}
    cycles = sum(v[0] == "cycle" for v in terminal.values())
    last = sum(v[0] == "last" for v in terminal.values())
    assert max_query <= 1_000_000
    bound = max(1_000_000, max_query + 1_000_000)
    assert bound <= 2_000_000
    print(
        f"0LB recursive partition: initial={len(opens)} cycles={cycles} "
        f"last={last} splits={len(splits)} unique={len(terminal)+len(splits)} "
        f"max_query={max_query} bound={bound}",
        flush=True,
    )
    return {
        "branch": branch,
        "bound": bound,
        "hash": hashlib.sha256(raw).hexdigest(),
        "tree_hash": hashlib.sha256(rawtree).hexdigest(),
        "far": [-1] * len(opens),
        "pool": [],
        "single": {},
        "multi": {},
        "long": {},
        "extra_tree": extra_tree,
    }


def main():
    files=sorted(ROOT.glob("complete-bundle*.json.zlib.b64"))
    data={}
    for p in files:
        for v in json.loads(zlib.decompress(base64.b64decode(p.read_text()))):data[v["branch"]]=v
    # The previously partial 1LA bundle is now closed by three parametric
    # nonhalting proofs, whose sparse tables are checked by the Audit kernel.
    path=ROOT/"partial-bundle-1LA.json.zlib.b64"
    for v in json.loads(zlib.decompress(base64.b64decode(path.read_text()))):
        assert v["branch"]=="1LA"
        n=v.setdefault("nested",{})
        assert all(str(i) not in n and v["far"][i]<0 for i in (235,1254,2919))
        n["235"]=["Agent2UnaryStack","BB6.Agent2UnaryStack.p","BB6.Agent2UnaryStack.never"]
        n["1254"]=["Agent2BinaryPair","BB6.Agent2BinaryPair.p false","BB6.Agent2BinaryPair.never false"]
        n["2919"]=["Agent2BinaryPair","BB6.Agent2BinaryPair.p true","BB6.Agent2BinaryPair.never true"]
        data[v["branch"]]=v
    requested=sys.argv[1:] or sorted(data)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99"/"enumerate.cpp"),"-o",str(ROOT/"enumerate")],check=True)
    for b in requested:
        bundle = longcycle_bundle(b) if b == "0LB" else data[b]
        generate(bundle)
if __name__=="__main__":main()
