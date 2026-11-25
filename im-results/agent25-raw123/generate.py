"""Regenerate raw123's partial proof-carrying audit from the compact manifest.

The C++ searches are untrusted producers. Every split, halt, side cycle,
FAR mask, n-gram invariant and arbitrary-exponent sweep is independently
checked by the original Lean source semantics. No timeout is a verdict.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib, json, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent
IM = ROOT.parent
OUT = ROOT / "generated"
OUT.mkdir(exist_ok=True)
sys.path[:0] = [str(IM/x) for x in (
    "agent31-three-hole-tnf", "agent10-tnf-multipump", "agent1-ngram",
    "agent32-raw59")]
import generate_sweeps as one
import multi
import emit_ngram
import generate_asym
from generate_four_hole import masks, move, slot

S = json.loads((ROOT/"spec.json").read_text())
B = S["weightedTarget"]
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]
NS = "BB6.Agent25Raw123"
CHUNK = 240
SHARD = 5000

def emit(name, imports, body, namespace=NS, opens=None):
    if opens is None:
        opens = ("BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath "
                 "BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit "
                 "BB6.Agent47PartialAudit")
    (OUT/(name+".lean")).write_text(
        "".join("import "+x+"\n" for x in imports)
        + "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
        + f"namespace {namespace}\nopen {opens}\n"
        + body + f"\nend {namespace}\n")

def compile_cpp(src, out):
    subprocess.run(["g++","-std=c++17","-O3",str(src),"-o",str(out)],check=True)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def generate():
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        compile_cpp(IM/"agent2-tnf-raw99/enumerate.cpp",work/"enumerate")
        compile_cpp(IM/"agent8-tnf-six/bank.cpp",work/"bank")
        compile_cpp(IM/"agent1-ngram/ngram.cpp",work/"ngram")
        compile_cpp(IM/"agent32-raw59/ngram_asym.cpp",work/"asym")
        subprocess.run([str(work/"enumerate"),S["parent"]],cwd=work,check=True)
        raw=(work/"open.txt").read_bytes()
        treebytes=(work/"tree.json").read_bytes()
        assert digest(raw)==S["openSHA256"]
        assert digest(treebytes)==S["treeSHA256"]
        rows=raw.decode().splitlines()
        assert len(rows)==len(set(rows))==S["stats"]["open"]
        tree=json.loads(treebytes)
        assert tree[:3]==["split",7,11]
        (work/"bank.txt").write_text("\n".join(S["bank"])+"\n")
        hit=subprocess.check_output([str(work/"bank"),str(work/"bank.txt"),str(work/"open.txt")],text=True)
        far={int(i):v for i,v in (s.split(":") for s in hit.splitlines())}
        assert len(far)==S["farCount"]
        special=[set(map(int,S[key])) for key in ("single","multi","ngram","asym","late","unresolved")]
        assert len(far)+sum(map(len,special))==len(rows)
        assert set(far).union(*special)==set(range(len(rows)))
        assert all(rows[int(i)] == row for i,row in S["unresolved"].items())
        assert all(row.count("---")==1 for row in S["unresolved"].values())
        index={row:i for i,row in enumerate(rows)}
        cert={}
        modules={}
        for i,code in far.items():
            d,D,L,R,z=masks(one.parse(rows[i]),int(code[0]),[int(c,36) for c in code[1:]])
            cert[i]=f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        for kind in ("single","multi"):
            for key,info in S[kind].items():
                i=int(key);p=one.parse(rows[i]);mod=one if kind=="single" else multi
                t,a,b=info[:3]
                if kind=="single":
                    ans=one.candidate(p,one.concrete_events(p,3500)[:80])
                else:
                    def decode(c):
                        q,l,r=c
                        return multi.C(q,tuple(map(tuple,l)),tuple(map(tuple,r)))
                    st,tg=map(decode,info[3:])
                    hist=multi.pump(p,st,tg,3000)
                    assert hist is not None,(i,kind)
                    ans=(t,st,tg,hist)
                assert ans is not None,(i,kind)
                code,actual=mod.generate(i,p,ans)
                assert actual==(t,a,b),(i,actual,info)
                name=f"Raw123Pump{i}";ns=f"{NS}.Pump{i}"
                emit(name,["SweepPumping"],code,ns,"BB6Coverage BB6Coverage.Agent31Pump")
                cert[i]=f".proven {ns}.M{i}.table {ns}.M{i}.never";modules[i]=name
        for key,k in S["ngram"].items():
            i=int(key)
            out=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {rows[i]}\n",text=True)
            ident,data=out.strip().split(maxsplit=1)
            assert int(ident)==i and int(data.split()[0])==k
            name=f"Raw123NGram{i}";ns=f"{NS}.NGram{i}"
            emit(name,["NGramCertificate"],emit_ngram.emit(str(i),rows[i],data),ns,"BB6Coverage BB6.Agent1NGram")
            cert[i]=f".proven {ns}.p{i} {ns}.never{i}";modules[i]=name
        for key,(l,r,n) in S["asym"].items():
            i=int(key)
            out=subprocess.check_output([str(work/"asym")],input=f"{i} {rows[i]} {l} {r}\n",text=True)
            ident,data=out.strip().split(maxsplit=1)
            assert int(ident)==i and list(map(int,data.split()[:3]))==[l,r,n]
            name=f"Raw123Asym{i}"
            generate_asym.emit(OUT,name,rows[i],data)
            ns=f"BB6.Agent32AsymNGram.{name}"
            cert[i]=f".proven {ns}.table {ns}.never";modules[i]=name
        for key,(n,s) in S["late"].items():
            i=int(key);assert rows[i].count("---")==1
            cert[i]=f".last {n} {slot(s)}"
        assert set(cert).isdisjoint(map(int,S["unresolved"]))
        assert set(cert).union(map(int,S["unresolved"]))==set(range(len(rows)))
        stats=Counter()
        sizes={}
        def inspect(t):
            tag=t[0];stats[tag]+=1
            n=1+sum(inspect(k) for k in t[3]) if tag=="split" else 1
            sizes[id(t)]=n
            return n
        inspect(tree)
        assert stats==Counter(S["stats"])
        used=set()
        def render(t):
            tag,*v=t
            if tag=="cycle":
                e,k,r,b=v;return f".closed (.cycle {e} {k} {str(r).lower()} ({b}))"
            if tag=="last":
                n,s=v;return f".closed (.last {n} {slot(s)})"
            if tag=="open":
                i=index[v[0]];assert i not in used;used.add(i)
                return f".closed ({cert[i]})" if i in cert else ".unresolved"
            assert tag=="split"
            n,s,kids=v;assert len(kids)==24
            return f".split {n} {slot(s)} (byPartialMove [\n"+",\n".join(map(render,kids))+"])"
        def deps(t):
            if t[0]=="open":
                return {modules[index[t[1]]]} if index[t[1]] in modules else set()
            if t[0]=="split":
                return set().union(*(deps(k) for k in t[3]))
            return set()
        emit("Raw123Base",["Raw111Prefix"],f"""
abbrev p123 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,5⟩)
theorem p123_root : p123 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p123_nohalt : weightedTNFNoAssignedHalt p123 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem split_checked (p : PartialMachine) (n : Nat) (s : Slot) (kids : Move → PartialAudit)
    (hq : zipQueryOK {B} p n s = true)
    (hk : ∀ mv, partialCheck {B} (refine p s (some mv)) (kids mv) = true) :
    partialCheck {B} p (.split n s kids) = true := by
  change (zipQueryOK {B} p n s && allMoves (fun mv => partialCheck {B} (refine p s (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩
""")
        def combine(p,name,n,s,names):
            cases="\n".join(f"  · exact c_{names[12*w+6*r+q]}" for q,w,r in product(range(6),range(2),range(2)))
            return f"""
def k_{name} : Move → PartialAudit := byPartialMove [{','.join('t_'+x for x in names)}]
def t_{name} : PartialAudit := .split {n} {slot(s)} k_{name}
theorem q_{name} : zipQueryOK {B} {p} {n} {slot(s)} = true := by decide
theorem kcheck_{name} (mv : Move) : partialCheck {B} (refine {p} {slot(s)} (some mv)) (k_{name} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
theorem c_{name} : partialCheck {B} {p} t_{name} = true :=
  split_checked {p} {n} {slot(s)} k_{name} q_{name} kcheck_{name}
"""
        def local(t,p,name):
            if sizes[id(t)]<=CHUNK:
                return f"""def t_{name} : PartialAudit := {render(t)}
theorem c_{name} : partialCheck {B} {p} t_{name} = true := by
  rw [← BB6.Agent47Raw111.partialPrefix_eq]
  decide
"""
            assert t[0]=="split"
            _,n,s,kids=t;out=[];names=[]
            for i,k in enumerate(kids):
                a=f"{name}_{i:02}";names.append(a)
                out.append(f"abbrev p_{a} := refine {p} {slot(s)} (some {move(MOVES[i])})\n")
                out.append(local(k,f"p_{a}",a))
            out.append(combine(p,name,n,s,names))
            return "".join(out)
        def shard(t,p,name):
            mod=f"Raw123Shard_{name}"
            if sizes[id(t)]<=SHARD:
                emit(mod,["Raw123Base",*sorted(deps(t))],
                     f"abbrev p_{name} := {p}\n"+local(t,f"p_{name}",name))
                return mod
            assert t[0]=="split"
            _,n,s,kids=t;names=[];imports=[]
            for i,k in enumerate(kids):
                a=f"{name}_{i:02}";names.append(a)
                imports.append(shard(k,f"(refine {p} {slot(s)} (some {move(MOVES[i])}))",a))
            emit(mod,imports,f"abbrev p_{name} := {p}\n"+combine(f"p_{name}",name,n,s,names))
            return mod
        mod=shard(tree,"p123","root")
        assert used==set(range(len(rows)))
        emit("Raw123Data",[mod],f"""
def residuals123 := partialResiduals p123 t_root
theorem sound123 : ∀ m, compatible p123 m →
    WeightedBound {B} m ∨ ∃ e ∈ residuals123, compatible e.2 m :=
  partialSound {B} p123 t_root p123_root p123_nohalt c_root
theorem residual_count123 : residuals123.length = {len(S["unresolved"])} := by decide
#print axioms sound123
#print axioms residual_count123
""")
        print("raw123:",stats,"partial candidate audit; bound",B,flush=True)

if __name__=="__main__":
    generate()
