"""Regenerate raw113's complete proof-carrying audit from the compact manifest.

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
NS = "BB6.Agent25Raw113"
CHUNK = 240
SHARD = 5000

def emit(name, imports, body, namespace=NS, opens=None):
    if opens is None:
        opens = ("BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath "
                 "BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit")
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
        assert tree[:3]==["split",7,5]
        (work/"bank.txt").write_text("\n".join(S["bank"])+"\n")
        hit=subprocess.check_output([str(work/"bank"),str(work/"bank.txt"),str(work/"open.txt")],text=True)
        far={int(i):v for i,v in (s.split(":") for s in hit.splitlines())}
        assert len(far)==S["farCount"]
        special=[set(map(int,S[key])) for key in ("pumps","ngram","asym","late","unresolved")]
        assert len(far)+sum(map(len,special))==len(rows)
        assert set(far).union(*special)==set(range(len(rows)))
        assert not S["unresolved"], "complete audit requires no unresolved leaves"
        index={row:i for i,row in enumerate(rows)}
        cert={}
        modules={}
        for i,code in far.items():
            d,D,L,R,z=masks(one.parse(rows[i]),int(code[0]),[int(c,36) for c in code[1:]])
            cert[i]=f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        for key,info in S["pumps"].items():
            i=int(key);kind,t,a,b,table=info
            assert rows[i].replace("_","")==table
            p=one.parse(rows[i]);mod=one if kind=="single" else multi
            ans=mod.candidate(p,one.concrete_events(p,20000))
            assert ans is not None,(i,kind)
            code,actual=mod.generate(i,p,ans)
            assert actual==(t,a,b),(i,actual,info)
            name=f"Raw113Pump{i}";ns=f"{NS}.Pump{i}"
            emit(name,["SweepPumping"],code,ns,"BB6Coverage BB6Coverage.Agent31Pump")
            cert[i]=f".proven {ns}.M{i}.table {ns}.M{i}.never";modules[i]=name
        for key,k in S["ngram"].items():
            i=int(key)
            out=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {rows[i]}\n",text=True)
            ident,data=out.strip().split(maxsplit=1)
            assert int(ident)==i and int(data.split()[0])==k
            name=f"Raw113NGram{i}";ns=f"{NS}.NGram{i}"
            emit(name,["NGramCertificate"],emit_ngram.emit(str(i),rows[i],data),ns,"BB6Coverage BB6.Agent1NGram")
            cert[i]=f".proven {ns}.p{i} {ns}.never{i}";modules[i]=name
        for key,(l,r,n) in S["asym"].items():
            i=int(key)
            out=subprocess.check_output([str(work/"asym")],input=f"{i} {rows[i]} {l} {r}\n",text=True)
            ident,data=out.strip().split(maxsplit=1)
            assert int(ident)==i and list(map(int,data.split()[:3]))==[l,r,n]
            name=f"Raw113Asym{i}"
            generate_asym.emit(OUT,name,rows[i],data)
            ns=f"BB6.Agent32AsymNGram.{name}"
            cert[i]=f".proven {ns}.table {ns}.never";modules[i]=name
        for key,(n,s) in S["late"].items():
            i=int(key);assert rows[i].count("---")==1
            cert[i]=f".last {n} {slot(s)}"
        assert set(cert)==set(range(len(rows)))
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
                e,k,r,b=v;return f".cycle {e} {k} {str(r).lower()} ({b})"
            if tag=="last":
                n,s=v;return f".last {n} {slot(s)}"
            if tag=="open":
                i=index[v[0]];assert i not in used;used.add(i)
                return cert[i]
            assert tag=="split"
            n,s,kids=v;assert len(kids)==24
            return f".split {n} {slot(s)} (byMove [\n"+",\n".join(map(render,kids))+"])"
        def deps(t):
            if t[0]=="open":
                return {modules[index[t[1]]]} if index[t[1]] in modules else set()
            if t[0]=="split":
                return set().union(*(deps(k) for k in t[3]))
            return set()
        emit("Raw113Base",["ZipPrefixAudit"],f"""
abbrev p113 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,true,2⟩)
theorem p113_root : p113 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p113_nohalt : weightedTNFNoAssignedHalt p113 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem split_checked (p : PartialMachine) (n : Nat) (s : Slot) (kids : Move → Audit)
    (hq : zipQueryOK {B} p n s = true)
    (hk : ∀ mv, zipCheck {B} (refine p s (some mv)) (kids mv) = true) :
    zipCheck {B} p (.split n s kids) = true := by
  change (zipQueryOK {B} p n s && allMoves (fun mv => zipCheck {B} (refine p s (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩
""")
        def combine(p,name,n,s,names):
            cases="\n".join(f"  · exact c_{names[12*w+6*r+q]}" for q,w,r in product(range(6),range(2),range(2)))
            return f"""
def k_{name} : Move → Audit := byMove [{','.join('t_'+x for x in names)}]
def t_{name} : Audit := .split {n} {slot(s)} k_{name}
theorem q_{name} : zipQueryOK {B} {p} {n} {slot(s)} = true := by decide
theorem kcheck_{name} (mv : Move) : zipCheck {B} (refine {p} {slot(s)} (some mv)) (k_{name} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
theorem c_{name} : zipCheck {B} {p} t_{name} = true :=
  split_checked {p} {n} {slot(s)} k_{name} q_{name} kcheck_{name}
"""
        def local(t,p,name):
            if sizes[id(t)]<=CHUNK:
                return f"""def t_{name} : Audit := {render(t)}
theorem c_{name} : zipCheck {B} {p} t_{name} = true := by
  rw [← BB6.Agent48PrefixAudit.prefixCheck_eq]
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
            mod=f"Raw113Shard_{name}"
            if sizes[id(t)]<=SHARD:
                emit(mod,["Raw113Base",*sorted(deps(t))],
                     f"abbrev p_{name} := {p}\n"+local(t,f"p_{name}",name))
                return mod
            assert t[0]=="split"
            _,n,s,kids=t;names=[];imports=[]
            for i,k in enumerate(kids):
                a=f"{name}_{i:02}";names.append(a)
                imports.append(shard(k,f"(refine {p} {slot(s)} (some {move(MOVES[i])}))",a))
            emit(mod,imports,f"abbrev p_{name} := {p}\n"+combine(f"p_{name}",name,n,s,names))
            return mod
        mod=shard(tree,"p113","root")
        assert used==set(range(len(rows)))
        emit("Raw113Data",[mod],f"""
noncomputable def certificate113 : WeightedTNFCertificate {B} p113 6 :=
  certifiedZip {B} p113 t_root p113_root p113_nohalt c_root
theorem all113 : ∀ m, compatible p113 m → WeightedBound {B} m :=
  certificate113.sound
#print axioms all113
""")
        print("raw113:",stats,"complete candidate audit; bound",B,flush=True)

if __name__=="__main__":
    generate()
