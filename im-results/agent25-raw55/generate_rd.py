"""Generate the complete Raw55 E1=0RD six-hole audit; witnesses are checked in Lean."""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib, json, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent
IM = ROOT.parent
OUT = ROOT / "generated-rd"
OUT.mkdir(exist_ok=True)
sys.path[:0] = [str(IM/x) for x in (
    "agent31-three-hole-tnf", "agent10-tnf-multipump", "agent1-ngram",
    "agent32-raw59")]
from generate_four_hole import masks, move, slot

B = 7014
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]
NS = "BB6.Agent25Raw55RD"
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
    subprocess.run(["g++","-std=c++20","-O3",str(src),"-o",str(out)],check=True)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def generate():
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        compile_cpp(IM/"agent2-tnf-raw124/fast_partition.cpp",work/"enumerate")
        prefix=work/"tree"
        subprocess.run([str(work/"enumerate"),"1RB---_1RC---_0RD---_1LD0RE_---0RD_------","1000","32",str(prefix)],check=True)
        raw=prefix.with_suffix(".open").read_bytes()
        treebytes=prefix.with_suffix(".json").read_bytes()
        assert digest(raw)=="96ad8ff01f11f45ae0b050ffcced5e19bb81fc64fdbc19d6f4a692eda1e8ad6b"
        assert digest(treebytes)=="aff7b816378742c178fcba69e0480c5162fac1b877f4d5231b03bdf5ebc21084"
        rows=raw.decode().splitlines()
        assert len(rows)==len(set(rows))==918
        tree=json.loads(treebytes)
        assert tree[:3]==["split",8,8]
        index={row:i for i,row in enumerate(rows)}
        cert={}
        modules={}
        compile_cpp(IM/"agent19-raw40-cut/farbank.cpp",work/"farbank")
        bank_input="".join(f"{i} {row.replace('_','')}\n" for i,row in enumerate(rows))
        bank=subprocess.run([str(work/"farbank"),"6"],input=bank_input,
                            text=True,capture_output=True,check=True)
        print(bank.stderr,flush=True)
        witnesses=dict(line.split() for line in bank.stdout.splitlines())
        assert len(witnesses)==914
        for key,code in witnesses.items():
            i=int(key)
            p=tuple(rows[i].replace("_","")[j:j+3] for j in range(0,36,3))
            d,D,L,R,z=masks(p,int(code[0]),[int(c,36) for c in code[1:]])
            cert[i]=f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        growth={
            418:"1RB0LA_1RC0RF_0RD0LB_1LD0RE_1LA0RD_1LE---",
            419:"1RB0LF_1RC0RF_0RD---_1LD0RE_1LA0RD_1LE0RA",
            513:"1RB1LC_1RC0LF_0RD1LB_1LD0RE_1LB0RD_0LA---",
            612:"1RB---_1RC0LF_0RD1RC_1LD0RE_1LF0RD_1LA1LB",
        }
        assert set(map(int,witnesses)).isdisjoint(growth)
        for i,table in growth.items():
            assert rows[i]==table
            cert[i]=f".proven BB6.Agent25Raw55M{i}.table BB6.Agent25Raw55M{i}.never"
            modules[i]="Raw55RDGrowth"
        assert set(cert)==set(range(len(rows)))
        stats=Counter()
        sizes={}
        def inspect(t):
            tag=t[0];stats[tag]+=1
            n=1+sum(inspect(k) for k in t[3]) if tag=="split" else 1
            sizes[id(t)]=n
            return n
        inspect(tree)
        assert stats==Counter(cycle=59290,last=11415,open=918,split=3114)
        used=set()
        def render(t):
            tag,*v=t
            if tag=="cycle":
                e,k,r,b=v;return f".cycle {e} {k} {str(bool(r)).lower()} ({b})"
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
        emit("Raw55RDBase",["Raw55Progress"],f"""
abbrev rdParent : PartialMachine :=
  refine BB6.Agent25Raw55Cut.parent (4,true) (some ⟨false,true,3⟩)
theorem rdParent_root : rdParent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem rdParent_nohalt : weightedTNFNoAssignedHalt rdParent :=
  weightedTNFNoAssignedHalt_refine _ _ _ BB6.Agent25Raw55Cut.parent_nohalt
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
            mod=f"Raw55RDShard_{name}"
            if sizes[id(t)]<=SHARD:
                emit(mod,["Raw55RDBase",*sorted(deps(t))],
                     f"abbrev p_{name} := {p}\n"+local(t,f"p_{name}",name))
                return mod
            assert t[0]=="split"
            _,n,s,kids=t;names=[];imports=[]
            for i,k in enumerate(kids):
                a=f"{name}_{i:02}";names.append(a)
                imports.append(shard(k,f"(refine {p} {slot(s)} (some {move(MOVES[i])}))",a))
            emit(mod,imports,f"abbrev p_{name} := {p}\n"+combine(f"p_{name}",name,n,s,names))
            return mod
        mod=shard(tree,"rdParent","root")
        assert used==set(range(len(rows)))
        emit("Raw55RDData",[mod],f"""
noncomputable def rdCertificate : WeightedTNFCertificate {B} rdParent 6 :=
  certifiedZip {B} rdParent t_root rdParent_root rdParent_nohalt c_root
theorem all_rd : ∀ m, compatible rdParent m → WeightedBound {B} m :=
  rdCertificate.sound
#print axioms all_rd
""")
        print("raw55rd:",stats,"complete candidate audit; bound",B,flush=True)

if __name__=="__main__":
    generate()
