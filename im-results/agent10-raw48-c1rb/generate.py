"""Generate Raw48 C1=0RB canonical audit; every verdict needs Lean.
Usage: python generate.py OUTPUT_DIR
Uses the existing enumerate.cpp, FAR masks and sweep generator."""
from pathlib import Path
from itertools import product
from collections import Counter
import json,sys,hashlib,subprocess
ROOT=Path(__file__).resolve().parent
O=Path(sys.argv[1]).resolve();O.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks,slot,move
import generate_sweeps as one
spec=json.loads((ROOT/"spec.json").read_text())
B=spec["bound"];CUT=spec["cut"];N=1000
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(O/"enumerate")],check=True)
subprocess.run([str(O/"enumerate"),spec["parent"]],cwd=O,check=True)
assert hashlib.sha256((O/"open.txt").read_bytes()).hexdigest()==spec["raw_open_sha256"]
TREE=json.loads((O/"tree.json").read_text());opens=[]
def collect(t,cut):
    if t[0]=="open":opens.append(t[1])
    if t[0]=="split":
        for j,x in enumerate(t[3]):
            if j%6<=cut:collect(x,cut+(j%6==cut))
collect(TREE,CUT)
assert len(opens)==len(spec["index"])==len(set(opens))
assert hashlib.sha256(("\n".join(opens)+"\n").encode()).hexdigest()==spec["canonical_open_sha256"]
FAR={s:spec["bank"][ord(c)-97] for s,c in zip(opens,spec["index"])}
HARD={s:i for i,s in enumerate(spec["pump_tables"])}
ns="BB6.Agent10Raw48B0RBPumps"
pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {ns}","open BB6Coverage BB6Coverage.Agent31Pump"]
for s,i in HARD.items():
    p=one.parse(s);ans=one.candidate(p,one.concrete_events(p,6000))
    assert ans is not None,s
    code,info=one.generate(i,p,ans);pumpcode.append(code);print(i,info)
pumpcode.append(f"end {ns}")
(O/"Raw48C1RBpumps.lean").write_text("\n\n".join(pumpcode)+"\n")
(O/"ZipCanonicalAudit.lean").write_bytes((ROOT/"ZipCanonicalAudit.lean").read_bytes())
NS="BB6.Agent10Raw48C1RB";mods={};count=0;stats=Counter()
def leaf(t):
    tag,*v=t;stats[tag]+=1
    if tag=="cycle":
        e,k,r,b=v;return f".cycle {e} {k} {str(r).lower()} ({b})"
    if tag=="last":
        n,s=v;return f".last {n} {slot(s)}"
    if tag=="open":
        s=v[0];a=FAR[s]
        if a=="-":
            k=HARD[s];ns=f"BB6.Agent10Raw48B0RBPumps.M{k}"
            return f".proven {ns}.table {ns}.never"
        rev=int(a[0]);d,D,L,R,z=masks(one.parse(s),rev,[int(ch,36) for ch in a[1:]])
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    raise ValueError(t)
def size(t,cut):
    return 1+sum(size(x,cut+(j%6==cut)) for j,x in enumerate(t[3]) if j%6<=cut) if t[0]=="split" else 1
def build(t,cut):
    if t[0]!="split":return leaf(t)
    stats["split"]+=1;n,s,k=t[1:]
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(x,cut+(j%6==cut)) if j%6<=cut else ".last 0 (0,false)" for j,x in enumerate(k))+"])"
def expr(path):
    a="parent"
    for s,j in path:a=f"(refine {a} {slot(s)} (some {move(MOVES[j])}))"
    return a
HEAD=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent10CanonicalAudit
"""
def emit(name,imports,body):
    mods[name]=imports;(O/(name+".lean")).write_text("".join("import "+x+"\n" for x in imports)+HEAD+body+f"\nend {NS}\n")
base="Raw48C1RBBase"
emit(base,["ZipCanonicalAudit","Raw48C1RBpumps"],"""def route : List PathEntry := (path.take 3) ++ [(5,(3,true),⟨true,false,2⟩),(6,(2,true),⟨false,true,1⟩)]
abbrev parent : PartialMachine := (pathEnd root 2 route).1
theorem parent_path : FirstHolePath parent 4 := by
  have h := pathOK_sound root 2 route FirstHolePath.root (by decide)
  exact h
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  pathEnd_nohalt root 2 route firstOneCylinder_no_assigned_halt
theorem parent_support : TNFSupport parent 4 := by
  have h0 := firstOneCylinder_tnf_support
  have h1 := refine_support root (1,false) ⟨true,true,2⟩ 2 3 h0 (by decide) (by decide) (by decide)
  have h2 := refine_support _ (2,false) ⟨false,true,3⟩ 3 4 h1 (by decide) (by decide) (by decide)
  have h3 := refine_support _ (3,false) ⟨true,false,3⟩ 4 4 h2 (by decide) (by decide) (by decide)
  have h4 := refine_support _ (3,true) ⟨true,false,2⟩ 4 4 h3 (by decide) (by decide) (by decide)
  exact refine_support _ (2,true) ⟨false,true,1⟩ 4 4 h4 (by decide) (by decide) (by decide)
""")
def generate(t,cut,path):
    global count
    i=count;count+=1;name=f"Raw48C1RBNode{i:04}";tn=f"tree{i:04}";hn=f"checked{i:04}";pn=f"p{i:04}"
    n=size(t,cut);p=expr(path)
    if n<=N:
        body=f"abbrev {pn} : PartialMachine := {p}\n\ndef {tn} : Audit := {build(t,cut)}\n\ntheorem {hn} : canonicalCheck {B} {pn} {cut} {tn} = true := by decide\n"
        emit(name,[base],body);return name,tn,hn
    assert t[0]=="split";stats["split"]+=1;step,s,kids=t[1:];rs=[]
    for j,x in enumerate(kids):
        rs.append(generate(x,cut+(j%6==cut),path+[(s,j)]) if j%6<=cut else None)
    ts=[r[1] if r else "(.last 0 (0,false))" for r in rs]
    body=f"""abbrev {pn} : PartialMachine := {p}

def {tn} : Audit := .split {step} {slot(s)} (byMove [{",".join(ts)}])

theorem {hn} : canonicalCheck {B} {pn} {cut} {tn} = true := by
  apply canonicalSplitChecked
  · decide
  · intro mv hmv
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
"""
    for q,w,r in product(range(6),range(2),range(2)):
        x=rs[12*w+6*r+q]
        body+=f"    · exact {x[2]}\n" if x else "    · omega\n"
    emit(name,[x[0] for x in rs if x],body);return name,tn,hn
root,tn,hn=generate(TREE,CUT,[])
assert stats==Counter(spec["stats"]),(stats,spec["stats"])
out="Raw48C1RBData"
emit(out,[root],f"""noncomputable def certificate : WeightedTNFCertificate {B} parent 4 :=
  certifiedCanonical {B} parent 4 {tn} parent_root parent_nohalt parent_support (by decide) {hn}
theorem all_completions : ∀ m, compatible parent m → WeightedBound {B} m := certificate.sound
theorem cover : Cover (WeightedBound {B}) parent := certificate.toCover
#print axioms all_completions
#print axioms cover
""")
# Group dependency-ordered subtrees; each checked proposition is small.
nodes=[x for x in mods if x not in (base,out)];groups=[];chunk=[];bytes_so_far=0
for x in nodes:
    n=(O/(x+".lean")).stat().st_size
    if bytes_so_far+n>90000 or len(chunk)>=55:
        groups.append(chunk);chunk=[];bytes_so_far=0
    chunk.append(x);bytes_so_far+=n
if chunk:groups.append(chunk)
mapto={x:f"Raw48C1RBGroup{i:03}" for i,g in enumerate(groups) for x in g};names={}
for i,g in enumerate(groups):
    name=f"Raw48C1RBGroup{i:03}"
    deps=sorted({base}|{mapto[y] for x in g for y in mods[x] if y!=base and mapto[y]!=name})
    names[name]=deps
    marker="open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent10CanonicalAudit\n"
    s="".join("import "+d+"\n" for d in deps)+HEAD
    for x in g:
        t=(O/(x+".lean")).read_text().split(marker,1)[1].rsplit("\nend "+NS,1)[0]
        s+=t+"\n"
    (O/(name+".lean")).write_text(s+"\nend "+NS+"\n")
    for x in g:(O/(x+".lean")).unlink()
(O/(out+".lean")).write_text((O/(out+".lean")).read_text().replace("import "+root,"import "+mapto[root]))
names[out]=[mapto[root]]
(O/"raw48-groups.json").write_text(json.dumps(names,indent=2))
print(stats,count,len(groups))
