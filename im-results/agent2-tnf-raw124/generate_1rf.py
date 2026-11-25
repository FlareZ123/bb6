"""Replay the exact candidate search; emit checked Lean modules, never trust a cutoff."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
BRANCH=sys.argv[1] if len(sys.argv)>1 else "1RF"
assert BRANCH in {"1RF"}, "0RB still has one unresolved leaf"
PARENT="1RB---_1RC---_0RD---_1LD1RE_---1LF_---"+BRANCH
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99"/"enumerate.cpp"),"-o",str(ROOT/"enumerate")],check=True)
subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="18d9ccf8e1a37ba08482d1c94137875eb2e0bb082869f82ebd42c021b6e6d5f0"
opens=raw.decode().splitlines()
assert len(opens)==1171 and len(set(opens))==1171
index={s:i for i,s in enumerate(opens)}
def load_witnesses(name):
    lines=[l for l in (ROOT/name).read_text().splitlines() if l and not l.startswith("#")]
    assert len(lines)%2==0
    result={}
    for meta,ops in zip(lines[::2],lines[1::2]):
        branch,i,*args=meta.split()
        if branch==BRANCH:result[int(i)]=(args,ops)
    return result
single=load_witnesses("single-witnesses.txt")
multi=load_witnesses("multi-witnesses.txt")
nested={341,923}
proven=set(single)|set(multi)|nested
assert len(proven)==11
subprocess.run(["g++","-std=c++20","-O3",str(ROOT.parent/"agent11-tnf-raw86"/"search.cpp"),"-o",str(ROOT/"search")],check=True)
inp="".join(f"{i} {s.replace('_','')}\n" for i,s in enumerate(opens) if i not in proven)
out=subprocess.run([str(ROOT/"search"),"6"],input=inp,text=True,capture_output=True,check=True)
print(out.stderr)
dfa=dict((int(i),v) for i,v in (line.split() for line in out.stdout.splitlines()))
assert set(dfa)==set(range(1171))-proven
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw1241RF
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent2Raw1241RF\n"
def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+HEADER+body+FOOTER)
body="""open BB6Coverage.Agent50Pump BB6.Agent2MultiPump
def fromRows (xs : List (Option (Option Move))) : PartialMachine :=
  fun s => (xs[2*s.1.val+s.2.toNat]?).getD none
"""
def shape(s):
    q,w=s.split(":")
    a,b,c,d,e,f=w.split(",")
    return f'⟨{q},(word "{a}" "{b}" "{c}"),(word "{d}" "{e}" "{f}")⟩'
def mword(s):
    a,b=s.split(";")
    ps=[]
    for x in b.split(",") if b else []:
        c,d=x.split(":")
        ps.append(f'⟨bits "{c}",bits "{d}",0⟩')
    return f'⟨bits "{a}",[{",".join(ps)}]⟩'
def compile_ops(spec,is_multi):
    ops=[]
    for x in spec.split():
        if x.isdigit():ops.extend([".step"]*int(x))
        elif x.startswith("W"):
            if is_multi:
                ops.append((".rewriteL " if x[1]=="0" else ".rewriteR ")+mword(x[3:]))
            else:
                ops.append(".rewrite "+shape(x[1:]))
        else:
            k,c,v=x[1:].split(",")
            ops.append(f'.{"left" if x[0]=="L" else "right"} {k} {c} (bits "{v}")')
    return "["+",".join(ops)+"]"
def table(i):
    return "["+",".join("none" if a=="---" else "some (some "+move(a)+")" for a in parse(opens[i]))+"]"
for i,(args,spec) in sorted(single.items()):
    entry,sh=args
    body+=f"""
def pumpTable{i} : PartialMachine := fromRows {table(i)}
def pumpCert{i} : Certificate := ⟨{entry},{shape(sh)},{compile_ops(spec,False)}⟩
theorem pumpCheck{i} : pumpCert{i}.check pumpTable{i} = true := by decide
theorem pumpNever{i} : ∀ m, compatible pumpTable{i} m → NeverHalts m :=
  Certificate.never pumpTable{i} pumpCert{i} pumpCheck{i}
#print axioms pumpNever{i}
"""
for i,(args,spec) in sorted(multi.items()):
    entry,q,l,r=args
    body+=f"""
def pumpTable{i} : PartialMachine := fromRows {table(i)}
def pumpCert{i} : MCertificate := ⟨{entry},⟨{q},{mword(l)},{mword(r)}⟩,{compile_ops(spec,True)}⟩
theorem pumpCheck{i} : pumpCert{i}.check pumpTable{i} = true := by decide
theorem pumpNever{i} : ∀ m, compatible pumpTable{i} m → NeverHalts m :=
  MCertificate.never pumpTable{i} pumpCert{i} pumpCheck{i}
#print axioms pumpNever{i}
"""
for i in sorted(nested):
    body+=f"""
abbrev pumpTable{i} := BB6.Agent2Nested.p{i}
theorem pumpNever{i} : ∀ m, compatible pumpTable{i} m → NeverHalts m := BB6.Agent2Nested.never{i}
#print axioms pumpNever{i}
"""
emit("Raw1241RFPumps",["ThreeHoleAudit","BlockPump","Agent2MultiPump","Agent2Nested"],body)
tree=json.loads((ROOT/"tree.json").read_text())
stats=Counter()
def build(node):
    tag,*v=node;stats[tag]+=1
    if tag=="cycle":
        e,k,r,b=v
        return f".cycle {e} {k} {str(r).lower()} ({b})"
    if tag=="last":
        n,s=v;return f".last {n} {slot(s)}"
    if tag=="open":
        code=v[0];i=index[code]
        if i in proven:return f".proven pumpTable{i} pumpNever{i}"
        a=dfa[i]
        rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,list(map(int,a[1:])))
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    assert tag=="split"
    n,s,kids=v;assert len(kids)==24
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
assert tree[:3]==["split",10,10]
emit("Raw1241RFBase",["Raw1241RFPumps"],"""
abbrev p124 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev p1RF : PartialMachine :=
  refine p124 (5,true) (some ⟨true,true,5⟩)
theorem p124_nohalt : weightedTNFNoAssignedHalt p124 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem p1RF_root : p1RF initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p1RF_nohalt : weightedTNFNoAssignedHalt p1RF :=
  weightedTNFNoAssignedHalt_refine _ _ _ p124_nohalt
abbrev child1RF (mv : Move) := refine p1RF (5,false) (some mv)
theorem query1RF : queryOK 140 p1RF 10 (5,false) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw1241RFKid{i:02}";mods.append(name)
    emit(name,["Raw1241RFBase"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 140 (child1RF {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=724,cycle=12897,last=2608,open=1171),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids1RF : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids1RF_checked (mv : Move) : check 140 (child1RF mv) (kids1RF mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree1RF : Audit := .split 10 (5,false) kids1RF
theorem tree1RF_checked : check 140 p1RF tree1RF = true := by
  change (queryOK 140 p1RF 10 (5,false) && allMoves (fun mv => check 140 (child1RF mv) (kids1RF mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query1RF, allMoves_of _ kids1RF_checked⟩
noncomputable def certificate1RF : WeightedTNFCertificate 140 p1RF 6 :=
  certified 140 p1RF tree1RF p1RF_root p1RF_nohalt tree1RF_checked
theorem all1RF : ∀ m, compatible p1RF m → WeightedBound 140 m :=
  certificate1RF.sound

#print axioms tree1RF_checked
#print axioms all1RF
"""
emit("Raw1241RFData",mods,body)
print("Candidate tree:",stats)
