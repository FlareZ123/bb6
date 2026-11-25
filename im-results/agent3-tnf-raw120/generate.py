"""Raw120/E0=0RF complete candidate weighted TNF audit.
Cutoffs are used only to choose candidate witnesses; all emitted claims are
checked by Lean against ZipThreeHoleAudit, including the late halt.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks,slot,move,parse
import generate_sweeps as one
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
import multi
import macro
MOVES=["".join(x) for x in product("01","LR","ABCDEF")]
PARENT="1RB---_1RC---_0RD---_1LD1RE_0RF1LE_------"
B=14416
ONE=[345,346,355,387,388,411,469,544,1037,1206,1334,1337,1582,1907,1908,1909,1910,2192,2455,2555,2793,2811,2887,3290,3299,3318,3349]
NESTED=[2140,2146]
LATE=448
CHUNK=240
folder=ROOT/"rf"
folder.mkdir(exist_ok=True)
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o","enumerate"],cwd=folder,check=True)
subprocess.run([str(folder/"enumerate"),PARENT],cwd=folder,check=True)
data=(folder/"open.txt").read_bytes()
assert hashlib.sha256(data).hexdigest()=="bda880d33c84532152766ab55afccf0744461e91eb337a3badecb8719f1a68dc"
opens=data.decode().splitlines()
assert len(opens)==len(set(opens))==3793
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent8-tnf-six/bank.cpp"),"-o","bank"],cwd=folder,check=True)
hits=subprocess.check_output([str(folder/"bank"),str(ROOT/"bank.txt"),str(folder/"open.txt")],text=True)
certs={}
for row in hits.splitlines():
    i,a=row.split(":")
    certs[opens[int(i)]]=a
symbolic=set(ONE+NESTED+[523,1201,LATE])
assert len(certs)==3761 and set(certs)==set(opens)-{opens[i] for i in symbolic}
pumpns="BB6.Agent3Raw120Pumps"
pc=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {pumpns}","open BB6Coverage BB6Coverage.Agent31Pump"]
pumps={opens[i]:(f"{pumpns}.M{i}.table",f"{pumpns}.M{i}.never") for i in symbolic-{LATE}}
# Suppress harmless append-nil discrepancies in generated equations.
if "List.append_nil" not in one.SIMP:one.SIMP+=",List.append_nil"
if "List.append_nil" not in multi.SIMP:multi.SIMP+=",List.append_nil"
for i in ONE:
    p=one.parse(opens[i])
    ans=one.candidate(p,one.concrete_events(p,20000))
    assert ans is not None,i
    code,info=one.generate(i,p,ans)
    pc.append(code)
    print(i,"one",info)
i=523
p=one.parse(opens[i])
L=multi.lit;R=multi.rep
st=multi.C(4,(),multi.clean(L("111011")+R("011")+L("0000")+R("0")+L("110000")))
tg=multi.C(4,(),multi.clean(L("111011011")+R("011")+L("00000")+R("0")+L("110000")))
ans=multi.pump(p,st,tg,3000)
assert ans is not None
code,info=multi.generate(i,p,(125,st,tg,ans))
assert info==(125,40,8),info
pc.append(code)
for i in NESTED:
    pc.append(macro.generate_nested(i,one.parse(opens[i])))
assert opens[1201]=="1RB0LE_1RC0LA_0RD1RA_1LD1RE_0RF1LE_---0RB"
assert opens[LATE]=="1RB1LF_1RC1RF_0RD1RB_1LD1RE_0RF1LE_---0LA"
pc.append(f"end {pumpns}")
(folder/"Raw120RFSweeps.lean").write_text("\n\n".join(pc)+"\n")
tree=json.loads((folder/"tree.json").read_text())
assert tree[:3]==["split",10,11]
prefix="Raw120RF";ns="BB6.Agent3Raw120"
header=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
"""
def emit(name,imports,body):
    (folder/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+header+body+f"\nend {ns}\n")
base=f"""
theorem pRF_root : pRF initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pRF_nohalt : weightedTNFNoAssignedHalt pRF :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
theorem split_checked (p : PartialMachine) (n : Nat) (s : Slot) (kids : Move → Audit)
    (hq : zipQueryOK {B} p n s = true)
    (hk : ∀ mv, zipCheck {B} (refine p s (some mv)) (kids mv) = true) :
    zipCheck {B} p (.split n s kids) = true := by
  change (zipQueryOK {B} p n s && allMoves (fun mv => zipCheck {B} (refine p s (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩
"""
emit(prefix+"Base",["Raw120Late","Raw120Counter",prefix+"Sweeps"],base)
stats=Counter();used=set()
def size(t):
    stats[t[0]]+=1
    return 1+sum(map(size,t[3])) if t[0]=="split" else 1
size(tree)
assert stats==Counter(split=1563,cycle=26299,last=5858,open=3793),stats
def count(t):return 1+sum(map(count,t[3])) if t[0]=="split" else 1
def render(t):
    tag,*v=t
    if tag=="cycle":
        e,k,r,b=v
        return f".cycle {e} {k} {str(r).lower()} ({b})"
    if tag=="last":
        n,s=v
        return f".last {n} {slot(s)}"
    if tag=="open":
        code=v[0]
        assert code not in used
        used.add(code)
        if code in pumps:return ".proven "+" ".join(pumps[code])
        if code==opens[LATE]:return ".last 14415 (5,false)"
        a=certs[code]
        d,D,L,R,z=masks(parse(code),int(a[0]),[int(x,36) for x in a[1:]])
        return f'.far {str(a[0]=="1").lower()} {d} ⟨0,{D},{L},{R},{z}⟩'
    assert tag=="split"
    n,s,kids=v
    assert len(kids)==24
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(map(render,kids))+"])"
def compose(pname,name,t):
    if count(t)<=CHUNK:
        return f"def t_{name} : Audit := {render(t)}\ntheorem c_{name} : zipCheck {B} {pname} t_{name} = true := by decide\n"
    assert t[0]=="split"
    _,n,s,kids=t
    out=[];names=[]
    for i,kid in enumerate(kids):
        a=f"{name}_{i:02}"
        names.append(a)
        out.append(f"abbrev p_{a} := refine {pname} {slot(s)} (some {move(MOVES[i])})\n")
        out.append(compose(f"p_{a}",a,kid))
    out.append(combine(pname,name,n,s,names))
    return "".join(out)
def combine(pname,name,n,s,names):
    cases="\n".join(f"  · exact c_{names[12*w+6*r+q]}" for q,w,r in product(range(6),range(2),range(2)))
    return f"""
def k_{name} : Move → Audit := byMove [{','.join('t_'+x for x in names)}]
def t_{name} : Audit := .split {n} {slot(s)} k_{name}
theorem q_{name} : zipQueryOK {B} {pname} {n} {slot(s)} = true := by decide
theorem kcheck_{name} (mv : Move) : zipCheck {B} (refine {pname} {slot(s)} (some mv)) (k_{name} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
theorem c_{name} : zipCheck {B} {pname} t_{name} = true :=
  split_checked {pname} {n} {slot(s)} k_{name} q_{name} kcheck_{name}
"""
mods=[];names=[]
for i,kid in enumerate(tree[3]):
    a=f"kid{i:02}"
    names.append(a)
    name=f"{prefix}Kid{i:02}"
    mods.append(name)
    emit(name,[prefix+"Base"],f"abbrev p_{a} := refine pRF (5,true) (some {move(MOVES[i])})\n"+compose(f"p_{a}",a,kid))
body=combine("pRF","root",10,11,names)+f"""
noncomputable def certificateRF : WeightedTNFCertificate {B} pRF 6 :=
  certifiedZip {B} pRF t_root pRF_root pRF_nohalt c_root
theorem allRF : ∀ m, compatible pRF m → WeightedBound {B} m := certificateRF.sound
theorem exactRF (T : Nat) :
    (∀ m, compatible pRF m → WeightedBound T m) ↔ {B} ≤ T := by
  constructor
  · intro h
    exact late_bound_lower T (h lateMachine late_compatible_RF)
  · intro ht m hm k d hk hd
    exact Nat.le_trans (allRF m hm k d hk hd) ht
#print axioms c_root
#print axioms allRF
#print axioms exactRF
"""
assert used==set(opens)
emit(prefix+"Data",mods,body)
print(stats,"all candidate FAR and symbolic witnesses emitted; exact weighted bound",B)
