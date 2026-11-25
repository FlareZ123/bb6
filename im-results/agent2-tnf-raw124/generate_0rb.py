"""Replay the exact candidate search; emit checked Lean modules, never trust a cutoff."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
BRANCH="0RB"
PARENT="1RB---_1RC---_0RD---_1LD1RE_---1LF_---"+BRANCH
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99"/"enumerate.cpp"),"-o",str(ROOT/"enumerate")],check=True)
subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="ec5a42680c391cef5c2184ec403c1fa92310b8d1dec3f3bdf2384164274997ae"
opens=raw.decode().splitlines()
assert len(opens)==570 and len(set(opens))==570
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
nested=set()
extra={238:'0012345630171450871'}
proven=set(single)|set(multi)|nested
assert len(proven)==10
subprocess.run(["g++","-std=c++20","-O3",str(ROOT.parent/"agent11-tnf-raw86"/"search.cpp"),"-o",str(ROOT/"search")],check=True)
inp="".join(f"{i} {s.replace('_','')}\n" for i,s in enumerate(opens) if i not in proven and i not in extra)
out=subprocess.run([str(ROOT/"search"),"6"],input=inp,text=True,capture_output=True,check=True)
print(out.stderr)
dfa=dict((int(i),v) for i,v in (line.split() for line in out.stdout.splitlines()))
dfa.update(extra)
assert set(dfa)==set(range(570))-proven
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw1240RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent2Raw1240RB\n"
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
emit("Raw1240RBPumps",["ThreeHoleAudit","BlockPump","Agent2MultiPump"],body)
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
assert tree[:3]==["split",8,3]
emit("Raw1240RBBase",["Raw1240RBPumps"],"""
abbrev p124 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev p0RB : PartialMachine :=
  refine p124 (5,true) (some ⟨false,true,1⟩)
theorem p124_nohalt : weightedTNFNoAssignedHalt p124 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem p0RB_root : p0RB initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p0RB_nohalt : weightedTNFNoAssignedHalt p0RB :=
  weightedTNFNoAssignedHalt_refine _ _ _ p124_nohalt
abbrev child0RB (mv : Move) := refine p0RB (1,true) (some mv)
theorem query0RB : queryOK 272 p0RB 8 (1,true) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw1240RBKid{i:02}";mods.append(name)
    emit(name,["Raw1240RBBase"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 272 (child0RB {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=1750,cycle=32488,last=7216,open=570),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids0RB : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids0RB_checked (mv : Move) : check 272 (child0RB mv) (kids0RB mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree0RB : Audit := .split 8 (1,true) kids0RB
theorem tree0RB_checked : check 272 p0RB tree0RB = true := by
  change (queryOK 272 p0RB 8 (1,true) && allMoves (fun mv => check 272 (child0RB mv) (kids0RB mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query0RB, allMoves_of _ kids0RB_checked⟩
noncomputable def certificate0RB : WeightedTNFCertificate 272 p0RB 6 :=
  certified 272 p0RB tree0RB p0RB_root p0RB_nohalt tree0RB_checked
theorem all0RB : ∀ m, compatible p0RB m → WeightedBound 272 m :=
  certificate0RB.sound

#print axioms tree0RB_checked
#print axioms all0RB
"""
emit("Raw1240RBData",mods,body)
print("Candidate tree:",stats)
