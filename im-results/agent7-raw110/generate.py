"""Regenerate candidate-only raw110 subtree proof data from the shared classifier.

No candidate decision is trusted. All closed subtrees must pass zipCheck, and
all unresolved siblings are retained by partialSound. X/Y denote one/two-block
induction proofs, not an unchecked simulator result.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib, json, subprocess, tempfile, sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
import generate_sweeps as one
from generate_four_hole import masks, move, slot
import multi
from chunk_checks import partition
spec=json.loads((ROOT/"spec.json").read_text())
PARENT=one.parse("1RB---_1RC---_0RD---_1LD1RE_---0LC_------")
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
B=7014
NS="BB6.Agent7Raw110"
HEADER=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""
def emit(name,imports,body,chunk=False):
    text="".join(f"import {i}\n" for i in imports)+HEADER+body+f"\nend {NS}\n"
    if chunk:
        text,n=partition(text,180)
        print(name,"chunked",n,flush=True)
    (ROOT/(name+".lean")).write_text(text)
emit("Raw110Base",["PartialAudit"],"""
abbrev p110 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,false,2⟩)
theorem p110_root : p110 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p110_nohalt : weightedTNFNoAssignedHalt p110 :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
abbrev child110 (mv : Move) := refine p110 (2,true) (some mv)
theorem query110 : zipQueryOK 7014 p110 7 (2,true) = true := by decide
""")
if '--base-only' in sys.argv:
    sys.exit(0)
cycles={2:(10,1,False,0),4:(10,1,False,0),7:(1,9,True,1),9:(13,1,False,1),
        15:(11,1,False,-1),16:(10,1,False,0),19:(1,9,True,1),21:(4,4,True,1)}
selected=set(map(int,spec))
mods=[]
with tempfile.TemporaryDirectory() as d:
    tmp=Path(d)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(tmp/"enumerate")],check=True)
    for i in sorted(selected):
        s=spec[str(i)]
        p=PARENT[:5]+(MOVES[i],)+PARENT[6:]
        subprocess.run([str(tmp/"enumerate"),one.show(p)],cwd=tmp,check=True)
        data=(tmp/"open.txt").read_bytes()
        assert hashlib.sha256(data).hexdigest()==s["sha256"],(i,"open roster digest")
        opens=data.decode().splitlines()
        assert len(opens)==len(s["index"])==len(set(opens))
        index={t:j for j,t in enumerate(opens)}
        pumpns=f"BB6.Agent7Raw110Pumps{i:02}"
        pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0",
                  f"namespace {pumpns}","open BB6Coverage BB6Coverage.Agent31Pump"]
        pumps={}
        for j,key in enumerate(s["index"]):
            if key not in "XY": continue
            mod=one if key=="X" else multi
            p0=one.parse(opens[j]);ans=mod.candidate(p0,one.concrete_events(p0,6000))
            assert ans is not None,(i,j,key)
            code,info=mod.generate(j,p0,ans)
            pumps[j]=f"{pumpns}.M{j}"
            pumpcode.append(code)
            print(i,j,key,info,flush=True)
        pumpcode.append(f"end {pumpns}")
        pumpname=f"Raw110Pump{i:02}"
        (ROOT/(pumpname+".lean")).write_text("\n\n".join(pumpcode)+"\n")
        stats=Counter()
        def build(node):
            tag,*v=node;stats[tag]+=1
            if tag=="cycle":
                e,k,r,b=v
                return f".cycle {e} {k} {str(r).lower()} ({b})"
            if tag=="last":
                n,s0=v
                return f".last {n} {slot(s0)}"
            if tag=="open":
                j=index[v[0]]
                if j in pumps:return f".proven {pumps[j]}.table {pumps[j]}.never"
                a=s["bank"][int(s["index"][j],36)]
                rev=int(a[0]);dfa=[int(c,36) for c in a[1:]]
                n,D,L,R,z=masks(one.parse(v[0]),rev,dfa)
                return f".far {str(bool(rev)).lower()} {n} ⟨0,{D},{L},{R},{z}⟩"
            assert tag=="split"
            n,s0,kids=v;assert len(kids)==24
            return f".split {n} {slot(s0)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
        tree=json.loads((tmp/"tree.json").read_text())
        name=f"Raw110Kid{i:02}";mods.append(name)
        emit(name,["Raw110Base",pumpname],f"""
def kid{i:02} : Audit := {build(tree)}
theorem check{i:02} : zipCheck {B} (child110 {move(MOVES[i])}) kid{i:02} = true := by decide
""",chunk=True)
        assert stats["open"]==len(opens)
        print(i,stats,flush=True)
    # Recheck immediate cycles in the shared classifier, without trusting
    # the literal cycle parameters in this script as semantic evidence.
    for i,cycle in cycles.items():
        p=PARENT[:5]+(MOVES[i],)+PARENT[6:]
        subprocess.run([str(tmp/"enumerate"),one.show(p)],cwd=tmp,check=True)
        assert json.loads((tmp/"tree.json").read_text())==["cycle",*cycle]
kids=[];checks=[]
for i in range(24):
    if i in selected:
        kids.append(f".closed kid{i:02}")
        checks.append(f"  · exact check{i:02}")
    elif i in cycles:
        e,k,r,b=cycles[i]
        kids.append(f".closed (.cycle {e} {k} {str(r).lower()} ({b}))")
        checks.append("  · decide")
    else:
        kids.append(".unresolved")
        checks.append("  · rfl")
cases="\n".join(checks[12*w+6*r+q] for q,w,r in product(range(6),range(2),range(2)))
emit("Raw110Cut",["Raw110Base",*mods],"""
def kids110 : Move → PartialAudit := byPartialMove ["""+",\n".join(kids)+"""]
theorem kids110_checked (mv : Move) : partialCheck 7014 (child110 mv) (kids110 mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def cut110 : PartialAudit := .split 7 (2,true) kids110
theorem cut110_checked : partialCheck 7014 p110 cut110 = true := by
  change (zipQueryOK 7014 p110 7 (2,true) &&
    allMoves (fun mv => partialCheck 7014 (child110 mv) (kids110 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query110, allMoves_of _ kids110_checked⟩
def residual110 := partialResiduals p110 cut110
theorem residual110_count : residual110.length = 6 := by decide
theorem raw110_sound :
    ∀ m, compatible p110 m → WeightedBound 7014 m ∨
      ∃ e ∈ residual110, compatible e.2 m :=
  partialSound 7014 p110 cut110 p110_root p110_nohalt cut110_checked
#print axioms cut110_checked
#print axioms residual110_count
#print axioms raw110_sound
""")
