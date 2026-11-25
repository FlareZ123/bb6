"""Reproduce four complete raw114 E0 child candidates, emit sharded Lean audits."""
from pathlib import Path
from itertools import product
from collections import Counter
import hashlib, json, subprocess, tempfile, sys

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import parse, masks
from generate_sweeps import candidate, concrete_events, generate as generate_pump
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
PARENT="1RB---_1RC---_0RD---_1LD1RE_---0LD_------"
EXPECTED={
    "0RB":(541,9943,2135,366,3,"6b44d039c3b57475394193134abf2145c4e5f07e191bd38d0684e6917eb3cb25"),
    "1RC":(504,9350,2023,220,5,"d6a97d7920f8c05b830495f37b40d6ad35ca2e8b17a1046b1e72d1a93f562273"),
    "0LB":(810,15221,2964,446,3,"cbcb4008a9608012b3674c46fa6120fe8b6cad9ac2c7b9f34c321f06ff11f6d2"),
    "0LC":(758,13981,3271,183,5,"52c1d8aabb0a198a273ab34f9406bf8cebfabadee39d47d74959921904a22801"),
    "0RC":(521,9579,2194,211,5,"7d54fde6d04c02ac1fb0945b75a0c378c2bfde4da45730446b9bd5df235871fe"),
    "1LC":(1108,20288,4974,223,5,"948fd7e5c9a9bad562c1fb7d52893f649cafaa5bca9f9f34a606c05799d025f9")
}
PUMPS={
    "1RB0LA_1RC0LF_0RD1RF_1LD1RE_0RB0LD_1LA---":(108,220,104),
    "1RB1LF_1RC0LA_0RD0LB_1LD1RE_1RC0LD_---1LB":(3,19,8),
    "1RB1LF_1RC0LA_0RD0LB_1LD1RE_1RC0LD_---1LE":(3,19,8),
}
def emit_pumps():
    parts=["import SweepPumping","set_option maxRecDepth 100000",
           "set_option maxHeartbeats 0","set_option linter.unusedVariables false",
           "namespace BB6Coverage.Agent31Pump.Raw114Hard","open BB6Coverage"]
    for i,(row,expected) in enumerate(PUMPS.items()):
        p=parse(row)
        ans=candidate(p,concrete_events(p))
        assert ans is not None,row
        code,info=generate_pump(i,p,ans)
        assert info==expected,(row,info)
        parts.append(code)
    parts.append("end BB6Coverage.Agent31Pump.Raw114Hard")
    (ROOT/"Raw114HardPumps.lean").write_text("\n\n".join(parts)+"\n")
def move(a):
    return f"⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩"
def slot(s):
    return f"({s//2},{str(bool(s%2)).lower()})"
def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw114Far
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
"""+body+"\nend BB6.Agent47Raw114Far\n")
emit("Raw114FarBase",["ZipThreeHoleAudit"],"""
abbrev raw114 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,false,3⟩)
theorem raw114_root : raw114 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem raw114_nohalt : weightedTNFNoAssignedHalt raw114 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
abbrev raw114Child (mv : Move) := refine raw114 (4,false) (some mv)
theorem child_root (mv : Move) : raw114Child mv initialSlot = some (some ⟨true,true,1⟩) :=
  refine_preserves_firstOne raw114 (4,false) (some mv) (by decide) raw114_root
theorem child_nohalt (mv : Move) : weightedTNFNoAssignedHalt (raw114Child mv) :=
  weightedTNFNoAssignedHalt_refine _ _ _ raw114_nohalt
""")
def generate(a,work):
    sp,cy,la,op,s,sha=EXPECTED[a]
    flat=PARENT.replace("_","")
    flat=flat[:24]+a+flat[27:]
    table="_".join(flat[i:i+6] for i in range(0,36,6))
    subprocess.run([str(work/"enumerate"),table],cwd=work,check=True)
    tree=json.loads((work/"tree.json").read_text())
    assert tree[:3]==["split",9,s],tree[:3]
    raw=(work/"open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest()==sha,(a,hashlib.sha256(raw).hexdigest())
    rows=raw.decode().splitlines()
    assert len(rows)==len(set(rows))==op
    farrows=[row for row in rows if row not in PUMPS]
    (work/"far-rows.txt").write_text("\n".join(farrows)+"\n")
    bank="pump-far-bank.txt" if a in ("0RB","1RC") else "far-cut-bank.txt"
    out=subprocess.check_output([str(work/"far"),str(work/"far-rows.txt"),"0",str(len(farrows)),"0",str(ROOT/bank)],text=True)
    found=dict((int(i),v) for i,v in (line.split(":") for line in out.splitlines()))
    assert set(found)==set(range(len(farrows)))
    certs={row:f".proven BB6Coverage.Agent31Pump.Raw114Hard.M{i}.table BB6Coverage.Agent31Pump.Raw114Hard.M{i}.never"
           for i,row in enumerate(PUMPS) if row in rows}
    for i,row in enumerate(farrows):
        code=found[i]
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,16) for c in code[1:]])
        certs[row]=f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    stats=Counter()
    def full(node):
        tag,*v=node
        stats[tag]+=1
        if tag=="cycle":
            e,k,r,b=v
            return f".cycle {e} {k} {str(r).lower()} ({b})"
        if tag=="last":
            n,t=v
            return f".last {n} {slot(t)}"
        if tag=="open": return certs[v[0]]
        assert tag=="split",node
        n,t,kids=v
        assert len(kids)==24
        return f".split {n} {slot(t)} (byMove [\n"+",\n".join(full(k) for k in kids)+"])"
    mods=[]
    for i,kid in enumerate(tree[3]):
        name=f"Raw114Far{a}Kid{i:02}"
        mods.append(name)
        body=f"""
def kid{a}{i:02} : Audit := {full(kid)}
theorem check{a}{i:02} : zipCheck 7014
    (refine (raw114Child {move(a)}) {slot(s)} (some {move(MOVES[i])}))
    kid{a}{i:02} = true := by decide
"""
        emit(name,["Raw114FarBase"]+(["Raw114HardPumps"] if a in ("0RB","1RC") else []),body)
    stats["split"]+=1
    assert stats==Counter(split=sp,cycle=cy,last=la,open=op),(a,stats)
    cases="\n".join(f"  · exact check{a}{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    emit(f"Raw114Far{a}Data",mods,f"""
def kids{a} : Move → Audit := byMove [{",".join(f"kid{a}{i:02}" for i in range(24))}]
theorem kids{a}_checked (mv : Move) : zipCheck 7014
    (refine (raw114Child {move(a)}) {slot(s)} (some mv)) (kids{a} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree{a} : Audit := .split 9 {slot(s)} kids{a}
theorem tree{a}_checked : zipCheck 7014 (raw114Child {move(a)}) tree{a} = true := by
  change (zipQueryOK 7014 (raw114Child {move(a)}) 9 {slot(s)} &&
    BB6.Agent31ThreeHole.allMoves (fun mv => zipCheck 7014
      (refine (raw114Child {move(a)}) {slot(s)} (some mv)) (kids{a} mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide,allMoves_of _ kids{a}_checked⟩
theorem all{a} : ∀ m, compatible (raw114Child {move(a)}) m → WeightedBound 7014 m :=
  (certifiedZip 7014 _ _ (child_root _) (child_nohalt _) tree{a}_checked).sound
#print axioms all{a}
""")
    closed_cycles={"0LD":".cycle 7 2 true 1","0LE":".cycle 13 1 false (-1)",
                   "0RD":".cycle 3 8 true 1","0RE":".cycle 14 1 true 2",
                   "1LD":".cycle 5 4 true 1","1LE":".cycle 13 1 false (-1)",
                   "1RD":".cycle 9 5 true 3","1RE":".cycle 11 1 true 3"}
    children=[".closed ("+closed_cycles[b]+")" if b in closed_cycles else
              ".closed tree"+a if a==b else ".unresolved" for b in MOVES]
    checks="\n".join("  · "+("exact tree"+a+"_checked" if MOVES[12*w+6*r+q]==a else "decide")
                     for q,w,r in product(range(6),range(2),range(2)))
    emit(f"Raw114Far{a}Cut",["PartialAudit",f"Raw114Far{a}Data"],f"""
open BB6.Agent47PartialAudit
def cutKids{a} : Move → PartialAudit := byPartialMove [{",".join(children)}]
theorem cutKids{a}_checked (mv : Move) : partialCheck 7014 (raw114Child mv) (cutKids{a} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{checks}
def cut{a} : PartialAudit := .split 8 (4,false) cutKids{a}
theorem cut{a}_checked : partialCheck 7014 raw114 cut{a} = true := by
  change (zipQueryOK 7014 raw114 8 (4,false) &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014 (raw114Child mv) (cutKids{a} mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ cutKids{a}_checked⟩
def residual{a} : List (List Move × PartialMachine) := partialResiduals raw114 cut{a}
theorem residual{a}_count : residual{a}.length = 15 := by decide
theorem cut{a}_sound :
    ∀ m, compatible raw114 m → WeightedBound 7014 m ∨
      ∃ e ∈ residual{a}, compatible e.2 m :=
  partialSound 7014 raw114 cut{a} raw114_root raw114_nohalt cut{a}_checked
#print axioms cut{a}_sound
#print axioms residual{a}_count
""")
    print(a,stats)
emit_pumps()
with tempfile.TemporaryDirectory() as d:
    work=Path(d)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99"/"enumerate.cpp"),"-o",str(work/"enumerate")],check=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT/"seeded_far.cpp"),"-o",str(work/"far")],check=True)
    args=sys.argv[1:] or list(EXPECTED)
    for a in args: generate(a,work)
