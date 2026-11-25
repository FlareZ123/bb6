"""Reproduce the full raw114 E0 frontier, emit sharded Lean audits."""
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
    "0LA":(1286,22146,6792,641,1,"1d67ff9fcf260251c4375a6b8d28438c47da2171d0165f5d27fa9dffeec7f22a"),
    "0LB":(810,15221,2964,446,3,"cbcb4008a9608012b3674c46fa6120fe8b6cad9ac2c7b9f34c321f06ff11f6d2"),
    "0LC":(758,13981,3271,183,5,"52c1d8aabb0a198a273ab34f9406bf8cebfabadee39d47d74959921904a22801"),
    "0LF":(1356,24869,5452,868,11,"5898dbdb3cd6717c36b8247a424e73fb86ddb7a4dc1bae7c08afbd2e977b2acb"),
    "0RA":(575,10136,2802,288,1,"2796fa9885fe07fe0cb38f333851e5103265fc5611bb02b612624d5643e07db9"),
    "0RB":(541,9943,2135,366,3,"6b44d039c3b57475394193134abf2145c4e5f07e191bd38d0684e6917eb3cb25"),
    "0RC":(521,9579,2194,211,5,"7d54fde6d04c02ac1fb0945b75a0c378c2bfde4da45730446b9bd5df235871fe"),
    "0RF":(754,13998,2908,437,11,"90f3dec078c8b199ce083210e086c2f446ea2b594175129dffc995a00ddcd098"),
    "1LA":(1616,27422,9069,678,1,"8f421034de834be88ce93aa2765775223e906f6138b805f0b74f77a7c48fc62d"),
    "1LB":(1328,23857,5972,716,3,"a844b79ba45142c323ec05e0be1c007f4abf0be85a367c714c179e0e97065552"),
    "1LC":(1108,20288,4974,223,5,"948fd7e5c9a9bad562c1fb7d52893f649cafaa5bca9f9f34a606c05799d025f9"),
    "1LF":(1634,29998,6297,1288,11,"95d650de7252b452134ab3a8bb5e0874c38dc62e33f88b3475a45bdc986e091e"),
    "1RA":(768,13108,3898,659,1,"f0581b976a28631bfc3d6e2a0d1690487677e9872a61024a4669e0247be6f7fd"),
    "1RB":(670,12200,2540,671,3,"34081aa25121041b6ee8998c94d010051295a7b30dce6a36672b3a407fb13f00"),
    "1RC":(504,9350,2023,220,5,"d6a97d7920f8c05b830495f37b40d6ad35ca2e8b17a1046b1e72d1a93f562273"),
    "1RF":(1493,27104,6213,1023,11,"71436e4daaf57c84882ccadf26ae9e6537b72e7ccbb259c7bd8416d80d3e0ead")
}
MANIFEST={}
for i,line in enumerate((ROOT/"raw114-hard-manifest.txt").read_text().splitlines()):
    if not line or line.startswith("#"): continue
    kind,row,params=line.split()
    assert row not in MANIFEST
    MANIFEST[row]=(kind,i,params)
assert len(MANIFEST)==112
HOLDOUTS={}
for row, module, suffix in zip(
    [row for row,(kind,_,_) in MANIFEST.items() if kind=="open"],
    [*(f"Raw114Pair{i}" for i in range(5)), "Raw114LongSweep", "Raw114Triple", "Raw114Binary"],
    [""]*5+[".M0","",""]):
    HOLDOUTS[row]=(module,"BB6Coverage.Agent31Pump."+module+suffix)
assert len(HOLDOUTS)==8
import multi_sweep
sys.path.insert(0,str(ROOT.parent/"agent1-ngram"))
from emit_ngram import emit as emit_ngram
def move(a):
    return f"⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩"
def slot(s):
    return f"({s//2},{str(bool(s%2)).lower()})"
def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw114Complete
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""+body+"\nend BB6.Agent47Raw114Complete\n")
emit("Raw114CompleteBase",["PartialAudit","ZipPrefixAudit"],"""
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
    farrows=[row for row in rows if row not in MANIFEST]
    (work/"far-rows.txt").write_text("\n".join(farrows)+"\n")
    out=subprocess.check_output([str(work/"far"),str(work/"far-rows.txt"),"0",str(len(farrows)),"0",str(ROOT/"all-far-bank.txt")],text=True)
    found=dict((int(i),v) for i,v in (line.split(":") for line in out.splitlines()))
    assert set(found)==set(range(len(farrows)))
    certs={}
    for i,row in enumerate(farrows):
        code=found[i]
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,16) for c in code[1:]])
        certs[row]=f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    ns=f"BB6Coverage.Agent31Pump.Raw114Complete{a}"
    ns_ng=f"BB6.Agent1NGram.Raw114Complete{a}"
    pumps=[]
    ngrams=[]
    kinds=Counter()
    holdout_imports=[]
    for row in rows:
        if row not in MANIFEST: continue
        kind,i,params=MANIFEST[row]
        kinds[kind]+=1
        if kind in ("single","multi"):
            p=parse(row)
            if kind=="single":
                ans=candidate(p,concrete_events(p))
                assert ans is not None,row
                code,info=generate_pump(i,p,ans)
            else:
                ans=multi_sweep.discover(p)
                assert ans is not None,row
                code,info=multi_sweep.generate(i,p,ans)
            assert info==tuple(map(int,params.split(","))),(row,info)
            pumps.append(code)
            certs[row]=f".proven {ns}.M{i}.table {ns}.M{i}.never"
        elif kind=="last":
            n,t=map(int,params.split(","))
            certs[row]=f".last {n} {slot(t)}"
        elif kind=="ngram":
            inp=f"{i} {row}\n"
            out=subprocess.check_output([str(work/"ngram"),params],input=inp,text=True)
            ident,data=out.strip().split(maxsplit=1)
            assert int(ident)==i and data.split()[0]==params
            ngrams.append(emit_ngram(str(i),row,data))
            certs[row]=f".proven {ns_ng}.p{i} {ns_ng}.never{i}"
        elif kind=="open":
            module,ns_hold=HOLDOUTS[row]
            holdout_imports.append(module)
            certs[row]=f".proven {ns_hold}.table {ns_hold}.never"
        else: raise ValueError(kind)
    imports=["Raw114CompleteBase"]+sorted(set(holdout_imports))
    if pumps:
        name=f"Raw114Complete{a}Pumps"
        parts=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {ns}","open BB6Coverage",*pumps,f"end {ns}"]
        (ROOT/(name+".lean")).write_text("\n\n".join(parts)+"\n")
        imports.append(name)
    if ngrams:
        name=f"Raw114Complete{a}NGram"
        parts=["import NGramCertificate","set_option maxRecDepth 100000","set_option maxHeartbeats 0",f"namespace {ns_ng}","open BB6Coverage BB6.Agent1NGram",*ngrams,f"end {ns_ng}"]
        (ROOT/(name+".lean")).write_text("\n\n".join(parts)+"\n")
        imports.append(name)
    stats=Counter()
    def partial(x):
        closed,code=x
        return ".closed ("+code+")" if closed else code
    def build(node):
        tag,*v=node
        stats[tag]+=1
        if tag=="cycle":
            e,k,r,b=v
            return True,f".cycle {e} {k} {str(r).lower()} ({b})"
        if tag=="last":
            n,t=v
            return True,f".last {n} {slot(t)}"
        if tag=="open":
            code=certs[v[0]]
            return (True,code) if code is not None else (False,".unresolved")
        assert tag=="split",node
        n,t,kids=v
        assert len(kids)==24
        children=[build(k) for k in kids]
        if all(closed for closed,_ in children):
            return True,f".split {n} {slot(t)} (byMove [\n"+",\n".join(code for _,code in children)+"])"
        return False,f".split {n} {slot(t)} (byPartialMove [\n"+",\n".join(map(partial,children))+"])"
    mods=[]
    for i,kid in enumerate(tree[3]):
        name=f"Raw114Complete{a}Kid{i:02}"
        mods.append(name)
        closed,code=build(kid)
        assert closed,(a,i)
        emit(name,imports,f"""
def auditKid{a}{i:02} : Audit := {code}
def kid{a}{i:02} : PartialAudit := .closed auditKid{a}{i:02}
theorem check{a}{i:02} : partialCheck 7014
    (refine (raw114Child {move(a)}) {slot(s)} (some {move(MOVES[i])}))
    kid{a}{i:02} = true := by
  change zipCheck 7014 _ auditKid{a}{i:02} = true
  rw [← BB6.Agent48PrefixAudit.prefixCheck_eq]
  decide
""")
    stats["split"]+=1
    assert stats==Counter(split=sp,cycle=cy,last=la,open=op),(a,stats)
    cases="\n".join(f"  · exact check{a}{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    emit(f"Raw114Complete{a}Data",mods,f"""
def kids{a} : Move → PartialAudit := byPartialMove [{",".join(f"kid{a}{i:02}" for i in range(24))}]
theorem kids{a}_checked (mv : Move) : partialCheck 7014
    (refine (raw114Child {move(a)}) {slot(s)} (some mv)) (kids{a} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree{a} : PartialAudit := .split 9 {slot(s)} kids{a}
theorem tree{a}_checked : partialCheck 7014 (raw114Child {move(a)}) tree{a} = true := by
  change (zipQueryOK 7014 (raw114Child {move(a)}) 9 {slot(s)} &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014
      (refine (raw114Child {move(a)}) {slot(s)} (some mv)) (kids{a} mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide,allMoves_of _ kids{a}_checked⟩
def residual{a} : List (List Move × PartialMachine) := partialResiduals (raw114Child {move(a)}) tree{a}
theorem count{a} : residual{a}.length = 0 := by decide
#print axioms tree{a}_checked
#print axioms count{a}
""")
    print(a,stats,kinds,flush=True)

def combine():
    cycles={"0LD":".cycle 7 2 true 1","0LE":".cycle 13 1 false (-1)",
            "0RD":".cycle 3 8 true 1","0RE":".cycle 14 1 true 2",
            "1LD":".cycle 5 4 true 1","1LE":".cycle 13 1 false (-1)",
            "1RD":".cycle 9 5 true 3","1RE":".cycle 11 1 true 3"}
    children=[".closed ("+cycles[b]+")" if b in cycles else "tree"+b for b in MOVES]
    checks="\n".join("  · "+("decide" if b in cycles else "exact tree"+b+"_checked")
                     for q,w,r in product(range(6),range(2),range(2))
                     for b in [MOVES[12*w+6*r+q]])
    count=0
    emit("Raw114CompleteData",[f"Raw114Complete{a}Data" for a in EXPECTED],f"""
def rootKids : Move → PartialAudit := byPartialMove [{",".join(children)}]
theorem rootKids_checked (mv : Move) : partialCheck 7014 (raw114Child mv) (rootKids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{checks}
def rootTree : PartialAudit := .split 8 (4,false) rootKids
theorem checked : partialCheck 7014 raw114 rootTree = true := by
  change (zipQueryOK 7014 raw114 8 (4,false) &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014 (raw114Child mv) (rootKids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ rootKids_checked⟩
def raw114Residuals : List (List Move × PartialMachine) := partialResiduals raw114 rootTree
theorem residual_count : raw114Residuals.length = {count} := by decide
def slots : List Slot := (List.finRange 6).flatMap fun q => [false,true].map fun b => (q,b)
theorem residual_one_hole :
    raw114Residuals.all (fun e => (slots.filter fun s => (e.2 s).isNone).length == 1) = true := by decide
theorem raw114_complete_sound :
    ∀ m, compatible raw114 m → WeightedBound 7014 m ∨
      ∃ e ∈ raw114Residuals, compatible e.2 m :=
  partialSound 7014 raw114 rootTree raw114_root raw114_nohalt checked
theorem raw114_all (m : Machine) (hm : compatible raw114 m) : WeightedBound 7014 m := by
  rcases raw114_complete_sound m hm with hb | ⟨e,he,_⟩
  · exact hb
  · have hnil : raw114Residuals = [] := by simpa using residual_count
    simp [hnil] at he
#print axioms raw114_all
#print axioms raw114_complete_sound
#print axioms residual_count
#print axioms residual_one_hole
""")

if sys.argv[1:]==["--combine"]:
    combine()
else:
    with tempfile.TemporaryDirectory() as d:
        work=Path(d)
        subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99"/"enumerate.cpp"),"-o",str(work/"enumerate")],check=True)
        subprocess.run(["g++","-std=c++17","-O3",str(ROOT/"seeded_far.cpp"),"-o",str(work/"far")],check=True)
        subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent1-ngram"/"ngram.cpp"),"-o",str(work/"ngram")],check=True)
        for a in sys.argv[1:] or EXPECTED: generate(a,work)
    combine()
