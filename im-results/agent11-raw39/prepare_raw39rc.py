#!/usr/bin/env python3
"""Generate complete source-audit candidate for the Raw39 A1=0RC child."""
import hashlib
import json
import re
from itertools import product
from pathlib import Path
import prepare_raw39 as common
import gen_rc_counters as counter

ROOT=Path(__file__).resolve().parent
BUILD=ROOT/"_build0RC"
DATA=json.loads((ROOT/"rc-witnesses.json").read_text())
BOUND=2354
CHILD="1RB0RC_1RC---_0RD---_1LD0RA_------_------"
m=common.m
parse=common.parse
masks=common.masks
slot=common.slot
move=common.move
MOVES=common.MOVES

HEADER=common.HEADER.replace("BB6.Agent11Raw39","BB6.Agent11Raw39RC")
FOOTER=common.FOOTER.replace("BB6.Agent11Raw39","BB6.Agent11Raw39RC")
PUMP_HEADER=common.PUMP_HEADER.replace("BB6.Agent11Raw39Pumps","BB6.Agent11Raw39RCPumps")

def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join(f"import {x}\n" for x in imports)+HEADER+body+FOOTER)

def generate():
    BUILD.mkdir(exist_ok=True)
    common.run("g++","-std=c++17","-O3",common.SOURCE/"fast_enum.cpp","-o",BUILD/"enum")
    res=common.run(BUILD/"enum",CHILD,cwd=BUILD,text=True,capture_output=True)
    print(res.stdout,flush=True)
    tree=json.loads((BUILD/"tree.json").read_text())
    opens=(BUILD/"open.txt").read_text().splitlines()
    assert hashlib.sha256((BUILD/"open.txt").read_bytes()).hexdigest()==DATA["open_sha256"]
    assert len(opens)==len(set(opens))==2166
    assert common.counts(tree)==DATA["stats"] and tree[:3]==["split",7,5]
    index={s:i for i,s in enumerate(opens)}
    special,chunks=counter.generate(ROOT,opens)
    assert len(special)==16
    # The modular invariant is independent of E/F naming. Generate its
    # exact state-renamed copy, leaving all costs and grammar lemmas intact.
    gram=(ROOT/"Raw39Hard56.lean").read_text()
    assert opens[56].replace("_","")=="1RB0RC1RC---0RD0LE1LD0RA1LE1RF1RA0LF"
    assert counter.swap(opens[56])==opens[194].replace("_","")
    mirror=gram.replace("Agent11Raw39Hard56","Agent11Raw39Hard194")
    mirror=mirror.replace("⟨5,","⟨4,").replace("sweepL table 5 ","sweepL table 4 ").replace("⟨4,_,by decide,a0_case1","⟨5,_,by decide,a0_case1")
    mirror=re.sub(r"def table : PartialMachine :=.*?(?=\nabbrev O)",lambda _:m.tab(parse(opens[194]))+"\n",mirror,flags=re.S)
    (ROOT/"Raw39Hard194.lean").write_text(mirror)
    for i in [56,194]:
        name=f"Raw39Hard{i}";ns=f"BB6.Agent11Raw39Hard{i}"
        special[i]=(ns+".table",ns+".never")
        chunks.append(name)
    for start in range(0,len(DATA["specs"]),10):
        name=f"Raw39RCPumps{start//10:02}"
        out=[PUMP_HEADER]
        for i,t,side,q,a,b,ss in DATA["specs"][start:start+10]:
            i,t,q,a,b=map(int,(i,t,q,a,b));assert i not in special
            p=parse(opens[i])
            w=m.clean(tuple((v.lstrip("*"),v.startswith("*")) for v in ss.split(",")))
            v=counter.nextword(w)
            st=m.C(q,w if side=="R" else (),w if side=="L" else ())
            tg=m.C(q,v if side=="R" else (),v if side=="L" else ())
            ans=m.pump(p,st,tg,500);assert ans is not None,i
            code,info=m.generate(i,p,(t,st,tg,ans));assert info==(t,a,b),(i,info)
            out.append(code)
            ns=f"BB6.Agent11Raw39RCPumps.M{i}"
            special[i]=(ns+".table",ns+".never")
        out.append("end BB6.Agent11Raw39RCPumps")
        (ROOT/(name+".lean")).write_text("\n\n".join(out)+"\n")
        chunks.append(name)
    assert len(special)==62
    late={i:(n,s) for i,n,s in DATA["late"]}
    assert not set(late)&set(special) and len(late)==4
    bank=DATA["bank"];assert len(bank)==len(set(bank))==63
    common.run("g++","-std=c++20","-O3",common.SOURCE/"bank.cpp","-o",BUILD/"bank")
    (BUILD/"bank.txt").write_text("\n".join(bank)+"\n")
    todo=set(range(len(opens)))-set(special)-set(late)
    text="".join(f"{i} {opens[i].replace('_','')}\n" for i in sorted(todo))
    res=common.run(BUILD/"bank",BUILD/"bank.txt",input=text,text=True,capture_output=True)
    assert not res.stderr.strip(),res.stderr
    found={int(i):a for i,a in (line.split() for line in res.stdout.splitlines())}
    assert set(found)==todo
    far={}
    for i,a in found.items():
        for c in [a]+[c for c in bank if c!=a]:
            try:
                d,D,L,R,z=masks(parse(opens[i]),int(c[0]),[int(ch,36) for ch in c[1:]])
                far[i]=f".far {str(bool(int(c[0]))).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
                break
            except (AssertionError,IndexError,ValueError):
                continue
        else:raise AssertionError((i,opens[i]))
    assert len(far)==2100
    def build(node):
        tag,*v=node
        if tag=="cycle":
            e,k,r,b=v
            return f".cycle {e} {k} {str(r).lower()} ({b})"
        if tag=="last":
            n,s=v
            return f".last {n} {slot(s)}"
        if tag=="open":
            i=index[v[0]]
            if i in special:
                p,h=special[i]
                return f".proven ({p}) (fun m hm => {h} m hm)"
            if i in late:
                n,s=late[i]
                return f".last {n} {slot(s)}"
            return far[i]
        assert tag=="split"
        n,s,kids=v
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(map(build,kids))+"])"

    emit("Raw39RCBase",["ZipThreeHoleAudit"]+chunks,r"""
abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
theorem p39_root : p39 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p39_nohalt : weightedTNFNoAssignedHalt p39 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
abbrev p0RC : PartialMachine := refine p39 (0,true) (some ⟨false,true,2⟩)
theorem p0RC_root : p0RC initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p0RC_nohalt : weightedTNFNoAssignedHalt p0RC :=
  weightedTNFNoAssignedHalt_refine _ _ _ p39_nohalt
abbrev childRC (mv : Move) := refine p0RC (2,true) (some mv)
theorem queryRC : zipQueryOK 2354 p0RC 7 (2,true) = true := by decide
theorem query39 : zipQueryOK 2354 p39 6 (0,true) = true := by decide
""")
    kids=[]
    for i,k in enumerate(tree[3]):
        name=f"Raw39RCKid{i:02}";kids.append(name)
        emit(name,["Raw39RCBase"],f"def kid{i:02} : Audit := {build(k)}\n\n"
             f"theorem check{i:02} : zipCheck {BOUND} (childRC {move(MOVES[i])}) kid{i:02} = true := by decide\n")
        p=ROOT/(name+".lean")
        content,n=common.partition(p.read_text(),180);p.write_text(content)
        print(name,"subproofs",n,flush=True)
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    names=",".join(f"kid{i:02}" for i in range(24))
    emit("Raw39RCData",["Raw39RCBase"]+kids,f"""
def kidsRC : Move → Audit := byMove [{names}]
theorem kidsRC_checked (mv : Move) : zipCheck 2354 (childRC mv) (kidsRC mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree0RC : Audit := .split 7 (2,true) kidsRC
theorem tree0RC_checked : zipCheck 2354 p0RC tree0RC = true := by
  change (zipQueryOK 2354 p0RC 7 (2,true) && allMoves (fun mv => zipCheck 2354 (childRC mv) (kidsRC mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨queryRC,allMoves_of _ kidsRC_checked⟩
noncomputable def certificate0RC : WeightedTNFCertificate 2354 p0RC 6 :=
  certifiedZip 2354 p0RC tree0RC p0RC_root p0RC_nohalt tree0RC_checked
theorem all0RC : ∀ m, compatible p0RC m → WeightedBound 2354 m := certificate0RC.sound
#print axioms tree0RC_checked
#print axioms all0RC
""")
    cycles={1:(0,10,True,0),2:(13,1,False,1),3:(10,1,False,0),6:(0,8,True,0),9:(0,8,True,0),
            14:(0,12,True,0),15:(10,1,False,0),18:(0,8,True,0),21:(0,8,True,0)}
    branches=[]
    for i in range(24):
        if i==8:branches.append(".closed tree0RC")
        elif i in cycles:
            e,k,r,b=cycles[i]
            branches.append(f".closed (.cycle {e} {k} {str(r).lower()} ({b}))")
        else:branches.append(".unresolved")
    pcs="\n".join("  · exact tree0RC_checked" if 12*w+6*r+q==8 else "  · decide"
                  for q,w,r in product(range(6),range(2),range(2)))
    branch_text=",\n  ".join(branches)
    emit("Raw39RCPartial",["Raw39RCData","PartialAudit"],f"""
open BB6.Agent47PartialAudit
def partialKids : Move → PartialAudit := byPartialMove [
  {branch_text}]
def partialTree : PartialAudit := .split 6 (0,true) partialKids
theorem partialKids_checked (mv : Move) :
    partialCheck 2354 (refine p39 (0,true) (some mv)) (partialKids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{pcs}
theorem partialTree_checked : partialCheck 2354 p39 partialTree = true := by
  change (zipQueryOK 2354 p39 6 (0,true) && allMoves (fun mv => partialCheck 2354 (refine p39 (0,true) (some mv)) (partialKids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query39,allMoves_of _ partialKids_checked⟩
def residuals := partialResiduals p39 partialTree
theorem residual_count : residuals.length = 14 := by decide
theorem cut_sound : ∀ m, compatible p39 m →
    WeightedBound 2354 m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  partialSound 2354 p39 partialTree p39_root p39_nohalt partialTree_checked
#print axioms cut_sound
#print axioms residual_count
""")
    manifest=dict(parent=common.PARENT,child=CHILD,bound=BOUND,open_sha256=DATA["open_sha256"],
                  stats=DATA["stats"],symbolic=62,late=4,far=2100,remaining_root_children=14,
                  tree_sha256=hashlib.sha256((BUILD/"tree.json").read_bytes()).hexdigest(),
                  proof_modules=chunks,child_modules=kids)
    (ROOT/"manifest-rc.json").write_text(json.dumps(manifest,indent=2)+"\n")
    print("Raw39 0RC source candidate generated",manifest,flush=True)

if __name__=="__main__":
    generate()
