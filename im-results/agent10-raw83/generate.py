#!/usr/bin/env python3
"""Emit source-connected weighted TNF certificates for the A10Raw83 cylinder.

The complete enumeration, FAR searches and block saturation are untrusted
discovery. Every resulting leaf and split is checked by the original Lean
zipCheck. The shard plan separates expensive second-query subtrees and is
deterministically derived from the pinned ordered enumeration.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
sys.path.insert(0, str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
sys.path.insert(0, str(ROOT.parent/"agent10-tnf-multipump"))
from chunk_checks import partition
sys.path.insert(0, str(ROOT.parent/"agent10-raw108"))
import build_lb
build_lb.ROOT = ROOT
SPEC = json.loads((ROOT/"spec.json").read_text())
B = SPEC["bound"]
NS = "BB6.Agent10Raw83"
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]
GROUPS = 1
HEADER = f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
"""
def emit(name, imports, body):
    p = ROOT/(name+".lean")
    p.write_text("".join("import "+i+"\n" for i in sorted(set(imports)))+HEADER+body+f"\nend {NS}\n")
    return p

def size(node):
    return 1 + sum(map(size,node[3])) if node[0]=="split" else 1

def discover():
    target=ROOT/"generated"
    target.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),SPEC["parent"]],cwd=target,check=True)
    raw=(target/"open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest()==SPEC["sha"]
    opens=raw.decode().splitlines()
    assert len(opens)==len(set(opens))==SPEC["stats"]["open"]
    tree=json.loads((target/"tree.json").read_text())
    assert tree[:3]==["split",*SPEC["query"]]
    return opens,tree,target

def plan_only(tree):
    leaves=[]
    for i,k in enumerate(tree[3]):
        leaves.append((f"A10Raw83Kid{i:02}",size(k),i,None))
    bins=[[] for _ in range(GROUPS)]
    totals=[0]*GROUPS
    for row in sorted(leaves,key=lambda x:(-x[1],x[0])):
        k=min(range(GROUPS),key=lambda k:(totals[k],k))
        bins[k].append(row);totals[k]+=row[1]
    groups={f"g{k:02}":[x[0] for x in sorted(rows)] for k,rows in enumerate(bins)}
    print("group audit nodes",dict(zip(groups,totals)),flush=True)
    return groups,leaves

def witnesses(opens,target):
    bank=target/"far-bank.txt"
    bank.write_text("\n".join(SPEC["bank"])+"\n")
    search=target/"seeded_far"
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent47-raw114-cut/seeded_far.cpp"),"-o",str(search)],check=True)
    # Supplying maxd=0 disables the exhaustive search; the exact bank is used.
    out=subprocess.check_output([str(search),str(target/"open.txt"),"0",str(len(opens)),"0",str(bank)],text=True)
    far={int(i):c for i,c in (row.split(":") for row in out.splitlines())}
    blocks={int(i):v for i,v in SPEC["blocks"].items()}
    assert set(far)|set(blocks)==set(range(len(opens)))
    print("FAR bank hits",len(far),"explicit block witnesses",len(blocks),flush=True)
    return far,blocks

def main():
    opens,tree,target=discover()
    groups,leaves=plan_only(tree)
    config={"artifact_prefix":"raw83-shard","groups":groups}
    (ROOT/"shard_groups.json").write_text(json.dumps(config,indent=2,sort_keys=True)+"\n")
    if len(sys.argv)>1 and sys.argv[1]=="--plan":
        return
    selected=sys.argv[1] if len(sys.argv)>1 else "all"
    needed=set() if selected=="assemble" else set(groups[selected]) if selected!="all" else {x[0] for x in leaves}
    far,blocks=({}, {}) if selected=="assemble" else witnesses(opens,target)
    index={s:i for i,s in enumerate(opens)}
    stats=Counter()
    block_done=set()
    def render(node,imports,produce):
        tag,*v=node;stats[tag]+=1
        if tag=="cycle":
            e,k,r,b=v
            return f".cycle {e} {k} {str(bool(r)).lower()} ({b})" if produce else ""
        if tag=="last":
            n,s=v
            return f".last {n} {slot(s)}" if produce else ""
        if tag=="open":
            i=index[v[0]]
            if not produce:return ""
            if i in blocks:
                mod=f"A10Raw83Block{i}"
                ns=f"BB6.Agent10{mod}"
                if i not in block_done:
                    w,c,m,r=blocks[i]
                    build_lb.emit_block(mod,ns,v[0],dict(width=w,cap=c,mod=m,runs=r),active=w>=5)
                    block_done.add(i)
                imports.add(mod)
                return f".proven {ns}.table {ns}.never"
            code=far[i]
            d,D,L,R,z=masks(parse(v[0]),int(code[0]),[int(c,36) for c in code[1:]])
            return f".far {str(bool(int(code[0]))).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag=="split" and len(v[2])==24
        n,s,kids=v
        rs=[render(k,imports,produce) for k in kids]
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(rs)+"])" if produce else ""
    emit("A10Raw83Base",["CachedZipAudit"],f"""
abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,0⟩)
abbrev child (mv : Move) : PartialMachine := refine parent (0,true) (some mv)
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (pathEnd_nohalt root 2 (path.take 6) firstOneCylinder_no_assigned_halt)
theorem query : zipQueryOK {B} parent 9 (0,true) = true := by decide
""")
    def leaf_module(mod,nm,ck,table,node):
        imports={"A10Raw83Base"}
        produce=mod in needed
        body=render(node,imports,produce)
        if not produce:return
        p=emit(mod,imports,f"""
def {nm} : Audit := {body}
theorem {ck} : zipCheck {B} {table} {nm} = true := by rfl
""")
        text,_=partition(p.read_text(),limit=180)
        # The cached checker is proved equal to zipCheck. Use it only for
        # the concrete leaves/chunks; the structural joins stay unchanged.
        text=re.sub(r"(theorem [^\n]+ : zipCheck [^\n]+ = true := by) rfl",
                    r"\1\n  rw [← BB6.Agent10CachedAudit.root_check_eq]\n  rfl",text)
        p.write_text(text+f"\n#print axioms {NS}.{ck}\n")
    def assemble(mod,nm,ck,table,n,s,partnames,partchecks,imports):
        klist=",".join(partnames)
        cases="\n".join(f"  · exact {partchecks[12*w+6*r+q]}" for q,w,r in product(range(6),range(2),range(2)))
        emit(mod,imports,f"""
def {nm} : Audit := .split {n} {slot(s)} (byMove [{klist}])
theorem {ck} : zipCheck {B} {table} {nm} = true := by
  change (zipQueryOK {B} {table} {n} {slot(s)} && allMoves (fun mv => zipCheck {B} (refine {table} {slot(s)} (some mv)) (byMove [{klist}] mv))) = true
  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
""")
    stats["split"]+=1
    for i,k in enumerate(tree[3]):
        m=f"A10Raw83Kid{i:02}";nm=f"kid{i:02}";ck=f"check{i:02}"
        table=f"(child {move(MOVES[i])})"
        leaf_module(m,nm,ck,table,k)
    assert stats==Counter(SPEC["stats"]),stats
    assemble("A10Raw83Data","tree","tree_checked","parent",9,1,
             [f"kid{i:02}" for i in range(24)],[f"check{i:02}" for i in range(24)],
             [f"A10Raw83Kid{i:02}" for i in range(24)])
    p=ROOT/"A10Raw83Data.lean"
    s=p.read_text()
    end=f"\nend {NS}\n"
    assert s.endswith(end)
    p.write_text(s[:-len(end)]+f"""
noncomputable def certificate : WeightedTNFCertificate {B} parent 6 :=
  certifiedZip {B} parent tree parent_root parent_nohalt tree_checked

theorem all_completions : ∀ m, compatible parent m → WeightedBound {B} m :=
  certificate.sound

#print axioms tree_checked
#print axioms all_completions
"""+end)
    print("enumerated",stats,"block proofs generated",len(block_done),flush=True)
    if selected not in ("all","assemble"):
        (ROOT/"roots.txt").write_text("".join(str((ROOT/(m+".lean")).relative_to(REPO))+"\n" for m in groups[selected]))
        check_by_mod={m:(f"check{i:02}" if j is None else f"check{i:02}_{j:02}") for m,_,i,j in leaves}
        (ROOT/"theorems.txt").write_text("".join(NS+"."+check_by_mod[m]+"\n" for m in groups[selected]))

if __name__=="__main__":
    main()
