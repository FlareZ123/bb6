#!/usr/bin/env python3
"""Replay raw111, generate kernel-checkable PARTIAL audit shards.

The external C++ searches are untrusted: every positive certificate is checked
by Lean. A missing certificate is always emitted as .unresolved.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent31-three-hole-tnf"))
from generate_four_hole import parse, masks
import symbolic

PARENT = "1RB---_1RC---_0RD---_1LD1RE_---0RC_------"
MOVES = [w + d + q for w, d, q in product("01", "LR", "ABCDEF")]
SHA = "0964ff7820b2745ddda1e05cd54a4b4f5774688bdbf4dc8f12eebf03ace19e0c"
HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw111
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""

def emit(name, imports, body):
    (ROOT / (name + ".lean")).write_text(
        "".join("import " + x + "\n" for x in imports) + HEADER + body +
        "\nend BB6.Agent47Raw111\n"
    )

def move(a):
    return f"⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩"

def slot(s):
    return f"({s//2},{str(bool(s%2)).lower()})"

def wrap(x):
    closed, code = x
    return ".closed (" + code + ")" if closed else code

def cases(fn):
    return "\n".join("  · exact " + fn(12*w + 6*r + q)
                     for q,w,r in product(range(6),range(2),range(2)))

CASES = """
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""

def main():
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for source, target in [
            (ROOT.parent/"agent2-tnf-raw99"/"enumerate.cpp", "enumerate"),
            (ROOT.parent/"agent47-raw114-cut"/"seeded_far.cpp", "far"),
        ]:
            subprocess.run(["g++","-std=c++17","-O3",str(source),"-o",str(work/target)],check=True)
        subprocess.run([str(work/"enumerate"), PARENT],cwd=work,check=True)
        tree = json.loads((work/"tree.json").read_text())
        assert tree[:3] == ["split",7,5]
        raw = (work/"open.txt").read_bytes()
        assert hashlib.sha256(raw).hexdigest() == SHA
        rows = raw.decode().splitlines()
        assert len(rows) == len(set(rows)) == 7069
        out = subprocess.check_output([str(work/"far"),str(work/"open.txt"),"0",str(len(rows)),"0",str(ROOT/"far-bank.txt")],text=True)
    found = dict((int(i),v) for i,v in (line.split(":") for line in out.splitlines()))
    assert len(found) == 6844
    certs = {}
    for i,code in found.items():
        d,D,L,R,z = masks(parse(rows[i]),int(code[0]),[int(c,16) for c in code[1:]])
        certs[rows[i]] = f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    unresolved = [row for row in rows if row not in certs]
    assert len(unresolved) == 225
    assert hashlib.sha256(("\n".join(unresolved)+"\n").encode()).hexdigest() == "ff89a913989ef6bf47d8eac232c16660b2ed9cf9e4fa0010e181b9c53e48a588"
    assert Counter(row.count("---") for row in unresolved) == {1:220,2:5}
    with tempfile.TemporaryDirectory() as tmp:
        more, imports = symbolic.generate(unresolved, Path(tmp))
    certs.update(more)
    unresolved = [row for row in unresolved if row not in more]
    assert not unresolved
    (ROOT/"unresolved.txt").write_text("\n".join(unresolved)+"\n")
    if "--symbolic-only" in sys.argv:
        print("Symbolic candidates", len(more), "unresolved", unresolved)
        return
    stats=Counter()

    def build(node):
        tag,*v=node
        stats[tag]+=1
        if tag=="cycle":
            e,k,r,b=v
            return True,f".cycle {e} {k} {str(r).lower()} ({b})"
        if tag=="last":
            n,s=v
            return True,f".last {n} {slot(s)}"
        if tag=="open":
            if v[0] in certs:
                return True,certs[v[0]]
            return False,".unresolved"
        assert tag=="split"
        n,s,kids=v
        children=[build(k) for k in kids]
        assert len(children)==24
        if all(x[0] for x in children):
            return True,f".split {n} {slot(s)} (byMove [\n"+",\n".join(x[1] for x in children)+"])"
        return False,f".split {n} {slot(s)} (byPartialMove [\n"+",\n".join(map(wrap,children))+"])"

    def deps(node):
        if node[0]=="open":
            return {imports[node[1]]} if node[1] in imports else set()
        if node[0]=="split":
            return set().union(*(deps(k) for k in node[3]))
        return set()

    def checked(name, p, audit):
        return f"""
def {name} : PartialAudit := {wrap(audit)}
theorem {name}_checked : partialCheck 7014 ({p}) {name} = true := by
  rw [← partialPrefix_eq]
  decide
"""

    mods=[]
    for i,node in enumerate(tree[3]):
        branch=f"Raw111Branch{i:02}"
        mods.append(branch)
        p=f"child {move(MOVES[i])}"
        name=f"branch{i:02}"
        if node[0]!="split":
            emit(branch,["Raw111Prefix"]+sorted(deps(node)),checked(name,p,build(node)))
            continue
        _,n,s,kids=node
        stats["split"]+=1
        parts=[]
        kn=lambda j:f"kid{i:02}_{j:02}"
        for j,kid in enumerate(kids):
            module=f"Raw111Kid{i:02}_{j:02}"
            parts.append(module)
            child=f"refine ({p}) {slot(s)} (some {move(MOVES[j])})"
            emit(module,["Raw111Prefix"]+sorted(deps(kid)),checked(kn(j),child,build(kid)))
        emit(branch,parts,f"""
def kids{i:02} : Move → PartialAudit := byPartialMove [{','.join(kn(j) for j in range(24))}]
theorem kids{i:02}_checked (mv : Move) :
    partialCheck 7014 (refine ({p}) {slot(s)} (some mv)) (kids{i:02} mv) = true := by
{CASES}{cases(lambda j:kn(j)+"_checked")}
def {name} : PartialAudit := .split {n} {slot(s)} kids{i:02}
theorem {name}_checked : partialCheck 7014 ({p}) {name} = true := by
  change (zipQueryOK 7014 ({p}) {n} {slot(s)} &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014
      (refine ({p}) {slot(s)} (some mv)) (kids{i:02} mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ kids{i:02}_checked⟩
""")
    stats["split"]+=1
    assert stats==Counter(split=12821,cycle=234495,last=53320,open=7069),stats
    emit("Raw111Data",mods,f"""
def rootKids : Move → PartialAudit := byPartialMove [{','.join(f'branch{i:02}' for i in range(24))}]
theorem rootKids_checked (mv : Move) : partialCheck 7014 (child mv) (rootKids mv) = true := by
{CASES}{cases(lambda j:f"branch{j:02}_checked")}
def tree : PartialAudit := .split 7 (2,true) rootKids
theorem checked : partialCheck 7014 parent tree = true := by
  change (zipQueryOK 7014 parent 7 (2,true) &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014 (child mv) (rootKids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ rootKids_checked⟩
def residuals := partialResiduals parent tree
theorem residual_count : residuals.length = 0 := by decide
theorem sound :
    ∀ m, compatible parent m → WeightedBound 7014 m ∨
      ∃ e ∈ residuals, compatible e.2 m :=
  partialSound 7014 parent tree parent_root parent_nohalt checked
theorem all_completions (m : Machine) (hm : compatible parent m) : WeightedBound 7014 m := by
  rcases sound m hm with hb | ⟨e,he,_⟩
  · exact hb
  · have hnil : residuals = [] := by simpa using residual_count
    simp [hnil] at he
#print axioms all_completions
#print axioms sound
#print axioms residual_count
""")
    print(stats, "FAR", len(certs), "unresolved", len(unresolved))

if __name__=="__main__":
    main()
