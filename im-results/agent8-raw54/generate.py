#!/usr/bin/env python3
"""Generate raw54 E1=0LE, E0=1LB symbolic Lean witnesses and a partial audit.

All discovery inputs are untrusted. Only source-checked theorems close a leaf.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import argparse, hashlib, json, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent8-tnf-raw117"))
import raw112_multisweep as multi
sys.path.insert(0, str(ROOT.parent / "agent31-three-hole-tnf"))
from generate_four_hole import masks, parse
PARENT = "1RB---_1RC---_0RD---_1LD0LE_1LB0LE_------"
BOUND = 7014
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]
HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""
def emit(name, imports, body):
    (ROOT/(name+".lean")).write_text("".join("import "+x+"\n" for x in imports)+HEADER+body+"\nend BB6.Agent8Raw54\n")
def slot(s): return f"({s//2},{str(bool(s%2)).lower()})"
def move(a): return f"⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩"
def wrap(t):
    closed, code=t
    return ".closed ("+code+")" if closed else code
def sweeps():
    certs, imports = {}, {}
    for line in (ROOT/"sweeps.txt").read_text().splitlines():
        i,code,q,l,r,p,jump,entry,a,b=line.split()
        i,jump,entry,a,b=map(int,(i,jump,entry,a,b))
        l,r=(x if x!="-" else "" for x in (l,r))
        st=multi.C(q,l,r,p)
        tg=multi.C(q,l.replace("V",p*jump+"V"),r.replace("V",p*jump+"V"),p)
        source,time=multi.gen(i,multi.Machine(code),st,tg,entry,jump)
        assert time==(a,b),(i,time)
        ns=f"BB6.Agent8Raw54.M{i}"
        name=f"Raw54Sweep{i}"
        (ROOT/(name+".lean")).write_text(source.replace(f"BB6.Agent8Raw112MultiSweep.M{i}",ns))
        certs[code]=f".proven {ns}.table {ns}.never"
        imports[code]=name
    return certs,imports

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--sweeps-only",action="store_true")
    a=ap.parse_args()
    certs,imports=sweeps()
    if a.sweeps_only:
        print("generated",len(certs),"sweep witnesses")
        return
    with tempfile.TemporaryDirectory() as d:
        work=Path(d)
        for src,name in [(ROOT.parent/"agent47-raw112-cut"/"enumerate_fast.cpp","enumerate"),(ROOT.parent/"agent8-tnf-six"/"bank.cpp","bank")]:
            subprocess.run(["g++","-std=c++17","-O3",str(src),"-o",str(work/name)],check=True)
        subprocess.run([str(work/"enumerate"),PARENT],cwd=work,check=True)
        tree=json.loads((work/"tree.json").read_text())
        raw=(work/"open.txt").read_bytes()
        assert hashlib.sha256(raw).hexdigest()=="e805fa023715eee0cda042eaf47d0fc56e7c2df9dc17045f642734e0c5648eaa"
        rows=raw.decode().splitlines()
        assert len(rows)==len(set(rows))==1146
        out=subprocess.check_output([str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True)
        found=dict((int(i),v) for i,v in (line.split(":") for line in out.splitlines()))
        assert len(found)==1058
        misses=[r for j,r in enumerate(rows) if j not in found]
        assert hashlib.sha256(("\n".join(misses)+"\n").encode()).hexdigest()=="de1d1a294812da53bd90779aae68624787f83b7c773c2e11365dbc135f0e9354"
        far={rows[i]:v for i,v in found.items()}
        for i,code in [(10,"10123224132"),(12,"10123224132"),(13,"10123224132"),(14,"10123224132"),(15,"10123224132"),(57,"00102334101"),(68,"00102334101")]:
            far[misses[i]]=code
        # Independently checked sparse n-gram and strong-induction witnesses.
        sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
        from emit_sparse import emit as emit_ngram
        subprocess.run(["g++","-O3","-std=c++17",str(ROOT.parent/"agent47-raw111-cut"/"ngram_sparse.cpp"),"-o",str(work/"ngram")],check=True)
        for i,k,n,l,r in [[30,16,1537,75,232],[43,16,3217,355,214],[45,8,644,18,62],[46,8,693,18,62],[47,8,693,18,62],[54,8,199,19,30],[55,16,436,40,59],[58,8,406,41,25],[60,8,593,40,34],[78,8,117,20,13],[79,12,239,33,40]]:
            result=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {misses[i]}\n",text=True).strip()
            ident,data=result.split(maxsplit=1)
            assert int(ident)==i
            mod,ns=emit_ngram(ROOT,i,misses[i],data,width=k,module_name=f"Raw54Sparse{i}",expected=(n,l,r))
            certs[misses[i]]=f".proven {ns}.table {ns}.never"
            imports[misses[i]]=mod
        # Pair of four-bit block counters, sharing the same closed orbit.
        for i,variant in [(2,"false"),(72,"true")]:
            ns="BB6.Agent8Raw54.Pair"
            certs[misses[i]]=f".proven ({ns}.table {variant}) ({ns}.never {variant})"
            imports[misses[i]]="Raw54Pair"
        for i in [38,39,40,42,56,61,67,69]:
            ns=f"BB6.Agent8Raw54.Rec{i}"
            certs[misses[i]]=f".proven {ns}.table {ns}.never"
            imports[misses[i]]=f"Raw54Rec{i}"
    for row,code in far.items():
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,36) for c in code[1:]])
        certs[row]=f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    residual=[row for row in rows if row not in certs]
    assert residual==[line.split(":")[1] for line in (ROOT/"unresolved.txt").read_text().splitlines()]
    stats=Counter()
    def build(t):
        tag,*v=t
        stats[tag]+=1
        if tag=="cycle":
            e,k,r,b=v
            return True,f".cycle {e} {k} {str(r).lower()} ({b})"
        if tag=="last":
            n,s=v
            return True,f".last {n} {slot(s)}"
        if tag=="open":
            return (True,certs[v[0]]) if v[0] in certs else (False,".unresolved")
        assert tag=="split"
        n,s,kids=v
        children=[build(k) for k in kids]
        if all(x[0] for x in children):
            return True,f".split {n} {slot(s)} (byMove [\n"+",\n".join(x[1] for x in children)+"])"
        return False,f".split {n} {slot(s)} (byPartialMove [\n"+",\n".join(map(wrap,children))+"])"
    def deps(t):
        if t[0]=="open": return {imports[t[1]]} if t[1] in imports else set()
        if t[0]=="split": return set().union(*(deps(k) for k in t[3]))
        return set()
    assert tree[0]=="split"
    _,n,s,kids=tree
    stats["split"]+=1
    mods=[]
    for i,t in enumerate(kids):
        name=f"kid{i:02}"
        mod=f"Raw54Kid{i:02}"
        mods.append(mod)
        p=f"refine parent {slot(s)} (some {move(MOVES[i])})"
        emit(mod,["Raw54Base",*sorted(deps(t))],f"""
def {name} : PartialAudit := {wrap(build(t))}
theorem {name}_checked : partialCheck {BOUND} ({p}) {name} = true := by
  rw [← BB6.Agent47Raw111.partialPrefix_eq]
  decide
""")
    checks="\n".join("  · exact kid%02d_checked"%(12*w+6*r+q) for q,w,r in product(range(6),range(2),range(2)))
    emit("Raw54Cut",mods,f"""
def rootKids : Move → PartialAudit := byPartialMove [{','.join(f'kid{i:02}' for i in range(24))}]
theorem rootKids_checked (mv : Move) : partialCheck {BOUND} (refine parent {slot(s)} (some mv)) (rootKids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{checks}
def tree : PartialAudit := .split {n} {slot(s)} rootKids
theorem checked : partialCheck {BOUND} parent tree = true := by
  change (zipQueryOK {BOUND} parent {n} {slot(s)} &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck {BOUND} (refine parent {slot(s)} (some mv)) (rootKids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ rootKids_checked⟩
def residuals := partialResiduals parent tree
theorem residual_count : residuals.length = {len(residual)} := by decide
theorem sound : ∀ m, compatible parent m → WeightedBound {BOUND} m ∨
    ∃ e ∈ residuals, compatible e.2 m :=
  partialSound {BOUND} parent tree parent_root parent_nohalt checked
#print axioms sound
#print axioms residual_count
""")
    assert stats==Counter(split=1515,cycle=25133,last=8567,open=1146),stats
    print(stats,"FAR",len(far),"sweeps",len(imports),"unresolved",len(residual))
if __name__=="__main__": main()
