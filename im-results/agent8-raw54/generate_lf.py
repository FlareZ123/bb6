#!/usr/bin/env python3
"""Reproduce the Raw54 E1=0LE E0=1LF partial certificate.
The candidate ledger is not a proof; every accepted leaf passes the Lean checker.
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
PARENT = "1RB---_1RC---_0RD---_1LD0LE_1LF0LE_------"
BOUND = 7014
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]
HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LF
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""
def emit(name, imports, body):
    (ROOT/(name+".lean")).write_text("".join("import "+x+"\n" for x in imports)+HEADER+body+"\nend BB6.Agent8Raw54.LF\n")
def slot(s): return f"({s//2},{str(bool(s%2)).lower()})"
def move(a): return f"⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩"
def wrap(t):
    closed, code=t
    return ".closed ("+code+")" if closed else code
def witness_sections():
    out = {}
    for line in (ROOT/"lf-witnesses.txt").read_text().splitlines():
        if not line or line.startswith("#"): continue
        if line.startswith("["):
            key=line[1:-1]
            out[key]=[]
        else: out[key].append(line.split())
    return out

def main():
    certs, imports = {}, {}
    specs=witness_sections()
    with tempfile.TemporaryDirectory() as d:
        work=Path(d)
        for src,name in [(ROOT.parent/"agent47-raw112-cut"/"enumerate_fast.cpp","enumerate"),(ROOT.parent/"agent8-tnf-six"/"bank.cpp","bank"),(ROOT.parent/"agent47-raw111-cut"/"ngram_sparse.cpp","ngram")]:
            subprocess.run(["g++","-std=c++17","-O3",str(src),"-o",str(work/name)],check=True)
        subprocess.run([str(work/"enumerate"),PARENT],cwd=work,check=True)
        tree=json.loads((work/"tree.json").read_text())
        raw=(work/"open.txt").read_bytes()
        assert hashlib.sha256(raw).hexdigest()=="c9667bc82bd6a947c1195892924a16940a8f9e3cf1a8772f63ed0932b99a2ea8"
        rows=raw.decode().splitlines()
        assert len(rows)==len(set(rows))==1198
        out=subprocess.check_output([str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True)
        found=dict((int(i),v) for i,v in (line.split(":") for line in out.splitlines()))
        assert len(found)==1085
        misses=[row for j,row in enumerate(rows) if j not in found]
        assert hashlib.sha256(("\n".join(misses)+"\n").encode()).hexdigest()=="cc35f7e9a70453d6a17dfa3bbbab2cd909b0217df804b39c73d09c7f1e3d998a"
        far={rows[i]:v for i,v in found.items()}
        for i,code in specs["far"]:
            far[misses[int(i)]]=code
        for i,code,q,l,r,p,jump,entry,a,b in specs["sweep"]:
            i,jump,entry,a,b=map(int,(i,jump,entry,a,b))
            assert misses[i]==code
            l,r=(x if x!="-" else "" for x in (l,r))
            st=multi.C(q,l,r,p)
            tg=multi.C(q,l.replace("V",p*jump+"V"),r.replace("V",p*jump+"V"),p)
            source,time=multi.gen(i,multi.Machine(code),st,tg,entry,jump)
            assert time==(a,b),(i,time)
            ns=f"BB6.Agent8Raw54.LF.M{i}"
            name=f"Raw54LFSweep{i}"
            (ROOT/(name+".lean")).write_text(source.replace(f"BB6.Agent8Raw112MultiSweep.M{i}",ns))
            certs[code]=f".proven {ns}.table {ns}.never"
            imports[code]=name
        sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
        from emit_sparse import emit as emit_ngram
        for i,k,n,l,r in (map(int,row) for row in specs["ngram"]):
            result=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {misses[i]}\n",text=True).strip()
            ident,data=result.split(maxsplit=1)
            assert int(ident)==i
            mod,ns=emit_ngram(ROOT,i,misses[i],data,width=k,module_name=f"Raw54LFSparse{i}",expected=(n,l,r))
            certs[misses[i]]=f".proven {ns}.table {ns}.never"
            imports[misses[i]]=mod
        for i,mod,ns,*args in specs["proved"]:
            ns="BB6.Agent8Raw54."+ns
            suffix=(" "+" ".join(args)) if args else ""
            certs[misses[int(i)]]=f".proven ({ns}.table{suffix}) ({ns}.never{suffix})"
            imports[misses[int(i)]]=mod
    for row,code in far.items():
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,36) for c in code[1:]])
        certs[row]=f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    residual=[row for row in rows if row not in certs]
    assert len(residual)==11
    assert all(row.count("---")==1 for row in residual)
    (ROOT/"lf-unresolved.txt").write_text("".join(f"{misses.index(row)}:{row}\n" for row in residual))
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
        mod=f"Raw54LFKid{i:02}"
        mods.append(mod)
        p=f"refine parent {slot(s)} (some {move(MOVES[i])})"
        emit(mod,["Raw54LFBase",*sorted(deps(t))],f"""
def {name} : PartialAudit := {wrap(build(t))}
theorem {name}_checked : partialCheck {BOUND} ({p}) {name} = true := by
  rw [← BB6.Agent47Raw111.partialPrefix_eq]
  decide
""")
    checks="\n".join("  · exact kid%02d_checked"%(12*w+6*r+q) for q,w,r in product(range(6),range(2),range(2)))
    emit("Raw54LFCut",mods,f"""
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
    assert stats==Counter(split=1926,cycle=28735,last=14366,open=1198),stats
    print(stats,"FAR",len(far),"other witnesses",len(imports),"unresolved",len(residual))
if __name__=="__main__": main()
