"""Regenerate raw123 audit shards without searching for new certificates.
Every emitted candidate is checked by the existing source semantics.
The 40 n-gram/block leaves remain explicit residuals until separately checked.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import json, subprocess, tempfile, sys, argparse
ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT.parent/x) for x in ("agent31-three-hole-tnf","agent10-tnf-multipump")]
import generate_sweeps as one
from generate_four_hole import masks, move, slot
import generate_growth
from audit_shards import Node, build_module, emit, MOVES, B

PARENT=one.parse("1RB---_1RC---_0RD---_1LD1RE_---0RF_------")
def special():
    out={}
    for l in (ROOT/"special.txt").read_text().splitlines():
        if not l or l.startswith("#"):continue
        s,k,*a=l.split();assert len(s)==36 and s not in out
        out[s]=(k,list(map(int,a)))
    assert Counter(k for k,_ in out.values())=={"H":9,"N":19,"B":21}
    return out

def make_bank():
    bank=set()
    for n in ("spec.json","partial_spec.json"):
        data=json.loads((ROOT.parent/"agent7-raw110"/n).read_text())
        for v in data.values():bank.update(v["bank"])
    assert len(bank)>=164
    bank.update((ROOT/"extra_bank.txt").read_text().split())
    return sorted(bank,key=lambda x:(len(x),x))

def generate(children):
    spec=special()
    growth=generate_growth.generate()
    assert not(set(spec)&set(growth))
    stats=Counter();remaining=[];mods=[]
    with tempfile.TemporaryDirectory() as d:
        tmp=Path(d)
        for src,name in [(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp","enumerate"),(ROOT/"bank.cpp","bank")]:
            subprocess.run(["g++","-std=c++17","-O3",str(src),"-o",str(tmp/name)],check=True)
        (tmp/"bank.txt").write_text(" ".join(make_bank()))
        for i in sorted(children):
            p=PARENT[:11]+(MOVES[i],)
            subprocess.run([str(tmp/"enumerate"),one.show(p)],cwd=tmp,check=True)
            opens=(tmp/"open.txt").read_text().splitlines()
            index={s:j for j,s in enumerate(opens)}
            assert len(opens)==len(index)
            hits=subprocess.run([str(tmp/"bank"),str(tmp/"bank.txt")],
                input="\n".join(opens)+"\n" if opens else "",text=True,capture_output=True,check=True).stdout.splitlines()
            hitdict=dict((int(j),a) for j,a in map(str.split,hits))
            assert set(hitdict)==set(range(len(opens)))
            refs=set();remaining_i=[];counts=Counter()
            def build(n):
                tag,*v=n;stats[tag]+=1;counts[tag]+=1
                if tag=="cycle":
                    e,k,r,b=v
                    return Node(f".cycle {e} {k} {str(r).lower()} ({b})")
                if tag=="last":
                    t,s=v
                    return Node(f".last {t} {slot(s)}")
                if tag=="open":
                    s=v[0];flat=s.replace("_","")
                    j=index[s]
                    if flat in growth:
                        mod,ns=growth[flat];refs.add(mod)
                        return Node(f".proven {ns}.table {ns}.never")
                    if flat in spec:
                        kind,args=spec[flat]
                        assert flat.count("---")==1
                        if kind=="H":
                            q=one.parse(s).index("---")
                            return Node(f".last {args[0]} {slot(q)}")
                        remaining_i.append(s)
                        return Node(".unresolved",open_count=1)
                    a=hitdict[j];assert a!="-",(i,j,s)
                    n,D,L,R,z=masks(one.parse(s),int(a[0]),[int(c,36) for c in a[1:]])
                    return Node(f".far {str(bool(int(a[0]))).lower()} {n} ⟨0,{D},{L},{R},{z}⟩")
                assert tag=="split"; t,s,kids=v;assert len(kids)==24
                cs=[build(k) for k in kids]
                return Node(f".split {t} {slot(s)}",cs,1+sum(k.size for k in cs),sum(k.open_count for k in cs))
            tree=build(json.loads((tmp/"tree.json").read_text()))
            assert counts["open"]==len(opens) and tree.open_count==len(remaining_i)
            pexpr=f"(child123 {move(MOVES[i])})"
            name=f"partialKid{i:02}"; auditname=name if tree.open_count else f"auditKid{i:02}"
            mod=build_module(tree,pexpr,auditname,["Raw123Base",*sorted(refs)])
            wrapper=[] if tree.open_count else [
                f"def {name} : PartialAudit := .closed {auditname}",
                f"theorem {name}_checked : partialCheck {B} {pexpr} {name} = true := {auditname}_checked"]
            modname=f"Raw123Partial{i:02}";mods.append(modname)
            emit(modname,[mod],[*wrapper,
                f"theorem countPartial{i:02} : (partialResiduals {pexpr} {name}).length = {tree.open_count} := by decide",
                f"#print axioms {name}_checked",f"#print axioms countPartial{i:02}"])
            (ROOT/f"remaining{i:02}.txt").write_text("\n".join(remaining_i)+"\n")
            remaining+=remaining_i
            print(i,counts,"retained",tree.open_count,"nodes",tree.size,flush=True)
    print("totals",stats,"retained",len(remaining))
    if len(children)==24:
        assert set(x.replace("_","") for x in remaining)=={s for s,(k,_) in spec.items() if k!="H"}
        assert len(remaining)==40
        assert stats=={"cycle":306928,"last":68320,"open":11544,"split":16816},stats

def assemble():
    kids=[f"partialKid{i:02}" for i in range(24)]
    cases="\n".join(f"  · exact {kids[12*w+6*r+q]}_checked" for q,w,r in product(range(6),range(2),range(2)))
    emit("Raw123Cut",["Raw123Base",*[f"Raw123Partial{i:02}" for i in range(24)]],[
        "def kids123 : Move → PartialAudit := byPartialMove ["+",".join(kids)+"]",
        "theorem kids123_checked (mv : Move) : partialCheck 10000 (child123 mv) (kids123 mv) = true := by",
        "  rcases mv with ⟨w,r,q⟩",
        "  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega",
        "  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl",
        "  all_goals cases w <;> cases r",cases,
        "def residual123 := partialResiduals p123 (cut123 kids123)",
        "theorem residual123_count : residual123.length = 40 := by decide",
        "theorem raw123_sound : ∀ m, compatible p123 m → WeightedBound 10000 m ∨ ∃ e ∈ residual123, compatible e.2 m :=",
        "  cut123_sound kids123 kids123_checked",
        "#print axioms residual123_count","#print axioms raw123_sound"])

if __name__=="__main__":
    ap=argparse.ArgumentParser();ap.add_argument("children",nargs="*",type=int);ap.add_argument("--assemble-only",action="store_true")
    a=ap.parse_args()
    if a.assemble_only:assemble()
    else:generate(set(a.children) if a.children else set(range(24)))
