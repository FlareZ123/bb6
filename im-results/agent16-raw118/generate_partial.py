"""Generate a source-checkable partial audit, retaining unproved leaves explicitly."""
from pathlib import Path
from itertools import product
import sys, json
from discover import discover, ROOT, IM
sys.path.insert(0,str(IM/"agent31-three-hole-tnf"))
from generate_four_hole import masks,parse
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
def move(a):return f"⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩"
def slot(s):return f"({s//2},{str(bool(s%2)).lower()})"
HEADER="""set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent16Raw118
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""
def emit(name,deps,body):
    (ROOT/(name+".lean")).write_text("".join("import "+x+"\n" for x in deps)+HEADER+body+"\nend BB6.Agent16Raw118\n")
def size(t):return 1+sum(map(size,t[3])) if t[0]=="split" else 1
CASES="""
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""
def main(work):
    rows,res=discover(work)
    t=json.loads((work/"tree.json").read_text())
    assert t[:3]==["split",9,8],t[:3]
    cert={}
    for i,a in res["far"].items():
        d,D,L,R,z=masks(parse(rows[i]),int(a[0]),[int(c,36) for c in a[1:]])
        cert[rows[i]]=f".far {str(a[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    # Avoid uncompressed kernel replay of long halter; retain it for graft.
    for i,(n,s) in res["late"].items():
        if n<=10000:cert[rows[i]]=f".last {n} {slot(s)}"
    def build(t):
        tag,*v=t
        if tag=="cycle":
            e,k,r,b=v
            return True,f".cycle {e} {k} {str(r).lower()} ({b})"
        if tag=="last":
            n,s=v;return True,f".last {n} {slot(s)}"
        if tag=="open":
            return (True,cert[v[0]]) if v[0] in cert else (False,".unresolved")
        n,s,kids=v;ks=[build(k) for k in kids]
        if all(c for c,_ in ks):
            return True,f".split {n} {slot(s)} (byMove [\n"+",\n".join(x for _,x in ks)+"])"
        return False,f".split {n} {slot(s)} (byPartialMove [\n"+",\n".join(wrap(x) for x in ks)+"])"
    def wrap(x):
        return ".closed ("+x[1]+")" if x[0] else x[1]
    def shard(t,p,path):
        name="Raw118Node"+path
        a="audit"+path
        if size(t)<=1200:
            emit(name,["Raw118Base"],f"""
def {a} : PartialAudit := {wrap(build(t))}
theorem {a}_checked : partialCheck bound ({p}) {a} = true := by
  rw [← BB6.Agent47Raw111.partialPrefix_eq]
  decide
""")
        else:
            assert t[0]=="split"
            _,n,s,kids=t
            parts=[shard(k,f"refine ({p}) {slot(s)} (some {move(MOVES[j])})",path+f"_{j:02}") for j,k in enumerate(kids)]
            cases="\n".join("  · exact "+parts[12*w+6*r+q][1]+"_checked" for q,w,r in product(range(6),range(2),range(2)))
            emit(name,[x[0] for x in parts],f"""
def {a}Kids : Move → PartialAudit := byPartialMove [{','.join(x[1] for x in parts)}]
theorem {a}Kids_checked (mv : Move) :
    partialCheck bound (refine ({p}) {slot(s)} (some mv)) ({a}Kids mv) = true := by
{CASES}{cases}
def {a} : PartialAudit := .split {n} {slot(s)} {a}Kids
theorem {a}_checked : partialCheck bound ({p}) {a} = true := by
  change (zipQueryOK bound ({p}) {n} {slot(s)} &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck bound
      (refine ({p}) {slot(s)} (some mv)) ({a}Kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ {a}Kids_checked⟩
""")
        return name,a
    name,a=shard(t,"parent","Root")
    count=len(rows)-len(cert)
    emit("Raw118Partial",[name],f"""
def residuals := partialResiduals parent {a}
theorem sound : ∀ m, compatible parent m → WeightedBound bound m ∨
    ∃ e ∈ residuals, compatible e.2 m :=
  partialSound bound parent {a} parent_root parent_nohalt {a}_checked
#print axioms sound
""")
    print("emitted candidate coverage; residual leaves",count)
if __name__=="__main__":main(Path(sys.argv[1]).resolve())
