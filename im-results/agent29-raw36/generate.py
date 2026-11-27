"""Reconstruct exact candidate trees and emit original Lean Audit checks."""
import argparse, json, subprocess, sys
from pathlib import Path
from itertools import product
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, refine, parse
sys.path.insert(0, str(ROOT.parent / "agent10-tnf-multipump"))
from chunk_checks import partition
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]
# E and F are fresh at this first hole. The F child is covered by the
# original-source state-renaming theorem from its E sibling, so no F
# audit tree need be regenerated or compiled.
REPRESENTATIVE_CHILDREN = tuple(i for i in range(24) if i % 6 != 5)
SPEC = json.loads((ROOT / "candidate.json").read_text())
HEADER = """import Raw36Cut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
"""
NODE = """
const {makeSearch}=require('./search.cjs');
const spec=require('./candidate.json');
const i=Number(process.argv[1]);
const s=makeSearch(spec.codes,spec.options);
const p=s.parse(spec.parent);p[spec.query[2]]=i;
const got=s.run(p,true);
const {tree,...stats}=got;
require('node:assert/strict').deepEqual({move:s.decode(i),...stats},spec.results[i]);
process.stdout.write(JSON.stringify(tree));
"""
def term(p,t):
    tag,*a=t
    if tag=="cycle":
        e,k,r,b=a
        return f".cycle {e} {k} {str(r).lower()} ({b})"
    if tag=="last":
        n,s=a
        return f".last {n} {slot(s)}"
    if tag=="far":
        code,=a
        rev,dfa=int(code[0]),list(map(int,code[1:]))
        d,D,L,R,z=masks(p,rev,dfa)
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    if tag=="split":
        n,s,kids=a
        assert len(kids)==24 and p[s]=="---"
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(term(refine(p,s,mv),kid) for mv,kid in zip(MOVES,kids))+"])"
    raise ValueError(t)
def generate(i,limit):
    tree=json.loads(subprocess.check_output(["node","-e",NODE,str(i)],cwd=ROOT))
    p=parse(SPEC["results"][i]["parent"])
    nm=f"kid{i:02d}"
    pexpr=f"(child {move(MOVES[i])})"
    body=HEADER+f"\ndef {nm} : Audit := {term(p,tree)}\n\ntheorem {nm}_checked : zipCheck 162 {pexpr} {nm} = true := by rfl\n"
    body,n=partition(body,limit)
    body+=f"""
theorem {nm}_bound : ∀ m, compatible {pexpr} m → WeightedBound 162 m :=
  (certifiedZip 162 {pexpr} {nm} (child_root {move(MOVES[i])}) (child_nohalt {move(MOVES[i])}) {nm}_checked).sound
#print axioms {nm}_bound
end BB6.Agent29Raw36
"""
    (ROOT/f"Raw36Kid{i:02d}.lean").write_text(body)
    print(f"Generated {nm}: {n} proof chunks",flush=True)
def assemble():
    out="import Raw36Symmetry\n" + "".join(f"import Raw36Kid{i:02d}\n" for i in REPRESENTATIVE_CHILDREN)+HEADER.split("\n",1)[1]
    out+="""
theorem children_bound (mv : Move) (m : Machine) (hm : compatible (child mv) m) : WeightedBound 162 m := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""
    for q,w,r in product(range(6),range(2),range(2)):
        if q == 5:
            i = 12*w + 6*r + 4
            out+=f"  · exact childF_bound 162 {str(bool(w)).lower()} {str(bool(r)).lower()} kid{i:02d}_bound m hm\n"
        else:
            out+=f"  · exact kid{12*w+6*r+q:02d}_bound m hm\n"
    out+="""
open BB6.Agent47PartialAudit
theorem branch_bound (m : Machine) (hm : compatible branch m) : WeightedBound 162 m := by
  let t : PartialAudit := .split 9 (2,true) (fun _ => .unresolved)
  have hc : partialCheck 162 branch t = true := by
    rw [partialCheck.eq_3, Bool.and_eq_true]
    exact ⟨by decide, allMoves_of _ (by intro mv; rfl)⟩
  rcases partialSound 162 branch t branch_root branch_nohalt hc m hm with h|⟨e,he,hh⟩
  · exact h
  · rw [partialResiduals.eq_3] at he
    obtain ⟨mv,_,hmem⟩ := List.mem_flatMap.mp he
    rw [partialResiduals.eq_1] at hmem
    obtain ⟨e',he',heq⟩ := List.mem_map.mp hmem
    have he'' : e' = ([], child mv) := by simpa only [List.mem_singleton] using he'
    rw [← heq,he''] at hh
    exact children_bound mv m hh
#print axioms branch_bound
end BB6.Agent29Raw36
"""
    (ROOT/"Raw36Branch.lean").write_text(out)
if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("children",nargs="*",type=int)
    ap.add_argument("--limit",type=int,default=300)
    args=ap.parse_args()
    selected=args.children or list(REPRESENTATIVE_CHILDREN)
    for i in selected:
        assert 0<=i<24
        generate(i,args.limit)
    if set(selected)==set(REPRESENTATIVE_CHILDREN): assemble()
