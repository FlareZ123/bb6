"""Emit compositional checks for large canonical cut subtrees."""
from itertools import product
from generate import slot, move, MOVES

def checked_subtree(tree, tag, p, cut, B, emit_tree, complete=False):
    def size(t):
        return 0 if t is None else 1+sum(map(size,t[3])) if t[0]=="split" else 1
    if tree[0]!="split" or size(tree)<=350:
        return (f"def c{tag} : Cut := {emit_tree(tree)}\n"
                f"theorem ok{tag} : check {B} ({p}) {cut} c{tag} = true := by decide\n"
                + (f"theorem complete{tag} : closedCut {cut} c{tag} = true := by decide\n" if complete else ""))
    n,s,children=tree[1:]
    decl=""
    terms=[]
    for i,k in enumerate(children):
        if k is None:
            terms.append(".unresolved")
            continue
        assert i%6<=cut
        childtag=f"{tag}_{i:02}"
        q=f"refine ({p}) {slot(s)} (some {move(MOVES[i])})"
        decl+=checked_subtree(k,childtag,q,max(cut,i%6+1),B,emit_tree,complete)
        terms.append("c"+childtag)
    kname="children"+tag
    pdef=f"({p})"
    st=slot(s)
    cases="\n".join(f"  · exact ok{tag}_{12*w+6*r+q:02}"
                     for q,w,r in product(range(min(5,cut)+1),range(2),range(2)))
    hq=" ∨ ".join(f"q = {i}" for i in range(min(5,cut)+1))
    alt="|".join("rfl" for _ in range(min(5,cut)+1))
    result = decl+f"""def {kname} : Move → Cut := byCutMove [{','.join(terms)}]
def c{tag} : Cut := .split {n} {st} {kname}
theorem kids_ok{tag} (mv : Move) (hv : mv.next.val ≤ {cut}) :
    check {B} (refine {pdef} {st} (some mv)) (nextCut {cut} mv) ({kname} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  change q.val ≤ {cut} at hv
  have hq : {hq} := by omega
  rcases hq with {alt}
  all_goals cases w <;> cases r
{cases}
theorem ok{tag} : check {B} {pdef} {cut} c{tag} = true := by
  change (BB6.Agent10ZipAudit.zipQueryOK {B} {pdef} {n} {st} &&
    BB6.Agent31ThreeHole.allMoves (fun mv => if mv.next.val ≤ {cut} then
      check {B} (refine {pdef} {st} (some mv)) (nextCut {cut} mv) ({kname} mv) else true)) = true
  simp only [Bool.and_eq_true]
  refine ⟨by decide, BB6.Agent31ThreeHole.allMoves_of _ ?_⟩
  intro mv
  by_cases h : mv.next.val ≤ {cut}
  · simp [h,kids_ok{tag} mv h]
  · simp [h]
"""
    if complete:
        ccases = cases.replace("exact ok", "exact complete")
        result += f"""theorem children_complete{tag} (mv : Move) (hv : mv.next.val ≤ {cut}) :
    closedCut (nextCut {cut} mv) ({kname} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  change q.val ≤ {cut} at hv
  have hq : {hq} := by omega
  rcases hq with {alt}
  all_goals cases w <;> cases r
{ccases}
theorem complete{tag} : closedCut {cut} c{tag} = true := by
  simp only [c{tag},closedCut]
  apply BB6.Agent31ThreeHole.allMoves_of
  intro mv
  by_cases h : mv.next.val ≤ {cut}
  · simp [h,children_complete{tag} mv h]
  · simp [h]
"""
    return result
