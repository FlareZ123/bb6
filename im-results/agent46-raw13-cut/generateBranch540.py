"""Reproduce the complete six-hole raw13 branch-540 certificate."""
import json
import sys
import subprocess
import tempfile
from pathlib import Path
from itertools import product
from collections import Counter
from generate import D, MOVES, boolean, move, slot, tally, emit as leaf_emit
from generateOneFAR import codes, fmt, saturate
from shard_cut import checked_subtree
from emitauto import emit_fixtures

BRANCH = sys.argv[1] if len(sys.argv)>1 else "540"
SPECS = {
    "540": ("1RB0RC1RC0LD1LA0LC------------------", 11, 7, Counter(cycle=51500,last=9303,split=2766,halt=2766,state=2284,far=509,auto=3)),
    "484": ("1RB0RB1RC0LC1LA0LD------------------", 12, 6, Counter(cycle=36067,last=7060,split=1934,halt=1934,state=1036,far=310,auto=2)),
}
ROOT, QUERY, QSLOT, EXPECTED = SPECS[BRANCH]
MODULE = "Agent46Raw13Branch" + BRANCH
NS = "BB6." + MODULE
AUTO = "BB6Coverage.Agent31Pump.Auto.Raw13Branch" + BRANCH
B = 7014
HEADER = f"set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {NS}\nopen BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut\n"

def write(name, imports, body):
    (D / (name + ".lean")).write_text("".join(f"import {x}\n" for x in imports) + HEADER + body + "\nend " + NS + "\n", encoding="utf-8")

def main():
    fixtures = json.loads((D / f"branch{BRANCH}-auto.json").read_text())
    # Fixtures already use the checked Lean constructor field order.
    emit_fixtures(fixtures, D / (MODULE + "Auto.lean"), "Raw13Branch"+BRANCH)
    auton = {x["table"]: i for i,x in enumerate(fixtures)}
    with tempfile.TemporaryDirectory() as temp:
        temp = Path(temp)
        exe = temp / "frontier_complete"
        subprocess.run(["g++","-O3","-std=c++17",str(D/"frontier_complete.cpp"),"-o",str(exe)],check=True)
        auto_tables = temp / "auto.txt"
        auto_tables.write_text("\n".join(auton) + "\n")
        tree = json.loads(subprocess.check_output([str(exe),str(D/"frontier-dfa-bank.txt"),str(D/f"branch{BRANCH}-far.txt"),str(auto_tables)],input=ROOT+" 4 6\n",text=True))
    assert tree[:3] == ["split",QUERY,QSLOT]
    count,mass=Counter(),Counter()
    tally(tree,6,4,count,mass)
    assert count == EXPECTED,count
    assert sum(mass.values())==25**6,mass
    print("counts",count,"mass",mass)
    def emit(t):
        if t is None:return ".unresolved"
        tag,*v=t
        if tag=="far":
            raw,rev,df=v
            dfa=list(map(int,df))
            a,b,z=saturate(codes(raw),dfa,rev)
            return f".closed (.far {boolean(rev)} {len(dfa)//2} ⟨0,{fmt(dfa)},{fmt(a)},{fmt(b)},{z}⟩)"
        if tag=="auto":
            i=auton[v[0]]
            return f".closed (.proven {AUTO}.p{i} {AUTO}.never{i})"
        if tag=="split":
            n,s,kids=v
            return f".split {n} {slot(s)} (byCutMove [\n"+",\n".join(map(emit,kids))+"])"
        return leaf_emit(t)
    mods=[]
    for i,k in enumerate(tree[3]):
        if k is None:continue
        tag=f"{i:02}"
        name=MODULE+"Kid"+tag
        mods.append(name)
        p=f"next {move(MOVES[i])}"
        decl=checked_subtree(k,tag,p,max(4,i%6+1),B,emit)
        write(name,[MODULE+"Base",MODULE+"Auto"],decl+f"\ndef kid{tag} : Cut := c{tag}\ntheorem checked{tag} : check {B} ({p}) (nextCut 4 {move(MOVES[i])}) kid{tag} = true := ok{tag}\n")
    terms=",".join(f"kid{i:02}" if tree[3][i] is not None else ".unresolved" for i in range(24))
    cases="\n".join(f"  · exact checked{12*w+6*r+q:02}" for q,w,r in product(range(5),range(2),range(2)))
    write(MODULE,mods,f"""
def kids : Move → Cut := byCutMove [{terms}]
theorem kids_checked (mv : Move) (hv : mv.next.val ≤ 4) :
    check {B} (next mv) (nextCut 4 mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  change q.val ≤ 4 at hv
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}

def parentCut : Cut := .split {QUERY} {slot(QSLOT)} kids

theorem parent_checked : check {B} parent 4 parentCut = true := by
  change (BB6.Agent10ZipAudit.zipQueryOK {B} parent {QUERY} {slot(QSLOT)} &&
    BB6.Agent31ThreeHole.allMoves (fun mv =>
      if mv.next.val ≤ 4 then check {B} (next mv) (nextCut 4 mv) (kids mv) else true)) = true
  simp only [Bool.and_eq_true]
  refine ⟨by decide, BB6.Agent31ThreeHole.allMoves_of _ ?_⟩
  intro mv
  by_cases h : mv.next.val ≤ 4
  · simp [h,kids_checked mv h]
  · simp [h]

theorem empty_complement : residuals parent 4 parentCut = [] := by decide

theorem bound (m : Machine) (hm : compatible parent m) : WeightedBound {B} m := by
  rcases sound {B} parent 4 parentCut (by decide) parent_support (by decide)
      parent_nohalt parent_checked m (compatible_quotient m hm) with hb | ⟨e,he,hq⟩
  · exact hb
  · rw [empty_complement] at he
    simp at he

#print axioms parent_checked
#print axioms empty_complement
#print axioms bound
""")
if __name__=="__main__":main()
