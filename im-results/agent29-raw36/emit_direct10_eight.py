#!/usr/bin/env python3
"""Generate the literal D1=0RE 16-cycle / 8-live whole-parent Lean proof.

The 24 first-use child classifications come *only* from the archived
canonical 46122807180 source tree. Every emitted cycle is independently
kernel-checked; this script supplies no axioms or trusted result.
"""
import argparse,gzip,hashlib,json
from pathlib import Path
from collections import Counter

MOVES=[(w,d,q) for w in "01" for d in "LR" for q in "ABCDEF"]
BASE="1RB---_1RC---_0RD---_0LD0RE_------_------"
def mvlit(i):
    w,d,q=MOVES[i]
    return "⟨"+str(w=="1").lower()+","+str(d=="R").lower()+","+str(ord(q)-65)+"⟩"
def count_open(t):
    if t[0]=="open":return 1
    if t[0]=="split":return sum(count_open(c) for c in t[3])
    return 0
def fmtlist(xs):return "["+",".join(map(str,xs))+"]"
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--census",required=True,type=Path)
    p.add_argument("--source",required=True,type=Path)
    p.add_argument("--summary",required=True,type=Path)
    p.add_argument("--bound",type=int,default=2004)
    a=p.parse_args()
    census=json.loads(gzip.decompress(a.census.read_bytes()))
    assert census["parent"]==BASE
    assert census["cut"]==5
    assert census["stats"]["open"]==2638
    B=a.bound
    assert B>=2004
    root=census["tree"]
    assert root[0]=="split" and len(root[3])==24
    n,s,kids=root[1:4]
    assert s==8,(n,s)
    closed=[i for i,k in enumerate(kids) if count_open(k)==0]
    live=[i for i in range(24) if i not in closed]
    assert closed==[0,1,2,3,6,7,8,9,10,14,15,18,19,20,21,22],closed
    assert live==[4,5,11,12,13,16,17,23],live
    assert sum(count_open(k) for k in kids)==2638
    assert all(kids[i][0]=="cycle" and len(kids[i])==5 for i in closed)
    assert all(count_open(kids[i])>0 for i in live)

    out=[]
    out.append(f"""import Raw36ParentLive9
import CanonicalFastAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
D1=0RE first E/0 branching: 16 of 24 physical next transitions
have exact literal side-cycle proofs; exactly eight child Covers remain
unproved. The original census supplies only the *choice of candidate*
cycles. Lean independently checks all cycle terms and first-hole bounds.
-/

namespace BB6.Agent29Raw36D110Live8
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent29FastZipWeight BB6.Agent29CanonicalFast

def B : Nat := {B}
def parent : PartialMachine :=
  BB6.Agent29Raw36.d1Child ⟨false,true,4⟩
def hole : Slot := (4,false)
def child (i : Nat) : PartialMachine :=
  match i with
""")
    for i in range(24):
        out.append(f"  | {i} => refine parent hole (some {mvlit(i)})\n")
    out.append("  | _ => parent\n")
    out.append(f"def cycleCodes : List Nat := {fmtlist(closed)}\n")
    out.append(f"def liveCodes : List Nat := {fmtlist(live)}\n")
    out.append("""theorem parent_root :
    parent initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
    weightedTNFNoAssignedHalt_refine _ _ _ BB6.Agent29Raw36.parent_nohalt

theorem parent_query : fastQueryOK B parent """)
    out.append(f"{n} hole = true := by decide +kernel\n")
    out.append(f"""theorem haltChild :
    Cover (WeightedBound B) (refine parent hole none) := by
  obtain ⟨hread, hu, hw⟩ :=
    zipQueryOK_sound ((fastQueryOK_eq B parent {n} hole).symm.trans parent_query)
  cases h : knownRun parent {n} with
  | none => simp [h] at hread
  | some c =>
      have hs : readSlot c = hole := by simpa [h] using hread
      apply Cover.leaf
      intro m hm
      exact first_hole_weighted_halt B parent {n} c parent_root h
        (by simpa only [hs] using hu)
        (by simpa only [hs] using weightOK_sound parent hole {n} B hw)
        m (by simpa only [hs] using hm)

theorem ordinaryExact (mv : Move) :
    ∃ i ∈ List.range 24, refine parent hole (some mv) = child i := by
  have h : allMoves (fun v => (List.range 24).any
      (fun i => tableOK (refine parent hole (some v)) (child i))) = true := by
    decide +kernel
  obtain ⟨i, hi, he⟩ := List.any_eq_true.mp (allMoves_sound _ h mv)
  exact ⟨i, hi, tableOK_sound _ _ he⟩

theorem liveComplete (i : Nat) (hi : i ∈ List.range 24)
    (hc : i ∉ cycleCodes) : i ∈ liveCodes := by
  have h : (List.range 24).all
      (fun j => decide (j ∈ cycleCodes ∨ j ∈ liveCodes)) = true := by
    decide
  exact (of_decide_eq_true (List.all_eq_true.mp h i hi)).resolve_left hc

theorem cycleCover (i : Nat) (hi : i ∈ cycleCodes) :
    Cover (WeightedBound B) (child i) := by
  simp only [cycleCodes,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with {" | ".join("rfl" for _ in closed)}
""")
    for i in closed:
        _,e,k,right,b=kids[i]
        mv=mvlit(i)
        cyc=f"(.cycle {e} {k} {str(right).lower()} ({b}))"
        out.append(f"""  · exact (certifiedFast B (child {i}) {cyc}
      (by decide)
      (by
        change weightedTNFNoAssignedHalt (refine parent hole (some {mv}))
        exact weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt)
      (by decide +kernel)).toCover
""")
    out.append("""theorem parent_cover_from_live8
    (h : ∀ i ∈ liveCodes, Cover (WeightedBound B) (child i)) :
    Cover (WeightedBound B) parent := by
  apply Cover.branch parent hole (by decide)
  intro t ht
  cases t with
  | none => exact haltChild
  | some mv =>
      obtain ⟨i, hi, he⟩ := ordinaryExact mv
      rw [he]
      by_cases hc : i ∈ cycleCodes
      · exact cycleCover i hc
      · exact h i (liveComplete i hi hc)

theorem live_count : liveCodes.length = 8 := by decide
#print axioms parent_root
#print axioms parent_nohalt
#print axioms parent_query
#print axioms haltChild
#print axioms ordinaryExact
#print axioms liveComplete
#print axioms cycleCover
#print axioms parent_cover_from_live8
#print axioms live_count
end BB6.Agent29Raw36D110Live8
""")
    source="".join(out)
    a.source.parent.mkdir(parents=True,exist_ok=True)
    a.source.write_text(source)
    raw=a.census.read_bytes()
    receipt={
      "parent":BASE,
      "candidate_source_census_sha256":hashlib.sha256(raw).hexdigest(),
      "cycle_indices":closed,
      "live_indices":live,
      "live_transition_moves":["".join(MOVES[i]) for i in live],
      "bound_weighted":B,
      "root_query_step":n,
      "root_query_slot":s,
      "source_sha256":hashlib.sha256(source.encode()).hexdigest(),
      "source_path":a.source.name,
      "status":"candidate Lean source emitted, not checked"}
    a.summary.write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print("CANDIDATE: D1=0RE",len(closed),"exact source cycle children;",
          len(live),"Cover premises",flush=True)

if __name__=="__main__":main()
