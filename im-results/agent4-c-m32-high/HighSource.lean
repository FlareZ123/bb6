import M32HighSmall
import CSourceBridge32
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace BB6.Agent4M32

/-- One authenticated source theorem for every high stopping-family input
whose exact quotient class is absent from the B8/M32 forward closure.
The predicate is executable, and this covers all such classes without
manually instantiating a fixed list. -/
theorem high32_forbidden_source (j m k : Nat)
    (hj : 3 ≤ j) (hm : 2 ≤ m)
    (heq : k+j+3*m+5 = 2^(2*m+2)*(j+3))
    (habs : CCert.highPairGood (j%32) (m%32)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  have hsource : CCert.Reach (2*j+3,k,0) :=
    CCert.source_reachable_embeds32 h
  have hseen := CCert.reachable_seen hsource
  have hfalse := CCert.high_pair_absent_sound j m k hj hm heq habs
  rw [hfalse] at hseen
  cases hseen

/-- All abstractly absent high stopping-family parameter pairs.
This is a finite set of congruence selectors; no finite time limit is
assumed for the theorem high32_forbidden_source. -/
def high32Pairs : List (Nat × Nat) :=
  (List.range 32).flatMap fun j =>
    (List.range 32).filterMap fun m =>
      if decide (CCert.highPairGood j m) then some (j,m) else none

/-- Exact membership count within the original 32×32 quotient. -/
theorem high32Pairs_count : high32Pairs.length = 492 := by
  decide +kernel

/-- These 36 classes were omitted from the prior 24-pair explicit list.
Their source soundness follows from the same original kernel-checked graph,
without assuming a novel blank-root outcome. -/
def additional36 : List (Nat × Nat) :=
  [(0,23),(1,1),(1,26),(2,24),(3,28),(4,11),
   (5,30),(6,20),(7,0),(8,31),(9,2),(9,25),
   (10,16),(11,4),(12,19),(13,6),(14,12),(15,8),
   (16,7),(17,10),(17,17),(18,8),(19,12),(20,27),
   (21,14),(22,4),(23,16),(24,15),(25,9),
   (25,18),(26,0),(27,20),(28,3),(29,22),(30,28),(31,24)]

theorem additional36_length : additional36.length = 36 := by decide

theorem additional36_all_absent :
    additional36.all
      (fun p => decide (CCert.highPairGood p.1 p.2)) = true := by
  decide +kernel

theorem additional36_disjoint_existing24 :
    additional36.all
      (fun p => decide (p ∉ CCert.newHighPairs)) = true := by
  decide +kernel

/-- The original source machine cannot visit any of the newly listed
36 absent congruence pairs at a high halting gateway. The restriction
j>=3 permits j with residue 0, 1, or 2 modulo 32. -/
theorem additional36_source_unreachable (j m k : Nat)
    (hj : 3 ≤ j) (hm : 2 ≤ m)
    (heq : k+j+3*m+5 = 2^(2*m+2)*(j+3))
    (hmem : (j%32,m%32) ∈ additional36) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  have hgood : CCert.highPairGood (j%32) (m%32) :=
    of_decide_eq_true
      ((List.all_eq_true.mp additional36_all_absent) (j%32,m%32) hmem)
  exact high32_forbidden_source j m k hj hm heq hgood

#print axioms high32_forbidden_source
#print axioms high32Pairs_count
#print axioms additional36_source_unreachable

end BB6.Agent4M32
