import Raw40LocalCut
import Raw40FamilyFilterBase
import Raw40A0RD
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.RDRefine
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent19Raw40.FamilyFilter

def remaining := kept [A0RD.p] canonicalRemaining

theorem count : remaining.length = 180 := by decide

theorem sound : ∀ m, TNFQuotientCompatible parent m → WeightedBound 7014 m ∨
      ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  apply filter_sound canonical_local_sound
  intro p hp m hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  subst p
  intro k d hk hd
  exact Nat.le_trans (A0RD.all_quotient m hm k d hk hd) (by decide)

#print axioms count
#print axioms sound
end BB6.Agent19Raw40.RDRefine
