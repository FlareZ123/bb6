import Raw40LocalCut
import Raw40FamilyFilterBase
import Raw40A0RDBase
import Raw40A1RBBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.FamilyRefine
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent19Raw40.FamilyFilter

def closed : List PartialMachine := [A0RD.p,A1RB.p]
def remaining := kept closed canonicalRemaining

theorem count : remaining.length = 170 := by decide

/-- Consume the two six-hole bounds, independently of their proof implementation. -/
theorem sound
    (hrd : ∀ m, TNFQuotientCompatible A0RD.p m → WeightedBound 1132 m)
    (hrb : ∀ m, TNFQuotientCompatible A1RB.p m → WeightedBound 1130 m) :
    ∀ m, TNFQuotientCompatible parent m → WeightedBound 7014 m ∨
      ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  apply filter_sound canonical_local_sound
  intro p hp m hm
  simp only [closed,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  · intro k d hk hd
    exact Nat.le_trans (hrd m hm k d hk hd) (by decide)
  · intro k d hk hd
    exact Nat.le_trans (hrb m hm k d hk hd) (by decide)

#print axioms count
#print axioms sound
end BB6.Agent19Raw40.FamilyRefine
