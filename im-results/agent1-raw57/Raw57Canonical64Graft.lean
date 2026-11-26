import Raw57Canonical64Membership
import Raw57ParentConsumer

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw57Canonical64FourWay

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier

/-- The local Raw57 parent can be closed from the accepted 1LA bound and
    four remaining sibling Covers. This is the route from local branch work
    into the retained Canonical64 representative. -/
theorem sound63_from_four (B : Nat) (hB : 6766859 ≤ B)
    (hLA : ∀ m, compatible (BB6.Agent1Raw57Parent.child ⟨true,false,0⟩) m →
      WeightedBound 832 m)
    (hLB : Cover (WeightedBound B) (BB6.Agent1Raw57Parent.child ⟨true,false,1⟩))
    (hLE : Cover (WeightedBound B) (BB6.Agent1Raw57Parent.child ⟨true,false,4⟩))
    (h0LF : Cover (WeightedBound B) (BB6.Agent1Raw57Parent.child ⟨false,false,5⟩))
    (h1LF : Cover (WeightedBound B) (BB6.Agent1Raw57Parent.child ⟨true,false,5⟩)) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ BB6.Agent1Raw57Canonical64.roster63,
          TNFQuotientCompatible e.2 m := by
  apply BB6.Agent1Raw57Canonical64.sound63 B hB
  exact BB6.Agent1Raw57Consumer.cover_at_target_from_four
    B (by omega) hLA hLB hLE h0LF h1LF

/-- If the four outstanding Raw57 sibling Covers and the 63 retained
    representative Covers hold at target B, the existing attaining witness
    gives ExactBB6 B. -/
theorem exact_at_target_from_four (B : Nat) (hB : 6766859 ≤ B)
    (hLA : ∀ m, compatible (BB6.Agent1Raw57Parent.child ⟨true,false,0⟩) m →
      WeightedBound 832 m)
    (hLB : Cover (WeightedBound B) (BB6.Agent1Raw57Parent.child ⟨true,false,1⟩))
    (hLE : Cover (WeightedBound B) (BB6.Agent1Raw57Parent.child ⟨true,false,4⟩))
    (h0LF : Cover (WeightedBound B) (BB6.Agent1Raw57Parent.child ⟨false,false,5⟩))
    (h1LF : Cover (WeightedBound B) (BB6.Agent1Raw57Parent.child ⟨true,false,5⟩))
    (hLeaves : ∀ e ∈ BB6.Agent1Raw57Canonical64.roster63,
      Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) (Nat.le_refl B)
    (sound63_from_four B hB hLA hLB hLE h0LF h1LF) hLeaves champ

#print axioms sound63_from_four
#print axioms exact_at_target_from_four

end BB6.Agent1Raw57Canonical64FourWay
