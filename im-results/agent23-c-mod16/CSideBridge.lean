import CSide
import CMod16Bridge
namespace BB6.Agent23

/-- Every strictly positive side gateway index divisible by sixteen is unreachable. -/
theorem source_side_positive_sixteen_unreachable (t : Nat) :
    ¬BB6CLine.Reach (0,64*t+64,384*t+407) := by
  intro hr
  exact side_positive_sixteen_unreachable t (reach_agree _ hr)

#print axioms source_side_positive_sixteen_unreachable
end BB6.Agent23
