import BackGoal
import SecondMod96
namespace A7

/-- Exclude every genuine blank-origin Machine C second-family stopping
    parameter with (j,m)=(5,29) modulo 96. -/
theorem no_second_family_5_29 (j m k:Nat)
    (hj:j%96=5) (hm:m%96=29)
    (hEquation:k+j+3*m+5=2^(2*m+2)*(j+3))
    (hReach: BB6CLine.Reach (2*j+3,k,0)):False := by
  obtain ⟨ha,hk⟩ := A41.second_target_5_29_mod96 j m k hj hm hEquation
  exact all_target_congruences_unreachable (2*j+3) k ha hk hReach

#print axioms no_second_family_5_29
end A7
