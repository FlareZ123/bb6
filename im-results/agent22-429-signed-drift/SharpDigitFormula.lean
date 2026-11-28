import SharpExactConstruction

namespace SharpExactConstruction
open SharpPackingUniversal

/-- Exact base-four digit formula for the extremal capacity. -/
theorem exact_capacity_digit_formula (K : Nat) :
    3*(F ((K-1)/3)-F (K/4)) + digitSum4 ((K-1)/3) =
      4*(((K-1)/3)-(K/4)) + digitSum4 (K/4) := by
  have ha := digit_identity (K/4)
  have hb := digit_identity ((K-1)/3)
  have hfa : F (K/4)≤F ((K-1)/3) := by
    have h := maxEdges_weight_plus_F K
    omega
  have hab : K/4≤(K-1)/3 := by omega
  omega

#print axioms exact_capacity_digit_formula
end SharpExactConstruction
