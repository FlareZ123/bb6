import ValuationReturn

namespace Agent9Val

theorem adversarialIndex_ge20 (n : Nat) : 20 ≤ adversarialIndex (n+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 20 ≤ 9 * adversarialIndex (n+2) + 2
    omega

theorem adversarial_input_valid (c : Nat) :
    16 ≤ 3*adversarialIndex (c+5)+4 := by
  have h := adversarialIndex_ge20 (c+3)
  have he : c+5 = (c+3)+2 := by omega
  rw [he]
  omega

theorem adversarial_input_residue (c : Nat) :
    (3*adversarialIndex (c+5)+4)%3 = 1 := by
  omega

#print axioms adversarial_input_valid
#print axioms adversarial_input_residue

end Agent9Val
