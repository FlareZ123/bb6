import P1ConeNoOne1

namespace BB6.Agent28
open BB6.P1Reduction

theorem no_one_10 (t q : Nat) :
    ∀ k, ¬GAncestor (100352*t + 99456*q + 100324) (129024*t + 127872*q + 129003) k 1 := by
  apply ancestor_one_exclusion _ _ 5
  · change ((129024*t + 127872*q + 129003) + (100352*t + 99456*q + 100324)/2 + 3)%64=32
    omega
  · change 32 < (129024*t + 127872*q + 129003) + (100352*t + 99456*q + 100324)/2 + 3
    omega

theorem no_one_11 (t q : Nat) :
    ∀ k, ¬GAncestor (50176*t + 49728*q + 50156) (179200*t + 177600*q + 179169) k 1 := by
  apply ancestor_one_exclusion _ _ 1
  · change ((179200*t + 177600*q + 179169) + (50176*t + 49728*q + 50156)/2 + 3)%4=2
    omega
  · change 2 < (179200*t + 177600*q + 179169) + (50176*t + 49728*q + 50156)/2 + 3
    omega

theorem no_one_12 (t q : Nat) :
    ∀ k, ¬GAncestor (25088*t + 24864*q + 25072) (204288*t + 202464*q + 204251) k 1 := by
  apply ancestor_one_exclusion _ _ 1
  · change ((204288*t + 202464*q + 204251) + (25088*t + 24864*q + 25072)/2 + 3)%4=2
    omega
  · change 2 < (204288*t + 202464*q + 204251) + (25088*t + 24864*q + 25072)/2 + 3
    omega

theorem no_one_13 (t q : Nat) :
    ∀ k, ¬GAncestor (184576*t + 182928*q + 184528) (44800*t + 44400*q + 44793) k 1 := by
  apply ancestor_one_exclusion _ _ 2
  · change ((44800*t + 44400*q + 44793) + (184576*t + 182928*q + 184528)/2 + 3)%8=4
    omega
  · change 4 < (44800*t + 44400*q + 44793) + (184576*t + 182928*q + 184528)/2 + 3
    omega

theorem no_one_14 (t q : Nat) :
    ∀ k, ¬GAncestor (215040*t + 213120*q + 214992) (14336*t + 14208*q + 14335) k 1 := by
  apply ancestor_one_exclusion _ _ 1
  · change ((14336*t + 14208*q + 14335) + (215040*t + 213120*q + 214992)/2 + 3)%4=2
    omega
  · change 2 < (14336*t + 14208*q + 14335) + (215040*t + 213120*q + 214992)/2 + 3
    omega

end BB6.Agent28
