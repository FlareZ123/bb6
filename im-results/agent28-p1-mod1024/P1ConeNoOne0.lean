import Agent28PowerMod

namespace BB6.Agent28
open BB6.P1Reduction

theorem no_one_0 (t q : Nat) :
    ∀ k, ¬GAncestor (229376*t + 227328*q + 229332) (0*t + 0*q + 3) k 1 := by
  apply ancestor_one_exclusion _ _ 4
  · change ((0*t + 0*q + 3) + (229376*t + 227328*q + 229332)/2 + 3)%32=16
    omega
  · change 16 < (0*t + 0*q + 3) + (229376*t + 227328*q + 229332)/2 + 3
    omega

theorem no_one_1 (t q : Nat) :
    ∀ k, ¬GAncestor (114688*t + 113664*q + 114660) (114688*t + 113664*q + 114673) k 1 := by
  apply ancestor_one_exclusion _ _ 1
  · change ((114688*t + 113664*q + 114673) + (114688*t + 113664*q + 114660)/2 + 3)%4=2
    omega
  · change 2 < (114688*t + 113664*q + 114673) + (114688*t + 113664*q + 114660)/2 + 3
    omega

theorem no_one_2 (t q : Nat) :
    ∀ k, ¬GAncestor (57344*t + 56832*q + 57324) (172032*t + 170496*q + 172007) k 1 := by
  apply ancestor_one_exclusion _ _ 5
  · change ((172032*t + 170496*q + 172007) + (57344*t + 56832*q + 57324)/2 + 3)%64=32
    omega
  · change 32 < (172032*t + 170496*q + 172007) + (57344*t + 56832*q + 57324)/2 + 3
    omega

theorem no_one_3 (t q : Nat) :
    ∀ k, ¬GAncestor (28672*t + 28416*q + 28656) (200704*t + 198912*q + 200673) k 1 := by
  apply ancestor_one_exclusion _ _ 2
  · change ((200704*t + 198912*q + 200673) + (28672*t + 28416*q + 28656)/2 + 3)%8=4
    omega
  · change 4 < (200704*t + 198912*q + 200673) + (28672*t + 28416*q + 28656)/2 + 3
    omega

theorem no_one_4 (t q : Nat) :
    ∀ k, ¬GAncestor (179200*t + 177600*q + 179156) (50176*t + 49728*q + 50169) k 1 := by
  apply ancestor_one_exclusion _ _ 1
  · change ((50176*t + 49728*q + 50169) + (179200*t + 177600*q + 179156)/2 + 3)%4=2
    omega
  · change 2 < (50176*t + 49728*q + 50169) + (179200*t + 177600*q + 179156)/2 + 3
    omega

end BB6.Agent28
