/-- The 107 A_step2 accelerations preserve an arbitrary right suffix. -/
set_option maxHeartbeats 1000000 in
theorem reaches_108_cylinder_suffix (k : Nat) (ls : List Symbol) :
    A (3 ^ 108 * k + 1975700577069254261393123959451562008800234946348086) ls ⊢*
    A (3 ^ 1 * (8 ^ 107 * k) + 7488166283129708930486796847462680979065226437987146331898837006603604720521272903526417758309106)
      ([0, 1, 0, 1, 1, 0, 1, 1] ++ ls) := by
  apply stepStar_trans
  · nth_rw 1 [(by simp : k = 8 ^ 0 * k)]
    A_step2 13
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 17
    A_step2 21
    A_step2 5
    A_step2 27
    finish
  apply stepStar_trans
  · A_step2 35
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 31
    A_step2 21
    A_step2 5
    finish
  apply stepStar_trans
  · A_step2 5
    A_step2 21
    A_step2 5
    A_step2 17
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    finish
  apply stepStar_trans
  · A_step2 21
    A_step2 21
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    finish
  apply stepStar_trans
  · A_step2 5
    A_step2 31
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 21
    A_step2 21
    A_step2 5
    A_step2 5
    finish
  apply stepStar_trans
  · A_step2 21
    A_step2 5
    A_step2 27
    A_step2 39
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    finish
  apply stepStar_trans
  · A_step2 31
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 17
    A_step2 21
    A_step2 5
    A_step2 5
    finish
  apply stepStar_trans
  · A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 21
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    finish
  apply stepStar_trans
  · A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 31
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    finish
  apply stepStar_trans
  · A_step2 17
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 21
    A_step2 21
    finish
  apply stepStar_trans
  · A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    finish
