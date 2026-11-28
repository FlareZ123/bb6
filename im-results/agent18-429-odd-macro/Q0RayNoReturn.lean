import Q0MacroCore

namespace BB429Q0Macro

/-- The authenticated q0 starting line p = 4*y + 6 is an entrance line
    for the strictly interior signed macro graph: no legal positive-cone
    macro transition lands on it. -/
theorem no_strict_macro_ray_predecessor (d : Digit) (p y : Nat)
    (hy : 0 < y) (hc : 3*y < p) (hd : num d p y % 16 = 0) :
    nextP d p ≠ 4 * nextY d p y + 6 := by
  intro hroot
  have hdiv := Nat.mod_add_div (num d p y) 16
  have heq : 16 * nextY d p y = num d p y := by
    unfold nextY
    omega
  cases d <;> simp [nextP, num, digit, cost, offset] at * <;> omega

#print axioms no_strict_macro_ray_predecessor

end BB429Q0Macro
