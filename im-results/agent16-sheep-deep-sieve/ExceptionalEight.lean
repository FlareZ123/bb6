import ExceptionalUniform
namespace SheepExceptional

/-! Kernel-verified uniform absence of every exceptional special parent for the
eight symbolic nodes of the six deepest new Sheep exponent classes. -/

theorem special_0 (j a : Nat) (hj : 426 ≤ j) :
    (2:Int)^(j+0)+(0:Int) ≠ 1*(3*(2:Int)^a+(a:Int)+3) := by
  exact uniform_special_parent_absent 1 (0:Int) 0 1 426
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) j hj a
#print axioms special_0

theorem special_1 (j a : Nat) (hj : 426 ≤ j) :
    (2:Int)^(j+1)+(1:Int) ≠ 3*(3*(2:Int)^a+(a:Int)+3) := by
  exact uniform_special_parent_absent 3 (1:Int) 1 2 426
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) j hj a
#print axioms special_1

theorem special_2 (j a : Nat) (hj : 426 ≤ j) :
    (2:Int)^(j+2)+(5:Int) ≠ 9*(3*(2:Int)^a+(a:Int)+3) := by
  exact uniform_special_parent_absent 9 (5:Int) 2 2 426
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) j hj a
#print axioms special_2

theorem special_3 (j a : Nat) (hj : 426 ≤ j) :
    (2:Int)^(j+3)+(-2:Int) ≠ 15*(3*(2:Int)^a+(a:Int)+3) := by
  exact uniform_special_parent_absent 15 (-2:Int) 3 2 426
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) j hj a
#print axioms special_3

theorem special_4 (j a : Nat) (hj : 426 ≤ j) :
    (2:Int)^(j+4)+(11:Int) ≠ 45*(3*(2:Int)^a+(a:Int)+3) := by
  exact uniform_special_parent_absent 45 (11:Int) 4 3 426
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) j hj a
#print axioms special_4

theorem special_5 (j a : Nat) (hj : 426 ≤ j) :
    (2:Int)^(j+5)+(67:Int) ≠ 135*(3*(2:Int)^a+(a:Int)+3) := by
  exact uniform_special_parent_absent 135 (67:Int) 5 3 426
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) j hj a
#print axioms special_5

theorem special_6 (j a : Nat) (hj : 426 ≤ j) :
    (2:Int)^(j+6)+(-46:Int) ≠ 225*(3*(2:Int)^a+(a:Int)+3) := by
  exact uniform_special_parent_absent 225 (-46:Int) 6 3 426
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) j hj a
#print axioms special_6

theorem special_7 (j a : Nat) (hj : 426 ≤ j) :
    (2:Int)^(j+7)+(133:Int) ≠ 675*(3*(2:Int)^a+(a:Int)+3) := by
  exact uniform_special_parent_absent 675 (133:Int) 7 3 426
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) j hj a
#print axioms special_7

end SheepExceptional
