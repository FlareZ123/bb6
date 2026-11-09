import CThreeAltStop
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Three
open BB6.Agent46

/-- One simple diagonal condition replaces all four individually named
    infinite Machine C stopping parameter congruence cylinders. -/
theorem high_stop_odd_diagonal_mod32 (j m k time : Nat)
    (hm : 4≤m) (hj : j%2=1)
    (hdiag : m%32=(j+25)%32)
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  have hclass :
      (j%8=3 ∧ (j+3*m)%32=23) ∨
      (j%8=7 ∧ (j+3*m)%32=7) ∨
      (j%8=1 ∧ (j+3*m)%32=15) ∨
      (j%8=5 ∧ (j+3*m)%32=31) := by
    omega
  exact high_stop_four_lattices j m k time hm hclass hstop

/-- The converse arithmetic certificate: the formerly four-branch
    criterion is exactly the single odd-index / +25 diagonal class. -/
theorem four_classes_iff_diagonal (j m : Nat) :
    ((j%8=3 ∧ (j+3*m)%32=23) ∨
      (j%8=7 ∧ (j+3*m)%32=7) ∨
      (j%8=1 ∧ (j+3*m)%32=15) ∨
      (j%8=5 ∧ (j+3*m)%32=31)) ↔
      (j%2=1 ∧ m%32=(j+25)%32) := by
  omega

#print axioms four_classes_iff_diagonal
#print axioms high_stop_odd_diagonal_mod32
end BB6.Agent4Three
