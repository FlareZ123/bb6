import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Raw56.LE17557RhoArithmetic

/-- The fixed zero-run map proposed for the first renormalization attempt.
    Residue 7 is represented as signed residue -1. -/
def rhoZero (z : Nat) : Nat :=
  16 * (z / 8) + if z % 8 = 7 then 15 else z % 8

/-- Outside residue 6, subtracting seven before `rhoZero` is the same as
    subtracting fifteen after it.  This is the regular B-triad arithmetic. -/
theorem rho_b_regular (ell : Nat) (h7 : 7 ≤ ell) (h6 : ell % 8 ≠ 6) :
    rhoZero (ell - 7) + 15 = rhoZero ell := by
  unfold rhoZero
  split <;> split <;> omega

/-- Residue 6 is the unique exceptional B class: the high runway loses only
    seven relative to `rhoZero (ell-7)`, producing the observed eight-cell
    defect. -/
theorem rho_b_exception (ell : Nat) (h7 : 7 ≤ ell) (h6 : ell % 8 = 6) :
    rhoZero (ell - 7) + 7 = rhoZero ell := by
  unfold rhoZero
  split <;> split <;> omega

/-- Outside residue 7, subtracting one commutes with `rhoZero`. -/
theorem rho_c_regular (ell : Nat) (h1 : 1 ≤ ell) (h7 : ell % 8 ≠ 7) :
    rhoZero (ell - 1) + 1 = rhoZero ell := by
  unfold rhoZero
  simp only [h7, ↓reduceIte]
  split <;> omega

/-- Residue 7 is the unique exceptional A-carry class: the difference is
    nine rather than one, exactly cancelling an incoming eight-cell defect. -/
theorem rho_c_exception (ell : Nat) (h1 : 1 ≤ ell) (h7 : ell % 8 = 7) :
    rhoZero (ell - 1) + 9 = rhoZero ell := by
  unfold rhoZero
  simp only [h7, ↓reduceIte]
  split <;> omega

/-- The normal-A left runway identity on the reachable second-block residue. -/
theorem rho_a_normal (b : Nat) (h6 : 6 ≤ b) (hr : b % 8 = 5) :
    rhoZero (b - 6) = 2 * b - 11 := by
  unfold rhoZero
  split <;> omega

/-- Exact characterization of the B obstruction. -/
theorem rho_b_identity_iff (ell : Nat) (h7 : 7 ≤ ell) :
    (rhoZero (ell - 7) + 15 = rhoZero ell) ↔ ell % 8 ≠ 6 := by
  unfold rhoZero
  split <;> split <;> omega

/-- Exact characterization of the A-carry obstruction. -/
theorem rho_c_identity_iff (ell : Nat) (h1 : 1 ≤ ell) :
    (rhoZero (ell - 1) + 1 = rhoZero ell) ↔ ell % 8 ≠ 7 := by
  unfold rhoZero
  split <;> split <;> omega

/-- Marking a finite zero-run is arithmetically meaningful from length seven
    onward: `rhoZero z - 8` remains nonnegative. -/
theorem rho_marked_positive (z : Nat) (h7 : 7 ≤ z) : 8 ≤ rhoZero z := by
  unfold rhoZero
  split <;> omega

#print axioms rho_b_regular
#print axioms rho_b_exception
#print axioms rho_c_regular
#print axioms rho_c_exception
#print axioms rho_a_normal
#print axioms rho_b_identity_iff
#print axioms rho_c_identity_iff
#print axioms rho_marked_positive

end BB6.Agent1Raw56.LE17557RhoArithmetic
