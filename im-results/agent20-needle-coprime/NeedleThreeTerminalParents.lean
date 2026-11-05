import NeedlePeriodTriple
import NeedleAffineParent
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace NeedleThreeTerminalParents
open NeedlePeriodTriple NeedleAffineParent

private theorem big_enough (t : Nat) :
    3145751 ≤ (2:Nat)^(exponent t) := by
  have hExp : 22 ≤ exponent t := by simp [exponent]; omega
  have hpow := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hExp
  have h22 : (2:Nat)^22=4194304 := by decide
  omega

theorem three_terminal_parents (t : Nat) :
    ∃ q0 q3 q20 : Nat,
      5*q0+6=(2:Nat)^(exponent t) ∧
      19*q3+30=(2:Nat)^(exponent t) ∧
      2097155*q20+3145751=(2:Nat)^(exponent t) ∧
      2*q0+1 ≠ 16*q3+22 ∧
      2*q0+1 ≠ 2097152*q20+3145726 ∧
      16*q3+22 ≠ 2097152*q20+3145726 := by
  let x := (2:Nat)^(exponent t)
  have hlarge : 3145751≤x := big_enough t
  obtain ⟨h5,h19,h2097155⟩ := all_bases t
  have hsmall : 6≤x := by omega
  have hmed : 30≤x := by omega
  obtain ⟨q0,hq0⟩ := affine_parent 5 1 x (by decide) hsmall h5
  obtain ⟨q3,hq3⟩ := affine_parent 19 11 x (by decide) hmed h19
  obtain ⟨q20,hq20⟩ := affine_parent 2097155 1048596 x
    (by decide) hlarge h2097155
  refine ⟨q0,q3,q20,?_,?_,?_,?_,?_,?_⟩
  all_goals omega

#print axioms three_terminal_parents
end NeedleThreeTerminalParents
