import BounceHaltBasin
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

theorem haltLevel_closed (k n : Nat) :
    haltLevel k n + 3*n + 2*(k+4) = 2^(n+1)*(k+4)+5 := by
  induction n generalizing k with
  | zero =>
      simp [haltLevel]; omega
  | succ n ih =>
      have h := ih (2*k+4)
      change 2*k+5 + haltLevel (2*k+4) n + 3*(n+1) + 2*(k+4) =
        2^(n+1+1)*(k+4)+5
      have hp : 2^(n+1+1) = 2 * 2^(n+1) := by
        simp only [Nat.pow_succ]
        omega
      rw [hp]
      have hfactor : 2^(n+1) * (2*k+4+4) = (2*2^(n+1))*(k+4) := by
        simp only [show 2*k+4+4=2*(k+4) by omega]
        simp [Nat.mul_assoc, Nat.mul_left_comm]
      rw [hfactor] at h
      omega

#print axioms haltLevel_closed
end BB6.Agent46
