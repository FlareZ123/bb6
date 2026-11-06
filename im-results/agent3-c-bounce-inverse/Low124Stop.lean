import Low124Cone
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3

private theorem low_124_power_bound (m : Nat) (hm : 3≤m) :
    3*m+260 ≤ (2:Nat)^(2*m+3) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hsmall : m<3
      · have htwo : m=2 := by omega
        subst m
        decide
      · have hprev := ih (by omega)
        have hp : (2:Nat)^(2*(m+1)+3) = 4*2^(2*m+3) := by
          rw [show 2*(m+1)+3=(2*m+3)+2 by omega, Nat.pow_add]
          simp only [show (2:Nat)^2=4 by decide]
          omega
        rw [hp]
        have hpos : 0 < (2:Nat)^(2*m+3) := Nat.pow_pos (by decide)
        omega

theorem blank_no_low_m_zero_mod128 (m k : Nat)
    (hm : m%128=0) (hm128 : 128≤m)
    (hstop : k+3*m+4=2^(2*m+3)) : ¬ CReach 1 k := by
  have hpow : 128 ∣ (2:Nat)^(2*m+3) := by
    change 2^7 ∣ (2:Nat)^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hmod128 : (k+3*m+4)%128=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hlarge := low_124_power_bound m (by omega)
  exact blank_no_one_124_mod128 k (by omega) (by omega)

#print axioms blank_no_low_m_zero_mod128
end BB6.Agent3
