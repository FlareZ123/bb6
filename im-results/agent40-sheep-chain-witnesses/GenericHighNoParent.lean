import SheepGenericHigh
import ResidueGap

namespace SheepGenericHigh

/-- The generic inverse equation is impossible whenever its odd residue lies
in the universal modular gap. No oddness premise on v is needed. -/
theorem no_large_generic_equation (D E a n v : Nat) (ha : 2 ≤ a)
    (hq : 1 < Q D E a ∧ Q D E a%2=1 ∧ Q D E a<2^a)
    (heq : D*(2^(a+1)+1)*v + 2*a*D + E = 2^n+3*D) : False := by
  have hs : (2*a-3)+3 = 2*a := by omega
  have hqid : Q D E a + 3*D = 2*a*D+E := by
    dsimp [Q]
    calc
      D*(2*a-3)+E +3*D = D*((2*a-3)+3)+E := by
        simp only [Nat.mul_add]
        omega
      _ = D*(2*a)+E := by rw [hs]
      _ = 2*a*D+E := by rw [Nat.mul_comm D (2*a)]
  have hmul : D*(2^(a+1)+1)*v=(2^(a+1)+1)*(D*v) := by ac_rfl
  have heqQ : (2^(a+1)+1)*(D*v)+Q D E a = 2^n := by
    rw [hmul] at heq
    omega
  have hqmod : Q D E a < 2^(a+1)+1 := by
    have hpow : 2^(a+1) = 2*2^a := by rw [Nat.pow_succ]; omega
    omega
  have hmod : 2^n%(2^(a+1)+1)=Q D E a := by
    rw [←heqQ]
    simp only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hqmod]
  exact SheepResidueGap.gap a n (Q D E a) hq.2.1 hq.1 hq.2.2 hmod

#print axioms no_large_generic_equation
end SheepGenericHigh
