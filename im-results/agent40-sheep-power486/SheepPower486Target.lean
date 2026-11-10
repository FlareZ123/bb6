import SheepPower486High
namespace SheepPower486

/-- The target power is nontrivial modulo 3^7 in this exact stratum. -/
theorem target_mod2187_not_one (t : Nat) (ht : t%3≠0) :
    2^(486*t)%2187 ≠ 1 := by
  have htlt : t%3<3 := Nat.mod_lt t (by decide)
  have hp : 2^(486*3)%2187=1 := by decide
  have hdiv : t=t%3+3*(t/3) := by
    have hh := Nat.mod_add_div t 3
    omega
  have heq : 486*t=486*(t%3)+(486*3)*(t/3) := by omega
  have hper := pow_mod_period 2187 (486*3) (486*(t%3)) (t/3) (by decide) hp
  rw [heq, hper]
  rcases (show t%3=1 ∨ t%3=2 from by omega) with h1|h2
  · rw [h1]
    decide
  · rw [h2]
    decide

#print axioms target_mod2187_not_one
end SheepPower486
