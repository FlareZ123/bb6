import SheepPower486High
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace SheepPower486

/-- Every sixth-stratum power is nontrivial modulo 3^7. -/
theorem target_mod2187_not_one (t : Nat) (ht : t%3≠0) :
    2^(486*t)%2187 ≠ 1 := by
  have htlt : t%3<3 := Nat.mod_lt t (by decide)
  have hp : 2^(486*3)%2187=1 := by rw [←Nat.powMod_def]; decide
  have hdiv : t=t%3+3*(t/3) := by
    have hh := Nat.mod_add_div t 3
    omega
  have heq : 486*t=486*(t%3)+(486*3)*(t/3) := by omega
  have hper := pow_mod_period 2187 (486*3) (486*(t%3)) (t/3) (by decide) hp
  rw [heq, hper]
  rcases (show t%3=1 ∨ t%3=2 from by omega) with h1|h2
  · rw [h1]
    rw [←Nat.powMod_def]
    decide
  · rw [h2]
    rw [←Nat.powMod_def]
    decide

/-- Any hidden odd block ending at this target has at most six steps. -/
theorem target_hidden_le6 (t h u : Nat) (ht : t%3≠0)
    (hy : 2^(486*t)=1+3^h*u) : h ≤ 6 := by
  by_cases hsmall : h ≤ 6
  · exact hsmall
  have hh : 7 ≤ h := by omega
  have hd : 2187 ∣ 3^h := by
    have hrepl : h=7+(h-7) := by omega
    rw [hrepl,Nat.pow_add]
    refine ⟨3^(h-7), ?_⟩
    simp [show (3:Nat)^7=2187 by decide]
  have hmul : (3^h*u)%2187=0 := by
    have h0 : 3^h%2187=0 := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.mul_mod,h0]
    simp
  have hy_mod : 2^(486*t)%2187=1 := by
    rw [hy,Nat.add_mod,hmul]
  exfalso
  exact target_mod2187_not_one t ht hy_mod

#print axioms target_mod2187_not_one
#print axioms target_hidden_le6
end SheepPower486
