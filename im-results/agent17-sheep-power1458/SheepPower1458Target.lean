import SheepPower1458High
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SheepPower1458
theorem target_mod6561_not_one (t : Nat) (ht : t%3≠0) :
    2^(1458*t)%6561≠1 := by
  have hp : 2^(1458*3)%6561=1 := by rw [←Nat.powMod_def]; decide
  have hdiv : t=t%3+3*(t/3) := by
    have hh := Nat.mod_add_div t 3
    omega
  have heq : 1458*t=1458*(t%3)+(1458*3)*(t/3) := by omega
  have hper := pow_mod_period 6561 (1458*3) (1458*(t%3)) (t/3) (by decide) hp
  rw [heq,hper]
  rcases (show t%3=1 ∨ t%3=2 from by omega) with h1|h2
  · rw [h1]; rw [←Nat.powMod_def]; decide
  · rw [h2]; rw [←Nat.powMod_def]; decide

theorem target_hidden_le7 (t h u : Nat) (ht : t%3≠0)
    (hy : 2^(1458*t)=1+3^h*u) : h≤7 := by
  by_cases hsmall : h≤7
  · exact hsmall
  have hh : 8≤h := by omega
  have hd : 6561∣3^h := by
    have hrepl : h=8+(h-8) := by omega
    rw [hrepl,Nat.pow_add]
    refine ⟨3^(h-8), ?_⟩
    simp [show (3:Nat)^8=6561 by decide]
  have hmul : (3^h*u)%6561=0 := by
    have h0 : 3^h%6561=0 := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.mul_mod,h0]; simp
  have hy_mod : 2^(1458*t)%6561=1 := by rw [hy,Nat.add_mod,hmul]
  exfalso
  exact target_mod6561_not_one t ht hy_mod
#print axioms target_mod6561_not_one
#print axioms target_hidden_le7
end SheepPower1458
