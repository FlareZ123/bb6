import Std
namespace SheepPower1296

theorem pow_mod_period (m period r k : Nat)
    (hm : 1 < m) (hp : 2^period % m = 1) :
    2^(r + period*k) % m = 2^r % m := by
  have hpow : (2^period)^k % m = 1 := by
    rw [Nat.pow_mod, hp]
    simp [Nat.mod_eq_of_lt hm]
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hpow]
  simp

theorem no_mod_class (m base shift C cycle : Nat)
    (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(340200*cycle)%m=1)
    (hc : ∀ t : Fin cycle,
      (2^(base+340200*t.val)+shift)%m ≠ C%m) :
    ∀ k : Nat, (2^(base+340200*k)+shift)%m ≠ C%m := by
  intro k
  have ht : k%cycle < cycle := Nat.mod_lt k hq
  have hk : k=k%cycle+cycle*(k/cycle) := by
    have hdiv := Nat.mod_add_div k cycle
    omega
  have heq : base+340200*k = (base+340200*(k%cycle)) + (340200*cycle)*(k/cycle) := by
    calc
      base+340200*k = base+340200*(k%cycle+cycle*(k/cycle)) := by rw [←hk]
      _ = _ := by simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
  have hpowers : 2^(base+340200*k)%m = 2^(base+340200*(k%cycle))%m := by
    rw [heq, pow_mod_period m (340200*cycle) (base+340200*(k%cycle)) (k/cycle) hm hp]
  have hmod : (2^(base+340200*k)+shift)%m = (2^(base+340200*(k%cycle))+shift)%m := by
    simp only [Nat.add_mod, Nat.mod_mod, hpowers]
  intro hbad
  exact hc ⟨k%cycle,ht⟩ (hmod.symm.trans hbad)

theorem no_generic_equation (m base shift C cycle k v : Nat)
    (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(340200*cycle)%m=1)
    (hc : ∀ t : Fin cycle, (2^(base+340200*t.val)+shift)%m ≠ C%m)
    (heq : m*v+C=2^(base+340200*k)+shift) : False := by
  have heqmod : (2^(base+340200*k)+shift)%m=C%m := by
    rw [←heq]
    exact Nat.mul_add_mod_self_left _ _ _
  exact (no_mod_class m base shift C cycle hm hq hp hc k) heqmod

#print axioms no_generic_equation
end SheepPower1296
