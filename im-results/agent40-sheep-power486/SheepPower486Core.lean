import Std
namespace SheepPower486

theorem pow_mod_period (m period r k : Nat)
    (hm : 1 < m) (hp : 2^period % m = 1) :
    2^(r + period*k) % m = 2^r % m := by
  have hpow : (2^period)^k % m = 1 := by
    rw [Nat.pow_mod, hp]
    simp [Nat.mod_eq_of_lt hm]
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hpow]
  simp

theorem reduce_hit (m base shift cycle t : Nat)
    (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(486*cycle)%m=1) :
    (2^(base+486*t)+shift)%m = (2^(base+486*(t%cycle))+shift)%m := by
  have hk : t=t%cycle+cycle*(t/cycle) := by
    have hdiv := Nat.mod_add_div t cycle
    omega
  have heq : base+486*t = (base+486*(t%cycle))+(486*cycle)*(t/cycle) := by
    calc
      base+486*t = base+486*(t%cycle+cycle*(t/cycle)) := by rw [←hk]
      _ = _ := by simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
  have hpowers : 2^(base+486*t)%m = 2^(base+486*(t%cycle))%m := by
    rw [heq, pow_mod_period m (486*cycle) (base+486*(t%cycle)) (t/cycle) hm hp]
  simp only [Nat.add_mod, Nat.mod_mod, hpowers]

theorem no_generic (m base shift C cycle t v : Nat)
    (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(486*cycle)%m=1)
    (hc : ∀ x : Fin cycle, (2^(base+486*x.val)+shift)%m ≠ C%m)
    (heq : m*v+C=2^(base+486*t)+shift) : False := by
  have hh : (2^(base+486*(t%cycle))+shift)%m=C%m := by
    rw [←reduce_hit m base shift cycle t hm hq hp, ←heq]
    exact Nat.mul_add_mod_self_left _ _ _
  exact hc ⟨t%cycle, Nat.mod_lt t hq⟩ hh

theorem only_class (m base shift C cycle good t v : Nat)
    (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(486*cycle)%m=1)
    (hc : ∀ x : Fin cycle,
      (2^(base+486*x.val)+shift)%m=C%m → x.val=good)
    (heq : m*v+C=2^(base+486*t)+shift) :
    t%cycle=good := by
  have hh : (2^(base+486*(t%cycle))+shift)%m=C%m := by
    rw [←reduce_hit m base shift cycle t hm hq hp, ←heq]
    exact Nat.mul_add_mod_self_left _ _ _
  exact hc ⟨t%cycle, Nat.mod_lt t hq⟩ hh

#print axioms no_generic
#print axioms only_class
end SheepPower486
