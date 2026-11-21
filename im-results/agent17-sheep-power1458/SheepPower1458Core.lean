import Std
namespace SheepPower1458
theorem pow_mod_period (m period r k : Nat) (hm : 1 < m) (hp : 2^period % m = 1) :
    2^(r + period*k) % m = 2^r % m := by
  have hpow : (2^period)^k % m = 1 := by
    rw [Nat.pow_mod, hp]
    simp [Nat.mod_eq_of_lt hm]
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hpow]
  simp
theorem reduce_hit (m base shift cycle t : Nat) (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(1458*cycle)%m=1) :
    (2^(base+1458*t)+shift)%m = (2^(base+1458*(t%cycle))+shift)%m := by
  have hk : t=t%cycle+cycle*(t/cycle) := by
    have hdiv := Nat.mod_add_div t cycle
    omega
  have heq : base+1458*t = (base+1458*(t%cycle))+(1458*cycle)*(t/cycle) := by
    calc
      base+1458*t = base+1458*(t%cycle+cycle*(t/cycle)) := by rw [←hk]
      _ = _ := by simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
  have hpowers : 2^(base+1458*t)%m = 2^(base+1458*(t%cycle))%m := by
    rw [heq, pow_mod_period m (1458*cycle) (base+1458*(t%cycle)) (t/cycle) hm hp]
  simp only [Nat.add_mod, Nat.mod_mod, hpowers]
theorem no_generic (m base shift C cycle t v : Nat) (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(1458*cycle)%m=1)
    (hc : ∀ x : Fin cycle, (2^(base+1458*x.val)+shift)%m ≠ C%m)
    (heq : m*v+C=2^(base+1458*t)+shift) : False := by
  have hh : (2^(base+1458*(t%cycle))+shift)%m=C%m := by
    rw [←reduce_hit m base shift cycle t hm hq hp, ←heq]
    exact Nat.mul_add_mod_self_left _ _ _
  exact hc ⟨t%cycle, Nat.mod_lt t hq⟩ hh
theorem only_class (m base shift C cycle good t v : Nat) (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(1458*cycle)%m=1)
    (hc : ∀ x : Fin cycle, (2^(base+1458*x.val)+shift)%m=C%m → x.val=good)
    (heq : m*v+C=2^(base+1458*t)+shift) : t%cycle=good := by
  have hh : (2^(base+1458*(t%cycle))+shift)%m=C%m := by
    rw [←reduce_hit m base shift cycle t hm hq hp, ←heq]
    exact Nat.mul_add_mod_self_left _ _ _
  exact hc ⟨t%cycle, Nat.mod_lt t hq⟩ hh
/-- A progression-specific modular obstruction. Unlike `no_generic`, this
lemma needs only the one base residue of the progression: the exponent advances
by an arbitrary period P for which 2^P = 1 modulo m. -/
/-- A fixed-progression non-hit: one base residue and one exponent
period suffice to exclude the entire arithmetic progression. -/
theorem no_hit_fixed_period (m base target period k : Nat)
    (hm : 1 < m) (hp : 2^period % m = 1)
    (hc : 2^base % m ≠ target % m) :
    2^(base+period*k) % m ≠ target % m := by
  rw [pow_mod_period m period base k hm hp]
  exact hc

theorem no_generic_fixed_period (m base shift C period k v : Nat)
    (hm : 1 < m) (hp : 2^period % m = 1)
    (hc : (2^base + shift) % m ≠ C % m)
    (heq : m*v+C=2^(base+period*k)+shift) : False := by
  have hpow : 2^(base+period*k)%m = 2^base%m :=
    pow_mod_period m period base k hm hp
  have hhit : (2^(base+period*k)+shift)%m=C%m := by
    rw [←heq]
    exact Nat.mul_add_mod_self_left _ _ _
  have hhit' : (2^base+shift)%m=C%m := by
    simpa only [Nat.add_mod, Nat.mod_mod, hpow] using hhit
  exact hc hhit'

#print axioms no_hit_fixed_period
#print axioms no_generic_fixed_period

#print axioms no_generic
#print axioms only_class
end SheepPower1458
