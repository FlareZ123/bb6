import Std
namespace SheepHBound

/-- A nonzero power residue bounds the odd run parameter h for an arbitrary
target satisfying d*y+c=2^n. This is source-independent. -/
theorem h_bounded (y d c n H h u : Nat)
    (hy : d*y+c=2^n)
    (hf : y=1+3^h*u)
    (hbad : 2^n%(d*3^H) ≠ (d+c)%(d*3^H)) : h<H := by
  by_cases hgood : h<H
  · exact hgood
  have hh : H≤h := by omega
  obtain ⟨t,ht⟩ : ∃ t, h=H+t := ⟨h-H, by omega⟩
  have hpow : 3^h=3^H*3^t := by rw [ht,Nat.pow_add]
  have heq : 2^n=d+c+(d*3^H)*(3^t*u) := by
    rw [←hy,hf,hpow]
    simp [Nat.mul_add, Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have hmod : 2^n%(d*3^H) = (d+c)%(d*3^H) := by
    rw [heq]
    exact Nat.add_mul_mod_self_left _ _ _
  exact False.elim (hbad hmod)

#print axioms h_bounded
end SheepHBound
