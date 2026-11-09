import Std

namespace CascadeDirectFatalArithmetic

private theorem pow_two_ge_k_plus_two (k : Nat) (hk : 2 ≤ k) :
    k+2 ≤ 2^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 2 ≤ k
    · have hprev := ih h
      rw [Nat.pow_succ]
      omega
    · have hk1 : k=1 := by omega
      subst k
      decide

private theorem quotient_band_gap (k j q : Nat)
    (hlow : 2*2^k < q) (hhigh : q < 3*2^k)
    (hband : 6*2^j+1 ≤ q ∧ q ≤ 8*2^j-1) : False := by
  by_cases h : j+2≤k
  · have hp := Nat.pow_le_pow_right (by decide : 0<2) h
    have heq : 2^(j+2)=4*2^j := by
      rw [show j+2=(j+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
      omega
    rw [heq] at hp
    omega
  · have hj : k≤j+1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0<2) hj
    have heq : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]; omega
    rw [heq] at hp
    omega

/-- An odd source quotient cannot be in its exact dyadic band when its
    zero-valuation output is the fatal threshold at level >=2. -/
theorem fatal_no_odd_zero_valuation (k j f q : Nat)
    (hk : 2≤k)
    (hf : f+k+4=4*2^k)
    (hz : 3*q=2*f+5)
    (hband : 6*2^j+1≤q ∧ q≤8*2^j-1) : False := by
  have hpow := pow_two_ge_k_plus_two k hk
  have hlow : 2*2^k<q := by omega
  have hhigh : q<3*2^k := by omega
  exact quotient_band_gap k j q hlow hhigh hband

private theorem pow2_period18 (n : Nat) : 2^(n+18)%9=2^n%9 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow2_mod18 (n : Nat) : 2^n%9=2^(n%18)%9 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n<18
    · rw [Nat.mod_eq_of_lt hn]
    · have ht : n=(n-18)+18 := by omega
      have hm : n%18=(n-18)%18 := by omega
      calc
        2^n%9=2^((n-18)+18)%9 := congrArg (fun e : Nat => 2^e%9) ht
        _ = 2^(n-18)%9 := pow2_period18 (n-18)
        _ = 2^((n-18)%18)%9 := ih (n-18) (by omega)
        _ = 2^(n%18)%9 := by rw [hm]

/-- An odd source image at a dyadic fatal threshold with nine-divisible
    output offset requires exactly one of two level residues modulo 18. -/
theorem fatal_nine_sector (k f : Nat)
    (hf : f+k+4=4*2^k)
    (hdiv : (2*f+5)%9=0) :
    k%18=4 ∨ k%18=5 := by
  have heq : 8*2^k=(2*f+5)+(2*k+3) := by omega
  have hmod : (8*2^k)%9=(2*k+3)%9 := by
    rw [heq, Nat.add_mod, hdiv]
    simp
  have hpmod := pow2_mod18 k
  have hred : (8*2^(k%18))%9=(2*(k%18)+3)%9 := by
    have ha : (8*2^k)%9=(8*2^(k%18))%9 := by
      calc
        (8*2^k)%9 = (8%9 * (2^k%9))%9 := Nat.mul_mod 8 (2^k) 9
        _ = (8%9 * (2^(k%18)%9))%9 := by rw [hpmod]
        _ = (8*2^(k%18))%9 := (Nat.mul_mod 8 (2^(k%18)) 9).symm
    have hb : (2*k+3)%9=(2*(k%18)+3)%9 := by omega
    omega
  have htable : ∀ x : Fin 18,
      (8*2^x.val)%9=(2*x.val+3)%9 → (x.val=4 ∨ x.val=5) := by
    decide
  exact htable ⟨k%18, Nat.mod_lt k (by decide)⟩ hred

#print axioms fatal_no_odd_zero_valuation
#print axioms fatal_nine_sector

end CascadeDirectFatalArithmetic
