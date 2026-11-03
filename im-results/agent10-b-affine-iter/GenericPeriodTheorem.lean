import GenericPeriodHelpers
namespace BB6.GeneralParity

/-- A congruence factor for any positive generalized odd-affine parity iterate
    must have modulus dividing the odd correction coefficient. -/
theorem general_periodic_modulus_divides_c (a b c n m : Nat)
    (ha : a%2=1) (hb : b%2=0) (hc : c%2=1)
    (hn : 0<n) (hm : 0<m)
    (hp : ∀ z : Nat, Iter a b c n (z+m)%m=Iter a b c n z%m) : m ∣ c := by
  obtain ⟨k,rfl⟩ : ∃ k : Nat, n=k+1 := ⟨n-1, by omega⟩
  have hs : Iter a b c k (m*2^k) = Iter a b c k 0+a^k*m := by
    simpa [Nat.mul_comm] using iter_shift a b c k 0 m
  have hmod : (H a b c (Iter a b c k 0+a^k*m))%m =
      (H a b c (Iter a b c k 0))%m := by
    have h := period_multiple a b c (k+1) m hp 0 (2^k)
    simp only [Nat.zero_add, Iter] at h
    rw [hs] at h
    exact h
  have hapow : (a^k)%2=1 := by simp [Nat.pow_mod,ha]
  rcases (show m%2=0 ∨ m%2=1 by omega) with heven | hodd
  · have hm2 : m=2*(m/2) := by omega
    have hhalf : 0<m/2 := by omega
    have hinc : H a b c (Iter a b c k 0+a^k*m) =
        H a b c (Iter a b c k 0)+a^(k+1)*(m/2) := by
      rw [hm2]
      have he : a^k*(2*(m/2)) = 2*(a^k*(m/2)) := by ac_rfl
      rw [he,H_even_shift]
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hmodinc : (H a b c (Iter a b c k 0)+a^(k+1)*(m/2))%m =
        (H a b c (Iter a b c k 0))%m := by
      rw [←hinc]
      exact hmod
    have hdiv : m ∣ a^(k+1)*(m/2) := mod_same_add_divides _ m _ hmodinc
    have hdiv' : 2*(m/2) ∣ a^(k+1)*(m/2) := by rwa [←hm2]
    have htwo : 2 ∣ a^(k+1) := (Nat.mul_dvd_mul_iff_right hhalf).mp hdiv'
    have hzero : (a^(k+1))%2=0 := Nat.mod_eq_zero_of_dvd htwo
    have hone : (a^(k+1))%2=1 := by simp [Nat.pow_mod,ha]
    omega
  · have hdodd : (a^k*m)%2=1 := by rw [Nat.mul_mod,hapow,hodd]
    have htwo : (2*H a b c (Iter a b c k 0+a^k*m))%m =
        (2*H a b c (Iter a b c k 0))%m := by
      calc
        (2*H a b c (Iter a b c k 0+a^k*m))%m =
            ((2%m)*(H a b c (Iter a b c k 0+a^k*m)%m))%m := Nat.mul_mod ..
        _ = ((2%m)*(H a b c (Iter a b c k 0)%m))%m := by rw [hmod]
        _ = (2*H a b c (Iter a b c k 0))%m := (Nat.mul_mod ..).symm
    have hbase : (2*H a b c (Iter a b c k 0)+a*(a^k*m))%m =
        (2*H a b c (Iter a b c k 0))%m := by
      have he : a*(a^k*m)=m*(a*a^k) := by ac_rfl
      rw [he]
      exact Nat.add_mul_mod_self_left ..
    rcases H_odd_increment a b c (Iter a b c k 0) (a^k*m) ha hb hc hdodd with hinc | hinc
    · have hsame : ((2*H a b c (Iter a b c k 0)+a*(a^k*m))+c)%m =
          (2*H a b c (Iter a b c k 0)+a*(a^k*m))%m := by
        rw [←hinc]
        exact htwo.trans hbase.symm
      exact mod_same_add_divides _ m c hsame
    · have hsame : ((2*H a b c (Iter a b c k 0+a^k*m))+c)%m =
          (2*H a b c (Iter a b c k 0+a^k*m))%m := by
        rw [hinc]
        exact hbase.trans htwo.symm
      exact mod_same_add_divides _ m c hsame

#print axioms general_periodic_modulus_divides_c
end BB6.GeneralParity
