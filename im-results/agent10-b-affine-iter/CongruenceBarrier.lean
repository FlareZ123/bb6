import OddIncrement

namespace BB6.Agent10IterBarrier

/-- Every nonzero modulus making G^n periodic on input residues divides seven. -/
theorem periodic_modulus_divides_seven (n m : Nat)
    (hn : 0<n) (hm : 0<m)
    (hperiod : ∀ z : Nat, F n (z+m)%m=F n z%m) : m ∣ 7 := by
  obtain ⟨k,rfl⟩ : ∃ k : Nat, n=k+1 := ⟨n-1, by omega⟩
  have hs : F k (m*2^k) = F k 0+3^k*m := by
    simpa [Nat.mul_comm] using F_shift k 0 m
  have hmod : (G (F k 0+3^k*m))%m=(G (F k 0))%m := by
    have hp := period_multiple (k+1) m hperiod 0 (2^k)
    simp only [Nat.zero_add, F] at hp
    rw [hs] at hp
    exact hp
  have hpodd : (3^k)%2=1 := by simp [Nat.pow_mod]
  have hparity : m%2=0 ∨ m%2=1 := by omega
  rcases hparity with heven | hodd
  · have hm2 : m=2*(m/2) := by omega
    have hp : 0<m/2 := by omega
    have hinc : G (F k 0+3^k*m) = G (F k 0)+3^(k+1)*(m/2) := by
      rw [hm2]
      have he : 3^k*(2*(m/2)) = 2*(3^k*(m/2)) := by ac_rfl
      rw [he,G_even_shift]
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hmodinc : (G (F k 0)+3^(k+1)*(m/2))%m=(G (F k 0))%m := by
      rw [←hinc]
      exact hmod
    have hdiv : m ∣ 3^(k+1)*(m/2) :=
      mod_same_add_divides _ m _ hmodinc
    have hdiv' : 2*(m/2) ∣ 3^(k+1)*(m/2) := by
      rwa [←hm2]
    have htwo : 2 ∣ 3^(k+1) :=
      (Nat.mul_dvd_mul_iff_right hp).mp hdiv'
    have hzero : (3^(k+1))%2=0 := Nat.mod_eq_zero_of_dvd htwo
    have hone : (3^(k+1))%2=1 := by simp [Nat.pow_mod]
    omega
  · have hdodd : (3^k*m)%2=1 := by
      rw [Nat.mul_mod,hpodd,hodd]
    have htwo : (2*G (F k 0+3^k*m))%m=(2*G (F k 0))%m := by
      calc
        (2*G (F k 0+3^k*m))%m =
          ((2%m)*(G (F k 0+3^k*m)%m))%m := Nat.mul_mod ..
        _ = ((2%m)*(G (F k 0)%m))%m := by rw [hmod]
        _ = (2*G (F k 0))%m := (Nat.mul_mod ..).symm
    have hbase : (2*G (F k 0)+3*(3^k*m))%m=(2*G (F k 0))%m := by
      have he : 3*(3^k*m)=m*(3*3^k) := by ac_rfl
      rw [he]
      exact Nat.add_mul_mod_self_left ..
    rcases G_odd_increment (F k 0) (3^k*m) hdodd with hinc | hinc
    · have hsame : ((2*G (F k 0)+3*(3^k*m))+7)%m =
          (2*G (F k 0)+3*(3^k*m))%m := by
        rw [←hinc]
        exact htwo.trans hbase.symm
      exact mod_same_add_divides _ m 7 hsame
    · have hsame : ((2*G (F k 0+3^k*m))+7)%m =
          (2*G (F k 0+3^k*m))%m := by
        rw [hinc]
        exact hbase.trans htwo.symm
      exact mod_same_add_divides _ m 7 hsame

#print axioms periodic_modulus_divides_seven
end BB6.Agent10IterBarrier
