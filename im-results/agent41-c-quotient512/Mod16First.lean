import Mod16OneTwo
namespace CCert

private theorem power_gap (n : Nat) :
    3*(n+1)+27 ≤ 2^(2*(n+1)+3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpow : 2^(2*(n+1+1)+3) = 4 * 2^(2*(n+1)+3) := by
      have e : 2*(n+1+1)+3 = (2*(n+1)+3)+2 := by omega
      rw [e, Nat.pow_add]
      omega
    rw [hpow]
    omega

theorem published_no_first_halt_m7_or_14 (m k : Nat)
    (hm : m%16=7 ∨ m%16=14)
    (hk : k+3*m+4=2^(2*m+3)) :
    ¬ BB6CLine.Reach (1,k,0) := by
  have hmpos : 0 < m := by omega
  have hpow : 16 ∣ 2^(2*m+3) := by
    obtain ⟨r,hr⟩ : ∃ r, 2*m+3 = 4+r := ⟨2*m-1, by omega⟩
    rw [hr,Nat.pow_add]
    change 16 ∣ 16*2^r
    exact ⟨2^r,rfl⟩
  have hmod : (k+3*m+4)%16=0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd hpow
  rcases hm with h7 | h14
  · have hlow : 23 ≤ k := by
      obtain ⟨n,hn⟩ : ∃ n, m=n+1 := ⟨m-1, by omega⟩
      have hgap : 3*m+27 ≤ 2^(2*m+3) := by
        simpa [hn] using power_gap n
      omega
    have hkmod : k%16=7 := by omega
    have hre : k=16*(k/16)+7 := by omega
    have hv : 0 < k/16 := by omega
    rw [hre]
    exact published_no_one_seven_except 0 (k/16) (Or.inr hv)
  · have hkmod : k%16=2 := by omega
    have hre : k=16*(k/16)+2 := by omega
    rw [hre]
    exact published_no_one_two 0 (k/16)

#print axioms published_no_first_halt_m7_or_14
end CCert
