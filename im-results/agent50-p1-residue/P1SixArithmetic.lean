import Std
namespace BB6.Agent50P1

def s6 (k:Nat) : Nat := 7*2^(16*k+3)-(2*k+2)

private theorem big_pow (k:Nat) : 16*k+4 ≤ 2^(16*k+3) := by
  have h := Nat.lt_pow_self (n:=16*k+3) (a:=2) (by decide)
  omega

private theorem s6_add (k:Nat) : s6 k+2*k+2=7*2^(16*k+3) := by
  have h := big_pow k
  simp only [s6]
  omega

theorem s6_even (k:Nat) : s6 k%2=0 := by
  have h := s6_add k
  have hp : 2^(16*k+3)=2*2^(16*k+2) := by
    have he : 16*k+3=(16*k+2)+1 := by omega
    rw [he,Nat.pow_succ]
    omega
  rw [hp] at h
  omega

theorem s6_large (k:Nat) : 8≤s6 k := by
  have h := s6_add k
  have hb := big_pow k
  omega

theorem six_target (k:Nat) :
    14*2^(16*k+6)-2*(16*k+6)-16=16*s6 k+4 := by
  have hp : 2^(16*k+6)=8*2^(16*k+3) := by
    have he : 16*k+6=(16*k+3)+3 := by omega
    rw [he,Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  have hs := s6_add k
  rw [hp]
  omega

theorem six_sandwich (k:Nat) :
    14*2^(16*k+5) < 9*s6 k+6 ∧ 9*s6 k+6 < 14*2^(16*k+6) ∧
    14*2^(16*k+5) < 10*s6 k+8 ∧ 10*s6 k+8 < 14*2^(16*k+6) ∧
    14*2^(16*k+5) < 15*s6 k+10 ∧ 15*s6 k+10 < 14*2^(16*k+6) := by
  have hs := s6_add k
  have hb := big_pow k
  have h5 : 2^(16*k+5)=4*2^(16*k+3) := by
    have he : 16*k+5=(16*k+3)+2 := by omega
    rw [he,Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  have h6 : 2^(16*k+6)=8*2^(16*k+3) := by
    have he : 16*k+6=(16*k+3)+3 := by omega
    rw [he,Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  rw [h5,h6]
  omega

theorem six_no_power (k j : Nat) (a : Nat)
    (hl:14*2^(16*k+5)<a) (hu:a<14*2^(16*k+6)) :
    a≠14*2^j := by
  intro he
  by_cases hj : j<16*k+6
  · have hp : 2^j ≤ 2^(16*k+5) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hp : 2^(16*k+6) ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem six_no_power_9 (k j:Nat) : 9*s6 k+6≠14*2^j := by
  obtain ⟨h1,h2,_,_,_,_⟩ := six_sandwich k
  exact six_no_power k j _ h1 h2

theorem six_no_power_10 (k j:Nat) : 10*s6 k+8≠14*2^j := by
  obtain ⟨_,_,h1,h2,_,_⟩ := six_sandwich k
  exact six_no_power k j _ h1 h2

theorem six_no_power_15 (k j:Nat) : 15*s6 k+10≠14*2^j := by
  obtain ⟨_,_,_,_,h1,h2⟩ := six_sandwich k
  exact six_no_power k j _ h1 h2

#print axioms s6_even
#print axioms six_target
#print axioms six_no_power_9
#print axioms six_no_power_10
#print axioms six_no_power_15
end BB6.Agent50P1
