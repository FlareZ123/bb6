import FirstForkThree

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

private theorem gap_four (n v : Nat) (hn:4≤n)
    (hl:2^n<2*v) (hu:4*v<3*2^n) :
    ¬ ∃ k, 6*2^k+1≤v ∧ v≤8*2^k-1 := by
  rintro ⟨k, hlo, hhi⟩
  by_cases hk:k+4≤n
  · have hpow:2^(k+4)≤2^n := Nat.pow_le_pow_right (by decide:0<(2:Nat)) hk
    have he:2^(k+4)=16*2^k := by rw [Nat.pow_add]; omega
    rw [he] at hpow
    omega
  · have hnk:n≤k+3 := by omega
    have hpow:2^n≤2^(k+3) := Nat.pow_le_pow_right (by decide:0<(2:Nat)) hnk
    have he:2^(k+3)=8*2^k := by rw [Nat.pow_add]; omega
    rw [he] at hpow
    omega

private theorem gap_five (n v:Nat) (hn:5≤n)
    (hl:2^n<4*v) (hu:8*v<3*2^n) :
    ¬ ∃ k, 6*2^k+1≤v ∧ v≤8*2^k-1 := by
  rintro ⟨k,hlo,hhi⟩
  by_cases hk:k+5≤n
  · have hpow:2^(k+5)≤2^n := Nat.pow_le_pow_right (by decide:0<(2:Nat)) hk
    have he:2^(k+5)=32*2^k := by rw [Nat.pow_add]; omega
    rw [he] at hpow
    omega
  · have hnk:n≤k+4 := by omega
    have hpow:2^n≤2^(k+4) := Nat.pow_le_pow_right (by decide:0<(2:Nat)) hnk
    have he:2^(k+4)=16*2^k := by rw [Nat.pow_add]; omega
    rw [he] at hpow
    omega

theorem near_top_no_odd_tfour (n u A:Nat) (hn:4≤n)
    (hclose:u+A=4*2^n) (htight:64*A+164≤13*2^n) :
    ¬ ∃ k d, (6*2^k+1≤16*d ∧ 16*d≤8*2^k-1) ∧
      2*u+5=243*d := by
  rintro ⟨k,d,hband,heq⟩
  have hp:16≤2^n := by
    have h:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hn
    omega
  have hmul : 243*(16*d)=128*2^n-32*A+80 := by
    omega
  have hl : 2^n<2*(16*d) := by omega
  have hu : 4*(16*d)<3*2^n := by omega
  exact gap_four n (16*d) hn hl hu ⟨k,hband⟩

theorem near_top_no_odd_tfive (n u A:Nat) (hn:5≤n)
    (hclose:u+A=4*2^n) (htight:64*A+164≤13*2^n) :
    ¬ ∃ k d, (6*2^k+1≤32*d ∧ 32*d≤8*2^k-1) ∧
      2*u+5=729*d := by
  rintro ⟨k,d,hband,heq⟩
  have hp:32≤2^n := by
    have h:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hn
    omega
  have hmul : 729*(32*d)=256*2^n-64*A+160 := by omega
  have hl:2^n<4*(32*d) := by omega
  have hu:8*(32*d)<3*2^n := by omega
  exact gap_five n (32*d) hn hl hu ⟨k,hband⟩

#print axioms near_top_no_odd_tfour
#print axioms near_top_no_odd_tfive
end CascadeFirstFork
