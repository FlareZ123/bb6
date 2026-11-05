import FirstForkExactTwo

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

private theorem power_min (n:Nat) (hn:4≤n) : 16≤2^n := by
  have hp : 2^4≤2^n := Nat.pow_le_pow_right (by decide) hn
  exact hp

theorem near_top_no_odd_ttwo (n u A:Nat) (hn:4≤n)
    (hclose:u+A=4*2^n) (hsize:8*A≤5*2^n) :
    ¬ ∃ k d, (6*2^k+1≤4*d ∧ 4*d≤8*2^k-1) ∧
      2*u+5=27*d := by
  rintro ⟨k,d,⟨hlo,hhi⟩,heq⟩
  have hp := power_min n hn
  have hlow : 2^n < 4*d := by omega
  have hhigh : 2*(4*d) < 3*2^n := by omega
  by_cases hkn:k+3≤n
  · have hpow:2^(k+3)≤2^n :=
      Nat.pow_le_pow_right (by decide:0<(2:Nat)) hkn
    have he : 2^(k+3)=8*2^k := by rw [Nat.pow_add];omega
    rw [he] at hpow
    omega
  · have hnk:n≤k+2:=by omega
    have hpow:2^n≤2^(k+2) :=
      Nat.pow_le_pow_right (by decide:0<(2:Nat)) hnk
    have he : 2^(k+2)=4*2^k := by rw [Nat.pow_add];omega
    rw [he] at hpow
    omega

#print axioms near_top_no_odd_ttwo
end CascadeFirstFork
