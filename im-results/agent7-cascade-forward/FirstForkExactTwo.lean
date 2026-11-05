import FirstFork

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

private theorem pow_at_least_16 (n:Nat) (hn:4≤n) : 16 ≤ 2^n := by
  have hp:2^4≤2^n:=Nat.pow_le_pow_right (by decide) hn
  exact hp

private theorem two_n_le_pow (n:Nat) (hn:4≤n) : 2*n ≤ 2^n := by
  have h:∀ k:Nat, 2*(k+4)≤2^(k+4):=by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+4=k+4+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-4)+4:=by omega
  rw [he]
  exact h (n-4)

private theorem odd_band_scale_unique (v k j:Nat)
    (hb:6*2^k+1≤v ∧ v≤8*2^k-1)
    (hj:6*2^j+1≤v ∧ v≤8*2^j-1) : k=j := by
  by_cases heq:k=j
  · exact heq
  by_cases hlt:k<j
  · have hpow:2^(k+1)≤2^j:=Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
    have he:2^(k+1)=2*2^k:=by rw [Nat.pow_succ];omega
    rw [he] at hpow
    omega
  · have hpow:2^(j+1)≤2^k:=Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
    have he:2^(j+1)=2*2^j:=by rw [Nat.pow_succ];omega
    rw [he] at hpow
    omega

private theorem odd_tzero_in_dyadic_gap (n u:Nat) (hn:4≤n)
    (hl:3*2^n≤u) (hu:u≤4*2^n) :
    ¬ ∃ k d, (6*2^k+1≤d ∧ d≤8*2^k-1) ∧ 2*u+5=3*d := by
  rintro ⟨k,d,⟨hlo,hhi⟩,heq⟩
  have hp := pow_at_least_16 n hn
  have hdlo : 2*2^n < d := by omega
  have hdhi : d < 3*2^n := by omega
  by_cases hk : k+2≤n
  · have hpow:2^(k+2)≤2^n := Nat.pow_le_pow_right (by decide:0<(2:Nat)) hk
    have he:2^(k+2)=4*2^k := by rw [Nat.pow_add];omega
    rw [he] at hpow
    omega
  · have hnk : n≤k+1 := by omega
    have hpow:2^n≤2^(k+1) := Nat.pow_le_pow_right (by decide:0<(2:Nat)) hnk
    have he:2^(k+1)=2*2^k := by rw [Nat.pow_succ];omega
    rw [he] at hpow
    omega

/-
STAGED_EXACT_TWO
-/
end CascadeFirstFork
