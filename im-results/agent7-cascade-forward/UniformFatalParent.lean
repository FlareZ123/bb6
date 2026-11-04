import FirstInverseComplete
import FastShield

namespace CascadeUniformFatal
open CascadeResetInverse CascadeManyShield

private theorem pow_lower (n : Nat) (hn : 2 ≤ n) : n+2 ≤ 2^n := by
  have h : ∀ m : Nat, m+4 ≤ 2^(m+2) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        rw [show m+1+2=(m+2)+1 by omega, Nat.pow_succ]
        omega
  have hh := h (n-2)
  have he : n-2+2 = n := by omega
  rw [he] at hh
  omega

/-- For every fatal source reset n>=4, the complete odd first-return
    inverse grammar cannot have valuation exponent t=0. Its candidate
    odd input would lie strictly between adjacent admissible dyadic bands. -/
theorem fatal_no_odd_tzero (n : Nat) (hn : 4 ≤ n) :
    ¬∃ k d : Nat,
      (6*2^k+1 ≤ d ∧ d ≤ 8*2^k-1) ∧
      2*fatal n+5 = 3*d := by
  rintro ⟨k,d,⟨hl,hu⟩,heq⟩
  have hp : n+2 ≤ 2^n := pow_lower n (by omega)
  have hf : 2*fatal n+5 + 2*n+3 = 8*2^n := by
    dsimp [fatal]
    omega
  have hdlo : 2*2^n < d := by omega
  have hdhi : d < 3*2^n := by omega
  by_cases hkn : k+2 ≤ n
  · have hmono : 2^(k+2) ≤ 2^n :=
      Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hkn
    have he : 2^(k+2) = 4*2^k := by
      rw [Nat.pow_add]
      omega
    rw [he] at hmono
    omega
  · have hnk : n ≤ k+1 := by omega
    have hmono : 2^n ≤ 2^(k+1) :=
      Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hnk
    have he : 2^(k+1) = 2*2^k := by
      rw [Nat.pow_succ]
      omega
    rw [he] at hmono
    omega

/-- Any even first-reset parent of fatal n>=4 uses exactly k=n-1 and
    has height 4*2^n-3*n-7, a closed affine dyadic formula. -/
theorem fatal_even_parent_unique (h n k : Nat) (hn : 4 ≤ n)
    (hband : 6*2^k-1 ≤ fatal n ∧ fatal n ≤ 8*2^k-3)
    (heq : 2*fatal n = 8*2^k+h+k) :
    k+1 = n ∧ h = 4*2^n-3*n-7 := by
  have hp : n+2 ≤ 2^n := pow_lower n (by omega)
  have hf : fatal n+n+4 = 4*2^n := by
    dsimp [fatal]
    omega
  have hlow : 2*2^n < fatal n := by omega
  have hhigh : fatal n < 6*2^n-1 := by omega
  have hkn : k+1 = n := by
    by_cases hl : k+2 ≤ n
    · have hmono : 2^(k+2) ≤ 2^n :=
        Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hl
      have he : 2^(k+2) = 4*2^k := by
        rw [Nat.pow_add]
        omega
      rw [he] at hmono
      omega
    · by_cases hr : n ≤ k
      · have hmono : 2^n ≤ 2^k :=
          Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hr
        omega
      · omega
  have hepow : 2^n = 2*2^k := by
    rw [←hkn, Nat.pow_succ]
    omega
  have hbig : 3*n+7 ≤ 4*2^n := by omega
  constructor
  · exact hkn
  · dsimp [fatal] at heq
    omega

/-- Strong all-index normal form specialized from the independently
    source-verified complete first-reset inverse theorem.
    Every fatal parent is the exact even predecessor above, or an odd
    predecessor with strictly positive 2-adic valuation exponent t. -/
theorem fatal_parent_normal_form (h n : Nat) (hn : 4 ≤ n)
    (hp : ResetParent h (fatal n)) :
    h = 4*2^n-3*n-7 ∨
    ∃ k t d, 1 ≤ t ∧ d%2=1 ∧
      (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
      2*fatal n+5=3^(t+1)*d ∧
      2*(2^t*d)=8*2^k+h+k+5 := by
  rcases hp with ⟨k,hband,heq⟩ | ⟨k,t,d,hodd,hband,heq,hq⟩
  · exact Or.inl ((fatal_even_parent_unique h n k hn hband heq).2)
  · have ht : 1 ≤ t := by
      by_cases hz : t = 0
      · subst t
        have he : 2*fatal n+5 = 3*d := by simpa using heq
        exact False.elim ((fatal_no_odd_tzero n hn) ⟨k,d,by simpa using hband,he⟩)
      · omega
    exact Or.inr ⟨k,t,d,ht,hodd,hband,heq,hq⟩

#print axioms fatal_no_odd_tzero
#print axioms fatal_even_parent_unique
#print axioms fatal_parent_normal_form
end CascadeUniformFatal
