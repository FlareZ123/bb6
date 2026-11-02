import BounceOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Research

private theorem two_pow_injective (n m : Nat) (h : 2^n = 2^m) : n=m := by
  by_cases hn : n<m
  · have hlt := Nat.pow_lt_pow_right (a:=2) (by decide) hn
    omega
  · by_cases hm : m<n
    · have hlt := Nat.pow_lt_pow_right (a:=2) (by decide) hm
      omega
    · omega

/-- At each fixed source bounce parameter k, a successful output target
    uniquely determines the input c; no two successful inputs can have
    the same final pair. -/
theorem bounce_fixed_k_injective (k c₁ c₂ x y : Nat)
    (h₁ : (bounce k c₁).2=some (x,y))
    (h₂ : (bounce k c₂).2=some (x,y)) : c₁=c₂ := by
  by_cases hk : k%2=1
  · obtain ⟨n,hy,hsum,hcost⟩ := (bounce_odd_image k c₁ x y hk).mp h₁
    obtain ⟨m,_,hsum2,hcost2⟩ := (bounce_odd_image k c₂ x y hk).mp h₂
    have hB : 0 < 2*k+6 := by omega
    have heq : 2^n = 2^m := Nat.mul_right_cancel hB (hsum.symm.trans hsum2)
    have hnm := two_pow_injective n m heq
    omega
  · have he : k%2=0 := by omega
    rcases (bounce_even_image k c₁ x y he).mp h₁ with
      ⟨hy,n,hsum,hcost⟩ | ⟨n,hy,hsum,hcost⟩
    · rcases (bounce_even_image k c₂ x y he).mp h₂ with
        ⟨_,m,hsum2,hcost2⟩ | ⟨m,hy2,_,_⟩
      · have hB : 0<2*k+8 := by omega
        have heq : 2^n = 2^m := Nat.mul_right_cancel hB (hsum.symm.trans hsum2)
        have hnm := two_pow_injective n m heq
        omega
      · omega
    · rcases (bounce_even_image k c₂ x y he).mp h₂ with
        ⟨hy2,_,_,_⟩ | ⟨m,_,hsum2,hcost2⟩
      · omega
      · have hB : 0<2*k+8 := by omega
        have heq : 2^n = 2^m := Nat.mul_right_cancel hB (hsum.symm.trans hsum2)
        have hnm := two_pow_injective n m heq
        omega

/-- Every successful bounce output obeys one universal parity relation:
    the output-counter sum and initial bounce parameter have opposite parity. -/
theorem bounce_output_odd_sum (k c x y : Nat)
    (h : (bounce k c).2=some (x,y)) : (x+y+k)%2=1 := by
  by_cases hk : k%2=1
  · obtain ⟨n,_,hsum,_⟩ := (bounce_odd_image k c x y hk).mp h
    have hdvd : 2 ∣ x+y := by
      rw [hsum]
      refine ⟨2^n*(k+3), ?_⟩
      calc
        2^n*(2*k+6) = 2^n*(2*(k+3)) := by congr 1
        _ = 2*(2^n*(k+3)) := by ac_rfl
    omega
  · have he : k%2=0 := by omega
    rcases (bounce_even_image k c x y he).mp h with
      ⟨hy,n,hsum,_⟩ | ⟨n,_,hsum,_⟩
    · have hdvd : 2 ∣ x+6 := by
        rw [hsum]
        refine ⟨2^n*(k+4), ?_⟩
        calc
          2^n*(2*k+8) = 2^n*(2*(k+4)) := by congr 1
          _ = 2*(2^n*(k+4)) := by ac_rfl
      omega
    · have hdvd : 2 ∣ x+y+1 := by
        rw [hsum]
        refine ⟨2^n*(k+4), ?_⟩
        calc
          2^n*(2*k+8) = 2^n*(2*(k+4)) := by congr 1
          _ = 2*(2^n*(k+4)) := by ac_rfl
      omega

#print axioms bounce_fixed_k_injective
#print axioms bounce_output_odd_sum
end BB6.Agent11Research
