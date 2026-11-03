import SpaceNeedleLift
namespace SpaceNeedlePrime

private theorem exists_q_of_mod (D B A : Nat) (hBA : B ≤ A)
    (heq : A%D=B%D) : ∃ q, A=D*q+B := by
  have hdiv : B/D ≤ A/D := Nat.div_le_div_right hBA
  let q := A/D-B/D
  have hq : A/D=B/D+q := by dsimp [q]; omega
  have hA := Nat.mod_add_div A D
  have hB := Nat.mod_add_div B D
  rw [hq, Nat.mul_add, heq] at hA
  refine ⟨q,?_⟩
  omega

private theorem seed49_mod :
    (2:Nat)^5167997945245 % 1125899906842627 =
       1688849860263988 % 1125899906842627 := by
  have h : Nat.powMod 2 5167997945245 1125899906842627 =
      1688849860263988 % 1125899906842627 := by decide
  exact (Nat.powMod_def _ _ _).symm.trans h

private theorem period49_mod :
    (2:Nat)^6701783066148 % 1125899906842627 = 1 := by
  have h : Nat.powMod 2 6701783066148 1125899906842627 = 1 := by decide
  exact (Nat.powMod_def _ _ _).symm.trans h

private theorem small_le_big_pow (B K : Nat) (hB : B ≤ 2^60)
    (hK : 60 ≤ K) : B ≤ 2^K := by
  have h : (2:Nat)^60 ≤ 2^K := Nat.pow_le_pow_right (by omega) hK
  omega

private theorem seed49 (K : Nat) (hK : K = 5167997945245) : ∃ q,
    2^49*(2*q+3)+49+3*(q+1) = 2^K := by
  have hsize : 1688849860263988 ≤ (2:Nat)^K :=
    small_le_big_pow _ _ (by decide) (by omega)
  have hmod : (2:Nat)^K % 1125899906842627 =
    1688849860263988 % 1125899906842627 := by
    rw [hK]
    exact seed49_mod
  obtain ⟨q,hq⟩ := exists_q_of_mod 1125899906842627 1688849860263988
    (2^K) hsize hmod
  refine ⟨q,?_⟩
  apply (exponent_den_iff 49 q K).mpr
  have hden : den 49 = 1125899906842627 := by decide
  have hbias : bias 49 = 1688849860263988 := by decide
  rw [hden,hbias]
  exact hq

private theorem period49 (L : Nat) (hL : L = 6701783066148) : ∃ c,
    2^L = 1 + den 49*c := by
  have hsize : 1 ≤ (2:Nat)^L :=
    small_le_big_pow _ _ (by decide) (by omega)
  have hmod : (2:Nat)^L % 1125899906842627 = 1 := by
    rw [hL]
    exact period49_mod
  obtain ⟨c,hc⟩ := exists_q_of_mod 1125899906842627 1
    (2^L) hsize (by simpa using hmod)
  refine ⟨c,?_⟩
  have hden : den 49 = 1125899906842627 := by decide
  rw [hden]
  omega

theorem valuation49_unbounded_predecessors (n : Nat) :
    ∃ q, 2^49*(2*q+3)+49+3*(q+1) = 2^(5167997945245+6701783066148*n) := by
  obtain ⟨q,hq⟩ := seed49 5167997945245 rfl
  obtain ⟨c,hc⟩ := period49 6701783066148 rfl
  exact predecessor_period_lift 49 q 5167997945245 6701783066148 c n hq hc

#print axioms valuation49_unbounded_predecessors
end SpaceNeedlePrime
