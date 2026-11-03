import SpaceNeedleOdd
import SpaceNeedleVal49

namespace SpaceNeedlePrime

private theorem quotient_of_mod (D B A : Nat) (hBA : B ≤ A)
    (heq : A%D=B%D) : ∃ q, A=D*q+B := by
  have hdiv : B/D ≤ A/D := Nat.div_le_div_right hBA
  let q := A/D-B/D
  have hq : A/D=B/D+q := by dsimp [q]; omega
  have hA := Nat.mod_add_div A D
  have hB := Nat.mod_add_div B D
  rw [hq, Nat.mul_add, heq] at hA
  exact ⟨q, by omega⟩

private theorem certificate_family (v K L : Nat)
    (hsmall : bias v ≤ 2^(v+2))
    (hk : v+2 ≤ K)
    (hseed : Nat.powMod 2 K (den v) = bias v % den v)
    (hperiod : Nat.powMod 2 L (den v) = 1) :
    ∀n, admissibleExponent (K+L*n) := by
  have hlarge : bias v ≤ (2:Nat)^K :=
    Nat.le_trans hsmall (Nat.pow_le_pow_right (by omega) hk)
  have heq : (2:Nat)^K % den v = bias v % den v :=
    (Nat.powMod_def _ _ _).symm.trans hseed
  obtain ⟨q,hq⟩ := quotient_of_mod (den v) (bias v) (2^K) hlarge heq
  have hsize : 1 ≤ (2:Nat)^L := Nat.pow_pos (by omega)
  have hP : (2:Nat)^L % den v = 1 :=
    (Nat.powMod_def _ _ _).symm.trans hperiod
  obtain ⟨c,hc⟩ := quotient_of_mod (den v) 1 (2^L) hsize (by
    have hd : 1 < den v := by simp [den]
    rw [Nat.mod_eq_of_lt hd]
    exact hP)
  have hperi : 2^L = 1 + den v*c := by omega
  have hseed' := (exponent_den_iff v q K).mpr hq
  intro n
  obtain ⟨q',hq'⟩ := predecessor_period_lift v q K L c n hseed' hperi
  exact ⟨v,q',hq'⟩

private theorem family6 (n : Nat) : admissibleExponent (13+130*n) := by
  exact certificate_family 6 13 130 (by decide) (by decide) (by decide) (by decide) n

private theorem family11 (n : Nat) : admissibleExponent (3669+4098*n) := by
  exact certificate_family 11 3669 4098 (by decide) (by decide) (by decide) (by decide) n

private theorem family17 (n : Nat) : admissibleExponent (42089+262146*n) := by
  exact certificate_family 17 42089 262146 (by decide) (by decide) (by decide) (by decide) n

private theorem family49 (n : Nat) : admissibleExponent (5167997945245+6701783066148*n) := by
  obtain ⟨q,hq⟩ := valuation49_unbounded_predecessors n
  exact ⟨49,q,hq⟩

private def base (i : Fin 5) : Nat :=
  if i.val=0 then 4 else if i.val=1 then 13 else if i.val=2 then 3669 else
    if i.val=3 then 42089 else 5167997945245

private def stride (i : Fin 5) : Nat :=
  if i.val=0 then 4 else if i.val=1 then 130 else if i.val=2 then 4098 else
    if i.val=3 then 262146 else 6701783066148

private theorem family (i : Fin 5) (n : Nat) :
    admissibleExponent (base i + stride i*n) := by
  have hi : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 := by
    have hlt:=i.isLt
    omega
  rcases hi with h0 | h1 | h2 | h3 | h4
  · simpa [base,stride,h0,fourExponent] using four_admissible n
  · simpa [base,stride,h1] using family6 n
  · simpa [base,stride,h2] using family11 n
  · simpa [base,stride,h3] using family17 n
  · simpa [base,stride,h4] using family49 n

private theorem cover30 : ∀r : Fin 30,
    ∃ i : Fin 5, ∃ j : Fin 15, (base i+stride i*j.val)%30=r.val := by decide

private theorem stride30 : ∀i : Fin 5, (15*stride i)%30=0 := by decide
private theorem stride_pos : ∀i : Fin 5, 0<stride i := by decide

theorem every_residue_mod30_unbounded_predecessors (a bound : Nat) :
    ∃ k, bound ≤ k ∧ k%30=a%30 ∧ admissibleExponent k := by
  let r : Fin 30 := ⟨a%30,Nat.mod_lt _ (by decide)⟩
  obtain ⟨i,j,hij⟩ := cover30 r
  have hs := stride_pos i
  have hdvd : 30 ∣ 15*stride i := Nat.dvd_of_mod_eq_zero (stride30 i)
  obtain ⟨c,hc⟩ := hdvd
  let n := j.val + 15*(bound+1)
  let k := base i+stride i*n
  have hkeq : k=(base i+stride i*j.val)+30*(c*(bound+1)) := by
    dsimp [k,n]
    rw [Nat.mul_add]
    have he : stride i*(15*(bound+1))=(15*stride i)*(bound+1) := by ac_rfl
    rw [he, hc]
    simp only [Nat.mul_assoc, Nat.add_assoc]
  have hmod : k%30=a%30 := by
    rw [hkeq, Nat.add_mul_mod_self_left]
    exact hij
  have hb1 : bound+1 ≤ stride i*(bound+1) :=
    Nat.le_mul_of_pos_left (bound+1) hs
  have hb2 : stride i*(bound+1) ≤ 15*(stride i*(bound+1)) :=
    Nat.le_mul_of_pos_left _ (by decide)
  have hbound : bound ≤ k := by
    dsimp [k,n]
    rw [Nat.mul_add]
    have he : stride i*(15*(bound+1))=15*(stride i*(bound+1)) := by ac_rfl
    rw [he]
    omega
  exact ⟨k,hbound,hmod,family i n⟩

#print axioms every_residue_mod30_unbounded_predecessors
end SpaceNeedlePrime
