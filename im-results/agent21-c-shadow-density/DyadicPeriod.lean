import DyadicAffine

namespace BB6.Agent21Dyadic

/-- A nonempty positive inverse word has an odd binary coefficient, so
    a simultaneous half-period shift of both normalized coordinates
    cancels modulo a full period. -/
theorem two_dvd_odd_coeff_shift (u v : Int) (w : List Nat)
    (hw : ∃ r t, w = r::t ∧ 0<r) :
    (2:Int) ∣ u+(u+2*v)*coeff w := by
  have hc : coeff w%2=1 := coeff_odd w hw
  apply Int.dvd_of_emod_eq_zero
  rw [Int.add_emod,Int.mul_emod,hc]
  have hp : (u+2*v)%2=u%2 := by omega
  rw [hp]
  omega

theorem period_slope_dvd (n : Nat) (u v : Int) (w : List Nat)
    (hw : ∃ r t, w = r::t ∧ 0<r) :
    P (n+1) ∣ -(P n*u)-P n*(u+2*v)*coeff w := by
  obtain ⟨k,hk⟩ := two_dvd_odd_coeff_shift u v w hw
  refine ⟨-k,?_⟩
  rw [P_add]
  change -(P n*u)-P n*(u+2*v)*coeff w=(P n*2)*(-k)
  have he : -(P n*u)-P n*(u+2*v)*coeff w =
      -(P n*(u+(u+2*v)*coeff w)) := by
    calc
      -(P n*u)-P n*(u+2*v)*coeff w =
          -(P n*u+P n*((u+2*v)*coeff w)) := by rw [Int.mul_assoc]; omega
      _ = -(P n*(u+(u+2*v)*coeff w)) := by rw [Int.mul_add]
  rw [he,hk]
  rw [Int.mul_assoc]
  simp only [Int.mul_neg]

/-- Exact all-precision translation invariance of nonempty inverse-word
    divisibility. A shift by 2^(n+1) in the original x/y coordinates
    changes the transformed mass by -2^(n+1)(u+2v) and the transformed
    normal coordinate by -2^n u. The resulting word numerator changes
    by a multiple of 2^(n+1), for *every* positive word. -/
theorem period_word_difference (s z u v : Int) (n : Nat) (w : List Nat)
    (hw : ∃ r t, w = r::t ∧ 0<r) :
    P (n+1) ∣
      (z-P n*u+acc (s-2*(P n*(u+2*v))) w)-(z+acc s w) := by
  let k : Int := P n*(u+2*v)
  have hd : (-(2*k))%2=0 := by omega
  have ht := acc_translate s (-(2*k)) w hd
  have hhalf : (-(2*k))/2=-k := by omega
  rw [hhalf] at ht
  have hs : s-2*(P n*(u+2*v))=s+(-(2*k)) := by dsimp [k]; omega
  rw [hs,ht]
  have he : (z-P n*u+(acc s w+ -k*coeff w))-(z+acc s w) =
      -(P n*u)-P n*(u+2*v)*coeff w := by
    dsimp [k]
    rw [Int.neg_mul]
    omega
  rw [he]
  exact period_slope_dvd n u v w hw

theorem period_word_iff (s z u v : Int) (n : Nat) (w : List Nat)
    (hw : ∃ r t, w = r::t ∧ 0<r) :
    (P (n+1) ∣ z-P n*u+acc (s-2*(P n*(u+2*v))) w) ↔
      (P (n+1) ∣ z+acc s w) := by
  let newer : Int := z-P n*u+acc (s-2*(P n*(u+2*v))) w
  let older : Int := z+acc s w
  change (P (n+1)∣newer) ↔ (P (n+1)∣older)
  have hd : P (n+1)∣newer-older := period_word_difference s z u v n w hw
  constructor
  · intro h
    have hs := Int.dvd_sub h hd
    have heq : newer-(newer-older)=older := by omega
    rw [heq] at hs
    exact hs
  · intro h
    have hs := Int.dvd_add hd h
    have heq : (newer-older)+older=newer := by omega
    rw [heq] at hs
    exact hs

#print axioms period_word_iff
end BB6.Agent21Dyadic
