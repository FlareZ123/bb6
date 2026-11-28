import Lean
set_option maxHeartbeats 0
namespace BB6.Agent9AntiGenericBound

/-- Uniform logarithmic bound for the antiperiod determinant, independent
    of the modulus and anti-shift length. -/
theorem interior_energy_bound (h C a c w dir : Int) (K B : Nat)
    (hh : 0<h) (hC : 1≤c ∧ c≤C ∧ 1≤w ∧ w≤C)
    (ha : 0<a ∧ a<h) (hdir : dir=1∨dir= -1)
    (hscale : h*(C+(K:Int)+1)<(2:Int)^B) :
    -(2:Int)^B < h*(c-w)+dir*(K:Int)*a-dir*(K:Int)*h ∧
      h*(c-w)+dir*(K:Int)*a-dir*(K:Int)*h < (2:Int)^B := by
  have hdiff : -C≤c-w ∧ c-w≤C := by omega
  have hdiffL := Int.mul_le_mul_of_nonneg_left hdiff.1 (by omega : 0≤h)
  have hdiffR := Int.mul_le_mul_of_nonneg_left hdiff.2 (by omega : 0≤h)
  have hrem : -h≤a-h ∧ a-h≤0 := by omega
  have hremL := Int.mul_le_mul_of_nonneg_left hrem.1 (by omega : 0≤(K:Int))
  have hremR := Int.mul_le_mul_of_nonneg_left hrem.2 (by omega : 0≤(K:Int))
  have hcomm : h*(K:Int)=(K:Int)*h := by ac_rfl
  have hscale' : h*C+(K:Int)*h+h<(2:Int)^B := by
    rw [Int.mul_add,Int.mul_add] at hscale
    rw [hcomm] at hscale
    omega
  have hterm : dir*(K:Int)*a-dir*(K:Int)*h=dir*((K:Int)*(a-h)) := by
    simp only [Int.mul_sub,Int.mul_assoc]
  have hform : h*(c-w)+dir*(K:Int)*a-dir*(K:Int)*h = h*(c-w)+dir*((K:Int)*(a-h)) := by
    rw [←hterm]
    omega
  rw [hform]
  rcases hdir with hd|hd
  · rw [hd,Int.one_mul]
    have hneg : -(h*C)≤h*(c-w) := by rw [Int.mul_neg] at hdiffL; exact hdiffL
    have hrem0 : -((K:Int)*h)≤(K:Int)*(a-h) := by rw [Int.mul_neg] at hremL; exact hremL
    omega
  · rw [hd,Int.neg_one_mul]
    have hneg : -(h*C)≤h*(c-w) := by rw [Int.mul_neg] at hdiffL; exact hdiffL
    have hrem0 : -((K:Int)*h)≤(K:Int)*(a-h) := by rw [Int.mul_neg] at hremL; exact hremL
    omega

#print axioms interior_energy_bound
end BB6.Agent9AntiGenericBound
