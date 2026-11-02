import Std

namespace BB6.Agent5P1Affine

/-- A linear correction cannot escape a neighboring-power window when the
exponential scale dominates the linear parameter. -/
theorem affine_window (half top a b c u h : Nat)
    (ha : half + b + c < a) (hb : a < top) (hu : h+1 ≤ u) :
    half*u < a*u - (b*h+c) ∧
      a*u - (b*h+c) < top*u := by
  have hup : 0<u := by omega
  have hmul : (half+b+c)*u < a*u :=
    Nat.mul_lt_mul_of_pos_right ha hup
  have hba : b*h ≤ b*u := Nat.mul_le_mul_left b (by omega : h ≤ u)
  have hca : c ≤ c*u := by
    have hh : c*1 ≤ c*u := Nat.mul_le_mul_left c (by omega : 1≤u)
    simpa using hh
  have hsum : b*h+c ≤ (b+c)*u := by
    rw [Nat.add_mul]
    omega
  have hdistr : (half+b+c)*u = half*u + (b+c)*u := by
    simp [Nat.add_mul]
    omega
  rw [hdistr] at hmul
  have hlow : half*u + (b*h+c) < a*u := by omega
  have hhigh : a*u < top*u := Nat.mul_lt_mul_of_pos_right hb hup
  constructor
  · omega
  · omega

/-- Every integer strictly between consecutive 14-times-powers-of-two
is distinct from all members of that family. -/
theorem no_14_power_between (m x : Nat)
    (hl : 14*2^m < x) (hh : x < 14*2^(m+1)) (j : Nat) :
    x ≠ 14*2^j := by
  intro heq
  by_cases hj : j ≤ m
  · have hp := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) hj
    have hpm := Nat.mul_le_mul_left 14 hp
    omega
  · have hj' : m+1≤j := by omega
    have hp := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) hj'
    have hpm := Nat.mul_le_mul_left 14 hp
    omega

#print axioms affine_window
#print axioms no_14_power_between
end BB6.Agent5P1Affine
