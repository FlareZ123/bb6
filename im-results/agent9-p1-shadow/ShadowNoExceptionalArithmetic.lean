import Lean
namespace BB6.Shadow

/-- A small-cost q29-style P1 inverse hub has a large shifted
    original-right-coordinate, independent of the left/right split. -/
theorem mass_shifted_gt1024 (P b d m L : Nat)
 (hmass : b+d+2*m+2*L+3=56*P)
 (hm : m≤10) (hL : L≤473) (hP:65536≤P) :
  1024 < d+b/2+3 := by omega

/-- If an original inverse has c=1 and depth <=8, its shifted
    right coordinate is at most 1024. -/
theorem small_inverse_one (t s : Nat)
 (ht:t≤8) (hpower:s=2^t*(1+3)) : s≤1024 := by
  have hp : 2^t≤2^8 := Nat.pow_le_pow_right (by decide) ht
  have hp8:(2:Nat)^8=256 := by decide
  omega

#print axioms mass_shifted_gt1024
#print axioms small_inverse_one
end BB6.Shadow
