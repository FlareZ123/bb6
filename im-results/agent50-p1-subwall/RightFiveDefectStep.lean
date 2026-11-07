import Lean

namespace BB6.Agent50Defect

/-- The shifted 12*2^n fixed-point defect remains strictly positive under
every source-shaped inverseAt transition of depth at least two. Assumptions
are the exact source inverse-power, inverse-mass and total-mass equations. -/
theorem high_depth_preserves_above_twelve
    (n b d m t k c : Nat) (hn : 14 ≤ n)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3=2^t*(c+3))
    (hinvMass : 2*k+c+2*t+2=b+d)
    (hk : 2≤k) (ht:2≤t)
    (hhigh : 12*2^n < b+4*m+4*n+20) :
    12*2^n < (2*k-4)+4*(m+t+1)+4*n+20 := by
  have hhalfb : 2*(b/2)=b := by omega
  by_cases ht2 : t=2
  · have hpow : 2^t=4 := by simp [ht2]
    have hW :
        8*((2*k-4)+4*(m+t+1)+4*n+20)=
          (b+4*m+4*n+20)+84*2^n+16*(m+n+6) := by
      rw [hpow] at hpower
      omega
    omega
  · have ht3 : 3≤t := by omega
    have hpow8 : 8≤2^t := by
      have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht3
      simpa using hh
    have hcmul : 8*(c+3) ≤ 2^t*(c+3) :=
      Nat.mul_le_mul_right (c+3) hpow8
    have hhalf : b/2≤b := by omega
    have hcBound : c < 2*2^n := by
      have hp : 1 ≤ 2^n := Nat.pow_pos (by decide)
      omega
    omega

#print axioms BB6.Agent50Defect.high_depth_preserves_above_twelve

end BB6.Agent50Defect
