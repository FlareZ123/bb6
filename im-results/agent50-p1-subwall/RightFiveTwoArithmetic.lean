import Lean

namespace BB6.Agent50RightFiveTwo

theorem hundred_mul_le_pow (n : Nat) (hn : 14 ≤ n) :
    100*n ≤ 2^n := by
  have h : ∀ k : Nat, 100*(k+14) ≤ 2^(k+14) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hidx : k+1+14=(k+14)+1 := by omega
      rw [hidx,Nat.pow_succ]
      omega
  have hidx : (n-14)+14=n := by omega
  simpa only [hidx] using h (n-14)

/-- A dyadic gap that precludes a second positive reset with a right-five
terminal after a one-reset prefix. The equations are exact mass and power
identities of the source inverse word. -/
theorem no_two_reset_last_prefix (n r u B mp C : Nat)
    (hn : 14 ≤ n)
    (hr : r ≤ mp)
    (hmp : mp ≤ 3*n+4)
    (hu : 1 ≤ u)
    (hroot : 2^r*(B+12)+2*n+4=14*2^n)
    (hpower : 2*(2^u*C)+B+4*r+4*n+20=28*2^n)
    (hC : C=2*2^n+2*mp+2*n+6) : False := by
  have hbound : 100*n ≤ 2^n := hundred_mul_le_pow n hn
  by_cases hzero : r=0
  · have htwo : 2*C < 2^u*C := by
      simp [hzero] at hroot
      omega
    have hfour : 2^u*C < 4*C := by
      simp [hzero] at hroot
      omega
    by_cases huone : u=1
    · simp [huone] at htwo
    · have htwoexp : 2 ≤ u := by omega
      have hmonopow : 4 ≤ 2^u := by
        have hm := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) htwoexp
        simpa using hm
      have hmul : 4*C ≤ 2^u*C := Nat.mul_le_mul_right C hmonopow
      omega
  · have hrpos : 1 ≤ r := by omega
    have hpow : 2 ≤ 2^r := by
      have hm := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hrpos
      simpa using hm
    have hbig : 2*(B+12) ≤ 2^r*(B+12) :=
      Nat.mul_le_mul_right (B+12) hpow
    have hB : B ≤ 7*2^n := by omega
    have hfour : 4*C < 2^u*C := by omega
    have height : 2^u*C < 8*C := by omega
    by_cases hule : u ≤ 2
    · have hmonopow : 2^u ≤ 4 := by
        have hm := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hule
        simpa using hm
      have hmul : 2^u*C ≤ 4*C := Nat.mul_le_mul_right C hmonopow
      omega
    · have huthree : 3 ≤ u := by omega
      have hmonopow : 8 ≤ 2^u := by
        have hm := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) huthree
        simpa using hm
      have hmul : 8*C ≤ 2^u*C := Nat.mul_le_mul_right C hmonopow
      omega

#print axioms BB6.Agent50RightFiveTwo.hundred_mul_le_pow
#print axioms BB6.Agent50RightFiveTwo.no_two_reset_last_prefix

end BB6.Agent50RightFiveTwo
