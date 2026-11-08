import WallResetDensitySource
import WallDensityNumeric
import DepthIndexedResetFloor

namespace BB6.Agent50Density
open BB6.Agent28 BB6.Agent43DepthResetFloor

/-- Every original-source inverse history hitting the shifted critical wall
must contain strictly more than floor(n/4) genuine positive-depth resets
for n>=68, without any cost or history-length restriction. -/
theorem source_quarter_wall_reset_floor
    (n b d m z : Nat) (hn : 68≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hwall : b+4*m+4*n+20=12*2^n) :
    n/4<z :=
  quarter_reset_from_growth n z hn
    (source_wall_reset_growth n b d m z (by omega) h hwall)

/-- Every original P1 right-five critical inverse history has strictly
more than n/4 positive-depth resets for n>=68. This is uniform in the
original CountCone's length and total cost, without root reachability. -/
theorem source_quarter_right_five_reset_floor
    (n b m z : Nat) (hn : 68≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    n/4<z := by
  have hNum := quarter_numeric n hn
  rcases source_right_five_depth_reset_dichotomy n b m z (by omega) h with
    hHigh | hPrefix
  · by_cases hz : n/4<z
    · exact hz
    · have hq : z≤n/4 := by omega
      have hMonot := Nat.mul_le_mul_left (2*n+3) hq
      have hMul : 1≤8^(n/4) := Nat.one_le_pow (n/4) 8 (by decide)
      have hScale : 32*(2*n+7+(2*n+3)*(n/4)) ≤
          32*(2*n+7+(2*n+3)*(n/4))*8^(n/4) :=
        Nat.le_mul_of_pos_right _ hMul
      have hStrict : (2*n+3)*(n/4) <
          32*(2*n+7+(2*n+3)*(n/4)) := by omega
      omega
  · rcases hPrefix with ⟨bp,dp,mp,zp,k,hpre,hzEq,hzp,hip,hb,hkm,
        hbpExact,hwall,hdpExact,hmEq,hcost⟩
    have hpreFloor := source_quarter_wall_reset_floor
      n bp dp mp zp hn hpre hwall
    omega

#print axioms BB6.Agent50Density.source_quarter_wall_reset_floor
#print axioms BB6.Agent50Density.source_quarter_right_five_reset_floor
end BB6.Agent50Density
