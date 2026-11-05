import CountedWallStrongGateSource
import NumericBridge148
import WallCountLowerBound

namespace BB6.Agent43Wall148Source

open BB6.Agent28 BB6.Agent43LastResetDraft BB6.Agent43WallStrongGate
open BB6.Agent43Numeric148 BB6.Agent50TwoReset

/-- All genuine P1 critical counted wall inverse histories have cost strictly
    above n+z for n>=148, uniformly in the number of positive resets and in
    every interleaved zero-depth inverse segment. Original source definitions. -/
theorem source_critical_wall_cost_above_n_plus_resets
    (n b d m z : Nat) (hn : 148 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hwall : b=4*(m+n)) :
    n+z < m := by
  have hzpos : 1 ≤ z := by
    by_cases hz0 : z=0
    · have hshape := (cone_shape _ _ b d m z h).1 hz0
      obtain ⟨r,htail⟩ := hshape
      exact False.elim
        (source_critical_zero_reset_no_wall n b d m r
          (by omega) htail hwall)
    · omega
  by_cases hsmall : m ≤ n+z
  · have hmin := counted_cost_at_least_twice_resets
      (14*2^n-2*n-16) 3 b d m z h
    have hzle : z ≤ n := by omega
    have hstrong : 3*2^z ≤ 2*(m+n+3) :=
      source_wall_near_cost_has_reset_bound n b d m z
        (by omega) hzpos h hwall hsmall
    have hgate : 3*2^z ≤ 4*n+2*z+6 := by omega
    have hnumeric : 24^z*(n+2)^(2*z+2) < 2^n :=
      universal_numeric_gap_148 n z hn hzle hgate
    have hreset : 2^n ≤ 24^z*(n+2)^(2*z+2) :=
      source_wall_forces_exponential_reset_count
        n z b d m (by omega) hzpos h hwall
    omega
  · omega

#print axioms BB6.Agent43Wall148Source.source_critical_wall_cost_above_n_plus_resets

end BB6.Agent43Wall148Source
