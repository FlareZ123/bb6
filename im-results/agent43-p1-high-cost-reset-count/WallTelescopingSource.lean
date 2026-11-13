import CountedWallStrongGateSource

namespace BB6.Agent43WallTelescoping

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetStrength

/-- The path-weighted source invariant.  S is the sum of 2^s over inverse-edge
    starting costs s, and U is the sum of (n+3+s)2^s over the same starts.
    The witnesses are built inductively from the actual CountCone history. -/
theorem source_weighted_sum_invariant
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    ∃ S U : Nat,
      2 + 14*2^n*S = 2^m*(d-1) + 2*U := by
  induction h with
  | root =>
      exact ⟨0, 0, by simp⟩
  | parent bp dp mp zp t k c hp hb hb4 hd hi hk hc ih =>
      obtain ⟨S, U, hInv⟩ := ih
      have hodd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
        counted_to_odd_cone _ _ _ _ _ _ hp
      have hmass0 := odd_cone_mass _ _ bp dp mp hodd
      have hroot : (14*2^n-2*n-16)+3+2*n+13 = 14*2^n := by omega
      have hmass : bp+dp+2*mp+2*n+13 = 14*2^n := by omega
      have hpower := (inverseAt_iff_power_mass bp dp t k c
        (by omega) hb4 hd).mp hi
      have hbpEven : bp = 2*(bp/2) := by omega
      have hpower2 : 2*(dp+bp/2+3) = 2^(t+1)*(c+3) := by
        calc
          2*(dp+bp/2+3) = 2*(2^t*(c+3)) := by rw [hpower.1]
          _ = 2^(t+1)*(c+3) := by
            rw [Nat.pow_succ]
            ac_rfl
      have hpowmass :
          2^(t+1)*(c+3)+2*mp+2*n+7 = dp+14*2^n := by
        calc
          _ = 2*(dp+bp/2+3)+2*mp+2*n+7 := by rw [← hpower2]
          _ = dp+(bp+dp+2*mp+2*n+13) := by omega
          _ = dp+14*2^n := by rw [hmass]
      have hdpPos : 1 ≤ dp := by omega
      have hrec :
          (dp-1)+14*2^n =
            2^(t+1)*(c+3)+2*(mp+n+3) := by omega
      have hrecMul :
          2^mp*(dp-1)+14*2^n*2^mp =
            2^(mp+t+1)*(c+3)+2*(mp+n+3)*2^mp := by
        calc
          _ = 2^mp*((dp-1)+14*2^n) := by
            rw [Nat.mul_add]
            ac_rfl
          _ = 2^mp*(2^(t+1)*(c+3)+2*(mp+n+3)) := by rw [hrec]
          _ = 2^(mp+t+1)*(c+3)+2*(mp+n+3)*2^mp := by
            rw [Nat.mul_add]
            have hpows : 2^mp * 2^(t+1) = 2^(mp+t+1) := by
              rw [← Nat.pow_add]
              congr 1
              omega
            rw [hpows]
            ac_rfl
      refine ⟨S+2^mp, U+(n+3+mp)*2^mp, ?_⟩
      calc
        2+14*2^n*(S+2^mp) =
            (2+14*2^n*S)+14*2^n*2^mp := by
          rw [Nat.mul_add]
          ac_rfl
        _ = 2^mp*(dp-1)+2*U+14*2^n*2^mp := by rw [hInv]
        _ = 2^mp*(dp-1)+14*2^n*2^mp+2*U := by ac_rfl
        _ = 2^(mp+t+1)*(c+3)+2*(mp+n+3)*2^mp+2*U := by
          rw [hrecMul]
        _ = 2^(mp+t+1)*(c+3)+2*(U+(n+3+mp)*2^mp) := by
          conv_rhs => rw [Nat.mul_add]
          ac_rfl
        _ = 2^(mp+t+1)*((c+4)-1)+2*(U+(n+3+mp)*2^mp) := by
          congr 1
          omega

/-- Exact source-wall telescoping identity in subtraction-free Nat form.
    The first witness is the sum of 2^s over edge-start costs; the second
    includes the terminal cost m as well. -/
theorem source_wall_cost_identity
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hw : b+4*m+4*n+20 = 12*2^n) :
    ∃ S U : Nat, 1+7*2^n*S = 2^n*2^m+U := by
  obtain ⟨S, U, hInv⟩ := source_weighted_sum_invariant n b d m z hn h
  have hodd : OddCone (14*2^n-2*n-16) 3 b d m :=
    counted_to_odd_cone _ _ _ _ _ _ h
  have hmass0 := odd_cone_mass _ _ b d m hodd
  have hroot : (14*2^n-2*n-16)+3+2*n+13 = 14*2^n := by omega
  have hmass : b+d+2*m+2*n+13 = 14*2^n := by omega
  have hdEq : d = 2*2^n+2*m+2*n+7 := by omega
  have hdMinus : d-1 = 2*2^n+2*m+2*n+6 := by omega
  have hInv' :
      2+14*2^n*S =
        2^m*(2*2^n+2*m+2*n+6)+2*U := by
    simpa [hdMinus] using hInv
  have hfactor :
      2^m*(2*2^n+2*m+2*n+6) =
        2*(2^m*(2^n+m+n+3)) := by
    have hlin : 2*2^n+2*m+2*n+6 = 2*(2^n+m+n+3) := by omega
    rw [hlin]
    ac_rfl
  have hdouble :
      2*(1+7*2^n*S) =
        2*(2^m*(2^n+m+n+3)+U) := by
    calc
      2*(1+7*2^n*S) = 2+14*2^n*S := by omega
      _ = 2^m*(2*2^n+2*m+2*n+6)+2*U := hInv'
      _ = 2*(2^m*(2^n+m+n+3)+U) := by
        rw [hfactor, Nat.mul_add]
  have hfinal :
      1+7*2^n*S = 2^m*(2^n+m+n+3)+U := by omega
  refine ⟨S, 2^m*(m+n+3)+U, ?_⟩
  calc
    1+7*2^n*S = 2^m*(2^n+m+n+3)+U := hfinal
    _ = 2^n*2^m+(2^m*(m+n+3)+U) := by
      have hsplit : 2^n+m+n+3 = 2^n+(m+n+3) := by omega
      rw [hsplit, Nat.mul_add]
      ac_rfl

#print axioms BB6.Agent43WallTelescoping.source_weighted_sum_invariant
#print axioms BB6.Agent43WallTelescoping.source_wall_cost_identity

end BB6.Agent43WallTelescoping
