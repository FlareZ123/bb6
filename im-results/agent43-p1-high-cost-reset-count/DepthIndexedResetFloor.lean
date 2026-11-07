import RightFiveThreeSource

namespace BB6.Agent43DepthResetFloor

open BB6.Agent28
open BB6.Agent47P1
open BB6.Agent50ExceptionalDepth
open BB6.Agent50RightFiveThree

private theorem nat_le_two_pow (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hp : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
    calc
      n+1 ≤ 2^n+1 := Nat.add_le_add_right ih 1
      _ ≤ 2^n+2^n := Nat.add_le_add_left hp (2^n)
      _ = 2^(n+1) := by rw [Nat.pow_succ]; omega

/-- Every original-source P1 counted history ending at right counter five
either has at least 3*2^n/(2*n+3) positive-depth resets, or its final
positive reset has the maximal possible depth n+1. In the latter case its
genuine CountCone prefix has at least two positive resets, lies exactly on
the shifted 12*2^n wall, and has the displayed cost cap. This is a source
theorem about counted inverse histories, not a blank-root reachability claim. -/
theorem source_right_five_depth_reset_dichotomy
    (n b m z : Nat)
    (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    (3*2^n ≤ (2*n+3)*z) ∨
    ∃ bp dp mp zp k,
      CountCone (14*2^n-2*n-16) 3 bp dp mp zp ∧
      z=zp+1 ∧
      2≤zp ∧
      inverseAt bp dp (n+1)=some (k,1) ∧
      b=2*k-4 ∧
      k+m+n+7=7*2^n ∧
      bp+4*m+12=12*2^n ∧
      bp+4*mp+4*n+20=12*2^n ∧
      dp=2*2^n+2*m+3 ∧
      mp+n+2=m ∧
      mp+n+7≤3*2^n := by
  have hzThree : 3≤z :=
    source_right_five_needs_three_resets n b m z hn h
  have hz : 1≤z := by omega
  obtain ⟨bp,dp,mp,zp,t,k,hpre,hzEq,hip,hb,hkm,hbp,hdp,hmEq,
      hdepthEnergy,henergy,hcost,hdpMin,hdepthExact,hcostLower,
      hcostUpper,htLow,htUpper⟩ :=
    source_exceptional_last_reset_depth_window n b 5 m z hn hz h rfl
  have hpowrel : 2^(t+3)=2*2^(t+2) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hmlower : 7*2^n+t ≤ 2^(t+2)+m+n := by omega
  have hnp : n≤2^n := nat_le_two_pow n
  by_cases ht : t≤n
  · have hmLower : 3*2^n≤m := by
      by_cases htn : t=n
      · subst t
        have hpow : 2^(n+2)=4*2^n := by
          simp [Nat.pow_add]
        omega
      · have ht' : t+1≤n := by omega
        have hpow : 2^(t+2)≤2^(n+1) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hpow2 : 2^(n+1)=2*2^n := by
          rw [Nat.pow_succ, Nat.mul_comm]
        omega
    exact Or.inl (by omega)
  · have htEq : t=n+1 := by omega
    have hpow2 : 2^(t+1)=4*2^n := by
      rw [htEq, show n+1+1=n+2 by omega, Nat.pow_add]
      simp [Nat.mul_comm]
    have hpow3 : 2^(t+3)=16*2^n := by
      rw [htEq, show n+1+3=n+4 by omega, Nat.pow_add]
      simp [Nat.mul_comm]
    have hbpExact : bp+4*m+12=12*2^n := by
      rw [hpow3] at hbp
      omega
    have hdpExact : dp=2*2^n+2*m+3 := by
      rw [hpow3] at hdp
      omega
    have hcostExact : mp+n+7≤3*2^n := by
      rw [hpow2] at hcostUpper
      omega
    have hwall : bp+4*mp+4*n+20=12*2^n := by omega
    have hzp : 2≤zp := by omega
    have hipExact : inverseAt bp dp (n+1)=some (k,1) := by
      simpa [htEq] using hip
    exact Or.inr ⟨bp,dp,mp,zp,k,hpre,hzEq,hzp,hipExact,hb,hkm,
      hbpExact,hwall,hdpExact,by omega,hcostExact⟩

#print axioms BB6.Agent43DepthResetFloor.source_right_five_depth_reset_dichotomy

end BB6.Agent43DepthResetFloor
