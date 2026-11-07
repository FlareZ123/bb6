import RightFiveEnergyCone

namespace BB6.Agent50CostGap
open BB6.Agent28 BB6.Agent50Energy BB6.Agent50EnergySource
open BB6.Agent50ExceptionalDepth

/-- A genuine original P1 CountCone right-five history must cost strictly
more than n+2+floor(n/2), uniformly over its positive reset count and
inverse-word length for all n>=128. -/
theorem source_right_five_cost_above_three_halves
    (n b m z : Nat) (hn : 128≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    n+2+n/2 < m := by
  by_cases hcost : n+2+n/2 < m
  · exact hcost
  · exfalso
    have hmbound : m≤n+2+n/2 := by omega
    have hM : 2*(n/2)≤n := by omega
    have hPow : 100*n≤2^n :=
      BB6.Agent50RightFiveTwo.hundred_mul_le_pow n (by omega)
    have hmid : 2*m+n+2≤5*2^n := by omega
    have hz : 1≤z := by
      have hfloor := BB6.Agent50RightFive.source_right_five_needs_two_resets
        n b m z (by omega) h
      omega
    obtain ⟨bp,dp,mp,zp,k,hpre,hzEq,hip,hb,hkm,hbp,hdp,hmp⟩ :=
      source_mid_cost_exceptional_last_reset_depth n b 5 m z
        (by omega) hmid hz h rfl
    have hmPre : mp≤n/2 := by omega
    have hwall : bp+4*mp+4*n+20=12*2^n := by omega
    have hgap := source_energy_budget_gap n (n/2) bp dp mp zp hn hM hpre hmPre
    have hThresh : 1≤threshold n (n/2) mp := by
      unfold threshold
      have h1 : 0<16*(n/2+n+6) := by omega
      have h2 : 0<(n/2-mp+1) := by omega
      have h3 : 0<(2:Nat)^((n/2)-mp) := Nat.pow_pos (by decide)
      have h12 := Nat.mul_pos h1 h2
      have h123 := Nat.mul_pos h12 h3
      omega
    rcases hgap with hhigh | hlow
    · omega
    · omega

#print axioms BB6.Agent50CostGap.source_right_five_cost_above_three_halves

end BB6.Agent50CostGap
