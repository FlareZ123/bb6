import RightFiveEnergyParam

namespace BB6.Agent50EnergySharp

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent50Energy
open BB6.Agent50EnergyParam BB6.Agent50ExceptionalDepth

/-- Sharper buffer: the linear factor in the remaining budget is unnecessary. -/
def thresholdSharp (n M m : Nat) : Nat :=
  3*(M+n+6)*(2^(M-m)-1)+1

theorem thresholdSharp_decay (n M m : Nat)
    (hM : M≤n) (hm3 : m+3≤M) :
    8*thresholdSharp n M (m+3)+16*(m+n+6)
      ≤ thresholdSharp n M m := by
  have hA : 7≤5*(M+n+6) := by omega
  have hmn : m+n+6≤M+n+6 := by omega
  have hpow : 2^(M-m)=8*2^(M-(m+3)) := by
    have hexp : M-m=(M-(m+3))+3 := by omega
    rw [hexp, Nat.pow_add]
    norm_num [Nat.pow_succ]
  dsimp [thresholdSharp]
  rw [hpow]
  nlinarith

theorem thresholdSharp_under_witness (n M m : Nat)
    (hM : M≤n) (hm : m≤M)
    (hNum : 3*(M+n+6)*2^M+1≤2^n) :
    thresholdSharp n M m≤2^n := by
  have hidx : M-m≤M := by omega
  have hpow : 2^(M-m)≤2^M :=
    Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) hidx
  have hsub : 2^(M-m)-1≤2^M := by omega
  have hmul := Nat.mul_le_mul_left (3*(M+n+6)) hsub
  dsimp [thresholdSharp]
  omega

/-- The original-source energy induction with the sharper buffer. -/
theorem source_energy_budget_gap_sharp
    (n M b d m z : Nat) (hn : 14≤n) (hM : M≤n)
    (hNum : 3*(M+n+6)*2^M+1≤2^n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    m≤M →
    (12*2^n < b+4*m+4*n+20 ∨
      (b+4*m+4*n+20)+thresholdSharp n M m ≤12*2^n) := by
  induction h with
  | root =>
    intro hm
    left
    have h100 : 100*n≤2^n :=
      BB6.Agent50RightFiveTwo.hundred_mul_le_pow n hn
    omega
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
    intro hmNow
    have hmPrev : m≤M := by omega
    have hprev := ih hmPrev
    have hOdd : BB6.Agent1Quarter.OddCone (14*2^n-2*n-16) 3 b d m :=
      BB6.Agent43LastResetStrength.counted_to_odd_cone _ _ _ _ _ _ hp
    have hsourceMass :=
      BB6.Agent1Quarter.odd_cone_mass (14*2^n-2*n-16) 3 b d m hOdd
    have hmass : b+d+2*m+2*n+13=14*2^n := by omega
    have hInv := (inverseAt_iff_power_mass b d t k c (by omega) hb4 hd).mp hi
    have hinvMass : 2*k+c+2*t+2=b+d := by omega
    by_cases hshallow : t≤1
    · have hGap := shallow_step_deficit_param n M b d m t k c hn hM
        hmNow hmass hb4 hInv.1 hinvMass hshallow hk
      have hsmall := thresholdSharp_under_witness n M (m+t+1) hM hmNow hNum
      exact Or.inr (by omega)
    · by_cases ht2 : t=2
      · subst t
        have hstep := two_step_cocycle n b d m k c hmass hb4 hInv.1 hinvMass
        have hdec := thresholdSharp_decay n M m hM (by omega)
        have hcm : m+2+1=m+3 := by omega
        rw [hcm] at hstep
        rcases hprev with hhi | hlo
        · exact Or.inl (by omega)
        · have hnow :
            ((2*k-4)+4*(m+3)+4*n+20)+thresholdSharp n M (m+3) ≤12*2^n := by
            omega
          exact Or.inr (by simpa only [hcm] using hnow)
      · have ht3 : 3≤t := by omega
        have hhigh := BB6.Agent50Energy.deep_high_step_above n b d m t k c
          (by omega) hmass hb4 hInv.1 hinvMass ht3 hk
        exact Or.inl hhigh

/-- Sharper parametric strict cost lower bound for original right-five histories. -/
theorem source_right_five_parametric_cost_gap_sharp
    (n M b m z : Nat) (hn : 14≤n) (hM : M≤n)
    (hNum : 3*(M+n+6)*2^M+1≤2^n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    n+2+M<m := by
  by_cases hcost : n+2+M<m
  · exact hcost
  · exfalso
    have hmbound : m≤n+2+M := by omega
    have hPow : 100*n≤2^n :=
      BB6.Agent50RightFiveTwo.hundred_mul_le_pow n hn
    have hmid : 2*m+n+2≤5*2^n := by omega
    have hz : 1≤z := by
      have hfloor := BB6.Agent50RightFive.source_right_five_needs_two_resets
        n b m z hn h
      omega
    obtain ⟨bp,dp,mp,zp,k,hpre,hzEq,hip,hb,hkm,hbp,hdp,hmp⟩ :=
      source_mid_cost_exceptional_last_reset_depth n b 5 m z
        hn hmid hz h rfl
    have hmPre : mp≤M := by omega
    have hwall : bp+4*mp+4*n+20=12*2^n := by omega
    have hgap := source_energy_budget_gap_sharp
      n M bp dp mp zp hn hM hNum hpre hmPre
    have hThresh : 1≤thresholdSharp n M mp := by
      unfold thresholdSharp
      omega
    rcases hgap with hhigh | hlow
    · omega
    · omega

#print axioms BB6.Agent50EnergySharp.thresholdSharp_decay
#print axioms BB6.Agent50EnergySharp.thresholdSharp_under_witness
#print axioms BB6.Agent50EnergySharp.source_energy_budget_gap_sharp
#print axioms BB6.Agent50EnergySharp.source_right_five_parametric_cost_gap_sharp

end BB6.Agent50EnergySharp
