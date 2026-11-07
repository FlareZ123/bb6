import RightFiveEnergyCone

namespace BB6.Agent50EnergyParam
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent50Energy
open BB6.Agent50ExceptionalDepth

/-- Exact parameterized buffer bound: the P-scale exponential witness
provides precisely the margin needed by the dyadic defect invariant. -/
theorem threshold_under_witness
    (n M m : Nat) (hM : M≤n) (hm : m≤M)
    (hNum : 64*(n+2)*(n+2)*2^M≤2^n) :
    threshold n M m≤2^n := by
  have h1 : M+n+6≤4*(n+2) := by omega
  have h2 : M-m+1≤n+2 := by omega
  have hprod := Nat.mul_le_mul h1 h2
  have hscale := Nat.mul_le_mul_left 16 hprod
  have hpart : 16*(M+n+6)*(M-m+1)≤64*(n+2)*(n+2) := by
    have heq : 16*(4*(n+2)*(n+2))=64*(n+2)*(n+2) := by
      calc
        _ = (16*4)*((n+2)*(n+2)) := by ac_rfl
        _ = 64*((n+2)*(n+2)) := by rw [show (16:Nat)*4=64 by decide]
        _ = 64*(n+2)*(n+2) := by ac_rfl
    simpa only [Nat.mul_assoc] using (Nat.le_trans hscale (Nat.le_of_eq heq))
  have hpow : 2^(M-m)≤2^M :=
    Nat.pow_le_pow_right (by decide) (by omega)
  calc
    threshold n M m = (16*(M+n+6)*(M-m+1))*2^(M-m) := rfl
    _ ≤ 64*(n+2)*(n+2)*2^M :=
      Nat.mul_le_mul hpart hpow
    _ ≤ 2^n := hNum

/-- The old shallow-step gap only requires M<=n, not M<=n/2. -/
theorem shallow_step_deficit_param (n M b d m t k c : Nat)
    (hn : 14≤n) (hM : M≤n) (hcost : m+t+1≤M)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3=2^t*(c+3))
    (hinvMass : 2*k+c+2*t+2=b+d)
    (ht : t≤1) (hk : 2≤k) :
    ((2*k-4)+4*(m+t+1)+4*n+20)+2^n ≤ 12*2^n := by
  obtain ⟨hpowerExact,hout⟩ :=
    energy_step_exact n b d m t k c hmass hb hpower hinvMass hk
  have h100 : 100*n≤2^n :=
    BB6.Agent50RightFiveTwo.hundred_mul_le_pow n (by omega)
  have hbefore : b+4*m+4*n+20 ≤14*2^n+2*m+2*n+7 := by omega
  have htp : 2^(t+1)≤4 := by
    by_cases hzero : t=0
    · simp [hzero]
    · have hone : t=1 := by omega
      simp [hone]
  have hmult : 2^(t+1)*(c+3)≤4*(c+3) :=
    Nat.mul_le_mul_right (c+3) htp
  have hclower : 14*2^n≤4*(c+3)+2*m+2*n+7 := by omega
  have hneed : 3*2^n+2*(m+n+t+4)≤c+3 := by omega
  omega

/-- Exact source CountCone, all n>=14 and arbitrary budget M<=n.
The 2^n buffer witness is an explicit necessary parameter condition;
no bound on reset count, word length or depth distribution. -/
theorem source_energy_budget_gap_param
    (n M b d m z : Nat) (hn : 14≤n) (hM : M≤n)
    (hNum : 64*(n+2)*(n+2)*2^M≤2^n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    m≤M →
    (12*2^n < b+4*m+4*n+20 ∨
      (b+4*m+4*n+20)+threshold n M m ≤12*2^n) := by
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
      have hsmall := threshold_under_witness n M (m+t+1) hM hmNow hNum
      exact Or.inr (by omega)
    · by_cases ht2 : t=2
      · subst t
        have hstep := two_step_cocycle n b d m k c hmass hb4 hInv.1 hinvMass
        have hdec := threshold_decay n M m (by omega)
        have hcm : m+2+1=m+3 := by omega
        rw [hcm] at hstep
        rcases hprev with hhi | hlo
        · exact Or.inl (by omega)
        · have hnow :
            ((2*k-4)+4*(m+3)+4*n+20)+threshold n M (m+3) ≤12*2^n := by
            omega
          exact Or.inr (by simpa only [hcm] using hnow)
      · have ht3 : 3≤t := by omega
        have hhigh := BB6.Agent50Energy.deep_high_step_above n b d m t k c
          (by omega) hmass hb4 hInv.1 hinvMass ht3 hk
        exact Or.inl hhigh

/-- Parametric uniform original-source strict cost lower bound approaching
2n-O(log n) by choosing M=n-O(log n). -/
theorem source_right_five_parametric_cost_gap
    (n M b m z : Nat) (hn : 14≤n) (hM : M≤n)
    (hNum : 64*(n+2)*(n+2)*2^M≤2^n)
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
    have hgap := source_energy_budget_gap_param
      n M bp dp mp zp hn hM hNum hpre hmPre
    have hThresh : 1≤threshold n M mp := by
      unfold threshold
      have h1 : 0<16*(M+n+6) := by omega
      have h2 : 0<(M-mp+1) := by omega
      have h3 : 0<(2:Nat)^(M-mp) := Nat.pow_pos (by decide)
      have h12 := Nat.mul_pos h1 h2
      have h123 := Nat.mul_pos h12 h3
      omega
    rcases hgap with hhigh | hlow
    · omega
    · omega

#print axioms BB6.Agent50EnergyParam.threshold_under_witness
#print axioms BB6.Agent50EnergyParam.source_energy_budget_gap_param
#print axioms BB6.Agent50EnergyParam.source_right_five_parametric_cost_gap

end BB6.Agent50EnergyParam
