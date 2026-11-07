import RightFiveShallowSource
import RightFiveEnergyStep

namespace BB6.Agent50EnergySource
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent50Energy

/-- Universal authentic source CountCone energy barrier at every inverse
prefix with cost at most M<=n/2: a shifted left defect can never enter
the tiny forbidden gap around 12*2^n, regardless of transition depths,
number of positive resets or inverse-word length. -/
theorem source_energy_budget_gap
    (n M b d m z : Nat) (hn : 128≤n) (hM : 2*M≤n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    m≤M →
    (12*2^n < b+4*m+4*n+20 ∨
      (b+4*m+4*n+20)+threshold n M m ≤12*2^n) := by
  induction h with
  | root =>
    intro hm
    left
    have h100 : 100*n ≤ 2^n :=
      BB6.Agent50RightFiveTwo.hundred_mul_le_pow n (by omega)
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
    · have hGap := shallow_step_deficit n M b d m t k c hn hM
        hmNow hmass hb4 hInv.1 hinvMass hshallow hk
      have hsmall := threshold_under_pow n M (m+t+1) hn hM hmNow
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
        have hhigh := deep_high_step_above n b d m t k c hn
          hmass hb4 hInv.1 hinvMass ht3 hk
        exact Or.inl hhigh

#print axioms BB6.Agent50EnergySource.source_energy_budget_gap

end BB6.Agent50EnergySource
