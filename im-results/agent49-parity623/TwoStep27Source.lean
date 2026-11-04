import Agent49LowStepSource
import Agent8RootedMass19Source
import Agent49FixedRaysSource
import Agent49TwoStep27HighSource

/-!
27-unit mass gain for all two surviving steps of Cryptids #623 whose first
counter is even and whose initial mass is at least 100, including every
low-even counter and the zero-second-counter ray. The final rooted theorem
derives a 27-per-two-return slope from depth 14 onward. It is conditional on
survival; this is not a proof of #623 nonhalting or a BB(6) solution.
-/

namespace BB6.Agent49TwoStep27Source
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

/-- Every two surviving transitions from any even-a mass≥100 state gain ≥27. -/
theorem two_step_gain27_mass100 (a d b e c f : Nat)
    (ha : a%2=0) (hm : 100≤a+d)
    (h1 : next (.D a d)=some (.D b e))
    (h2 : next (.D b e)=some (.D c f)) :
    a+d+27≤c+f := by
  change highLevelNext (.D a d)=some (.D b e) at h1
  by_cases hhigh : 6≤a
  · by_cases hz : d=0
    · subst d
      have hzero := BB6.Agent8SharpSource.high_zero_exact a (by omega)
      rw [hzero] at h1
      cases h1
      have h28 := BB6.Agent49FixedRaysSource.ray_14_gain28
        (a-4) c f (by omega) h2
      omega
    · have hdp : 0<d := by omega
      exact BB6.Agent49TwoStep27HighSource.high_even_two_step_gain27
        a d b e c f ha hhigh hdp hm h1 h2
  · have hsmall : a≤4 := by omega
    have hc : a=0 ∨ a=2 ∨ a=4 := by omega
    rcases hc with h0 | h2 | h4
    · subst a
      by_cases hodd : d%2=1
      · have hfirst := BB6.Agent49LowStepSource.low_zero_odd d hodd (by omega)
        rw [hfirst] at h1
        cases h1
        have h14 := BB6.Agent49TwoStep27HighSource.next_even_positive_mass14
          (d-1) 14 c f (by omega) (by omega) (by omega) (by omega) h2
        omega
      · have heven : d%2=0 := by omega
        have hfirst := BB6.Agent49LowStepSource.low_zero_even d heven
        rw [hfirst] at h1
        cases h1
        have h20 := BB6.Agent49FixedRaysSource.ray_7_gain20
          d c f (by omega) h2
        omega
    · subst a
      by_cases hodd : d%2=1
      · have hfirst := BB6.Agent49LowStepSource.low_two_odd d hodd (by omega)
        rw [hfirst] at h1
        cases h1
        have h18 := BB6.Agent49FixedRaysSource.ray_10_gain18
          (d+1) c f (by omega) h2
        omega
      · have heven : d%2=0 := by omega
        have hfirst := BB6.Agent49LowStepSource.low_two_even d heven (by omega)
        rw [hfirst] at h1
        cases h1
        have h20 := BB6.Agent49FixedRaysSource.ray_9_gain20
          d c f (by omega) h2
        omega
    · subst a
      by_cases hodd : d%2=1
      · have hfirst := BB6.Agent49LowStepSource.low_four_odd d hodd (by omega)
        rw [hfirst] at h1
        cases h1
        have h24 := BB6.Agent49FixedRaysSource.ray_12_gain24
          (d+1) c f (by omega) h2
        omega
      · have heven : d%2=0 := by omega
        have hfirst := BB6.Agent49LowStepSource.low_four_even d heven (by omega)
        rw [hfirst] at h1
        cases h1
        have h14 := BB6.Agent49TwoStep27HighSource.next_even_positive_mass14
          (d-6) 23 c f (by omega) (by omega) (by omega) (by omega) h2
        omega

/-- The genuine blank-origin section orbit has 27-unit two-step gain
from depth 14 onward, whenever both endpoint states exist. -/
theorem root_two_step_gain27 (n a d c f : Nat)
    (hn : 14≤n) (hbefore : run n=some (.D a d))
    (hafter : run (n+2)=some (.D c f)) :
    a+d+27≤c+f := by
  have hm : 100≤a+d := by
    have hb := BB6.Agent49ParitySource.run_grows_at_least_seven n a d hbefore
    omega
  have heven := BB6.Agent49ParitySource.run_preserves_even n a d hbefore
  cases hmid : next (.D a d) with
  | none =>
    have hnone : run (n+1)=none := by
      change (run n).bind highLevelNext = none
      rw [hbefore]
      exact hmid
    have hnone2 : run (n+2)=none := by
      change (run (n+1)).bind highLevelNext = none
      rw [hnone]
      rfl
    rw [hnone2] at hafter
    contradiction
  | some st =>
    rcases st with ⟨b,e⟩
    have hmidrun : run (n+1)=some (.D b e) := by
      change (run n).bind highLevelNext = some (.D b e)
      rw [hbefore]
      exact hmid
    have hstep2 : next (.D b e)=some (.D c f) := by
      change (run (n+1)).bind highLevelNext = some (.D c f) at hafter
      rw [hmidrun] at hafter
      exact hafter
    exact two_step_gain27_mass100 a d b e c f heven hm hmid hstep2

/-- Every surviving even-index return from section 14 has a 27-per-pair
linear lower bound, using only the source's old global seven-step floor at 14. -/
theorem root_even_mass27 (k a d : Nat)
    (h : run (14+2*k)=some (.D a d)) :
    105+27*k≤a+d := by
  induction k generalizing a d with
  | zero =>
    have h14 : run 14=some (.D a d) := by simpa using h
    have hm := BB6.Agent49ParitySource.run_grows_at_least_seven 14 a d h14
    omega
  | succ k ih =>
    let n : Nat := 14+2*k
    have htarget : run (n+2)=some (.D a d) := by
      have heq : n+2=14+2*(k+1) := by dsimp [n]; omega
      rw [heq]
      exact h
    cases hp : run n with
    | none =>
      have hnone : run (n+1)=none := by
        change (run n).bind highLevelNext = none
        rw [hp]
        rfl
      have hnone2 : run (n+2)=none := by
        change (run (n+1)).bind highLevelNext = none
        rw [hnone]
        rfl
      rw [hnone2] at htarget
      contradiction
    | some st =>
      rcases st with ⟨ap,dp⟩
      have hprev : run (14+2*k)=some (.D ap dp) := by simpa only [n] using hp
      have hbound := ih ap dp hprev
      have hgain := root_two_step_gain27 n ap dp a d (by dsimp [n]; omega)
        hp htarget
      omega

#print axioms two_step_gain27_mass100
#print axioms root_two_step_gain27
#print axioms root_even_mass27
end BB6.Agent49TwoStep27Source
