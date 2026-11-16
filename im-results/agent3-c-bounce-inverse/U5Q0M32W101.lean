import U5Q0OddOddFan
import M0EvenEvenSumZero
import M32SectionEmbedding
import M32U5Backward
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Source-only closure draft for the U5 q=0 target on the exact cylinder
t = 128*n+35, n = 3 (mod 4).

The complete exact original-section predecessor fan has depths q=0,1,2
because v2(43*t-1)=5. Depths 0 and 2 project to already M32-certified
absent cells; depth 1 is excluded by Agent 32's source-level backward
cone. This is a source proof draft, not yet locally preflighted or
CI-certified, and it is not a BB(6) decision.
-/

namespace BB6.Agent3U5M32W101

private theorem section_reach_embeds_line (a k : Nat)
    (h : BB6.Agent3.CReach a k) :
    BB6CLine.Reach (a,k,0) := by
  have hr15 : BB6.Agent15.CReach a k := by
    simpa [BB6.Agent3.CReach, BB6.Agent15.CReach] using h
  exact BB6.Agent15.m32_section_reach_embeds hr15

private theorem cReach_not_m32_cell (a k : Nat)
    (hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0) = false) :
    ¬ BB6.Agent3.CReach a k := by
  intro h
  exact CCert.original_m32_cell_unreachable a k hseen
    (section_reach_embeds_line a k h)

private theorem cReach_not_22_45 (a k : Nat)
    (ha : a % 64 = 22) (hk : k % 64 = 45) :
    ¬ BB6.Agent3.CReach a k := by
  intro h
  exact BB6.Agent32U5Backward.original_no_22_45 a k ha hk
    (section_reach_embeds_line a k h)

/-- The exact odd/odd target X_t=(44*t-1,42*t-1) is outside the
authentic blank section orbit when t=35 (mod 512) and, more precisely,
t=128*n+35 with n=3 (mod 4). Every original-section predecessor is
covered by one of three cases: an M32-absent q=0 cell, the source-level
(22,45) backward cone at q=1, or an M32-absent q=2 cell. -/
theorem q0_X_not_reach_t35 (n : Nat) (hn : n % 4 = 3) :
    ¬ BB6.Agent3.CReach
      (44*(128*n+35)-1) (42*(128*n+35)-1) := by
  let t := 128*n+35
  intro hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*t-1) (42*t-1) (by dsimp [t]; omega) hX
  have hfan :=
    (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
      t a k (by dsimp [t]; omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hN : 43*t-1 = 32*(172*n+47) := by dsimp [t]; omega
  have hNmod64 : (43*t-1) % 64 = 32 := by
    rw [hN]
    omega
  have hqle : q ≤ 2 := by
    by_contra hnot
    have hq3 : 3 ≤ q := by omega
    have hpow64 : 64 ∣ 4^q := by
      have h := Nat.pow_dvd_pow 4 hq3
      have h64 : (4:Nat)^3 = 64 := by decide
      simpa only [h64] using h
    obtain ⟨r,hr⟩ := hpow64
    have hdiv : 64 ∣ 4^q*U := by
      refine ⟨r*U, ?_⟩
      rw [hr]
      ac_rfl
    have hdivN : 64 ∣ 43*t-1 := by
      rw [hpow]
      exact hdiv
    have hmod0 : (43*t-1) % 64 = 0 :=
      Nat.mod_eq_zero_of_dvd hdivN
    omega
  have hqcases : q=0 ∨ q=1 ∨ q=2 := by omega
  rcases hqcases with hq0 | hq1 | hq2
  · have hU : U = 43*t-1 := by
      simpa [hq0] using hpow.symm
    have haEq : a = 5504*n+1502 := by
      rw [hU] at ha
      dsimp [t] at ha
      omega
    have hkEq : k = 5440*n+1484 := by
      rw [hU,hq0] at hcost
      dsimp [t] at hcost
      omega
    have hqa : CCert.q a = CCert.q 30 := by
      apply CCert.q_congr_big
      · rw [haEq]
        omega
      · decide
      · rw [haEq]
        omega
    have hqk : CCert.q k = CCert.q 12 := by
      apply CCert.q_congr_big
      · rw [hkEq]
        omega
      · decide
      · rw [hkEq]
        omega
    have hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0) = false := by
      rw [hqa,hqk]
      decide
    exact cReach_not_m32_cell a k hseen hprev
  · have hUeq : 4*U = 43*t-1 := by
      simpa [hq1] using hpow.symm
    have hU : U = 1376*n+376 := by
      dsimp [t] at hUeq
      omega
    have haEq : a = 1376*n+374 := by
      rw [hU] at ha
      omega
    have hkEq : k = 7504*n+2045 := by
      rw [hU,hq1] at hcost
      dsimp [t] at hcost
      omega
    have haMod : a % 64 = 22 := by rw [haEq]; omega
    have hkMod : k % 64 = 45 := by rw [hkEq]; omega
    exact cReach_not_22_45 a k haMod hkMod hprev
  · have hUeq : 16*U = 43*t-1 := by
      simpa [hq2] using hpow.symm
    have hU : U = 344*n+94 := by
      dsimp [t] at hUeq
      omega
    have haEq : a = 344*n+92 := by
      rw [hU] at ha
      omega
    have hkEq : k = 8020*n+2183 := by
      rw [hU,hq2] at hcost
      dsimp [t] at hcost
      omega
    have hnCases : n%8=3 ∨ n%8=7 := by omega
    rcases hnCases with hn3 | hn7
    · have hqa : CCert.q a = CCert.q 36 := by
        apply CCert.q_congr_big
        · rw [haEq]
          omega
        · decide
        · rw [haEq]
          omega
      have hqk : CCert.q k = CCert.q 35 := by
        apply CCert.q_congr_big
        · rw [hkEq]
          omega
        · decide
        · rw [hkEq]
          omega
      have hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0) = false := by
        rw [hqa,hqk]
        decide
      exact cReach_not_m32_cell a k hseen hprev
    · have hqa : CCert.q a = CCert.q 36 := by
        apply CCert.q_congr_big
        · rw [haEq]
          omega
        · decide
        · rw [haEq]
          omega
      have hqk : CCert.q k = CCert.q 19 := by
        apply CCert.q_congr_big
        · rw [hkEq]
          omega
        · decide
        · rw [hkEq]
          omega
      have hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0) = false := by
        rw [hqa,hqk]
        decide
      exact cReach_not_m32_cell a k hseen hprev

#print axioms q0_X_not_reach_t35
end BB6.Agent3U5M32W101
