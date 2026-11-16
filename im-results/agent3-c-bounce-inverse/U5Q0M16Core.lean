import U5Q0OddOddFan
import M0EvenEvenSumZero
import M32SectionEmbedding
import CSourceBridge16
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3U5Q0M16
open BB6.Agent3
open BB6.Agent46

private theorem cReach_not_seen (a k : Nat)
    (hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0)=false) :
    ¬ CReach a k := by
  intro hr
  have hr15 : BB6.Agent15.CReach a k := by
    simpa [BB6.Agent3.CReach, BB6.Agent15.CReach] using hr
  have hline : BB6CLine.Reach (a,k,0) :=
    BB6.Agent15.m32_section_reach_embeds hr15
  have hcert := CCert.source_reachable_embeds16 hline
  have hs := CCert.reachable_seen hcert
  rw [hseen] at hs
  cases hs

private theorem q0_absent :
    CCert.seen (CCert.q 14) (CCert.q 20) (CCert.q 0)=false := by decide
private theorem q1_absent_0 :
    CCert.seen (CCert.q 18) (CCert.q 15) (CCert.q 0)=false := by decide
private theorem q1_absent_1 :
    CCert.seen (CCert.q 10) (CCert.q 19) (CCert.q 0)=false := by decide
private theorem q1_absent_2 :
    CCert.seen (CCert.q 18) (CCert.q 23) (CCert.q 0)=false := by decide
private theorem q1_absent_3 :
    CCert.seen (CCert.q 10) (CCert.q 11) (CCert.q 0)=false := by decide

/-- Every original-section predecessor of X_t=(44*t-1,42*t-1) is
    excluded by the certified 24^3 modulus-16 quotient whenever
    t=19 (mod 32). The exact source fan leaves only q=0 and q=1;
    their quotient states are the five explicitly absent c=0 states. -/
theorem q0_X_not_reach (t n : Nat) (ht : t=32*n+19) :
    ¬ CReach (44*t-1) (42*t-1) := by
  intro hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*t-1) (42*t-1) (by rw [ht]; omega) hX
  have hfan := (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
    t a k (by rw [ht]; omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hqle : q≤1 := by
    by_cases hq2 : 2≤q
    · have hpow16 : 16∣4^q := by
        have h : 4^2∣4^q := Nat.pow_dvd_pow 4 (by omega)
        simpa using h
      obtain ⟨r,hr⟩ := hpow16
      obtain ⟨v,hv⟩ : ∃ v, U=2*v := ⟨U/2,by omega⟩
      have hdiv : 32∣4^q*U := by
        refine ⟨r*v, ?_⟩
        calc
          4^q*U=(16*r)*(2*v) := by rw [hr,hv]
          _=(16*2)*(r*v) := by ac_rfl
          _=32*(r*v) := by rw [show (16:Nat)*2=32 by decide]
      have hdivX : 32∣43*t-1 := by
        rw [hpow]
        exact hdiv
      have hmodX : (43*t-1)%32=0 := Nat.mod_eq_zero_of_dvd hdivX
      rw [ht] at hmodX
      omega
    · omega
  have hq0or1 : q=0 ∨ q=1 := by omega
  rcases hq0or1 with hq0 | hq1
  · subst q
    have hU : U=43*t-1 := by simpa using hpow.symm
    have ha' : a=43*t-3 := by rw [hU] at ha; omega
    have hk' : 2*k=85*t-7 := by rw [hU] at hcost; omega
    have haEq : a=1376*n+814 := by rw [ht] at ha'; omega
    have hkEq : k=1360*n+804 := by rw [ht] at hk'; omega
    have hqa : CCert.q a=CCert.q 14 := by
      apply CCert.q_congr_big
      · rw [haEq]; omega
      · decide
      · rw [haEq]; omega
    have hqk : CCert.q k=CCert.q 20 := by
      apply CCert.q_congr_big
      · rw [hkEq]; omega
      · decide
      · rw [hkEq]; omega
    have hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0)=false := by
      rw [hqa,hqk]
      exact q0_absent
    exact cReach_not_seen a k hseen hprev
  · subst q
    have hU : 4*U=43*t-1 := by simpa using hpow.symm
    have hUeq : U=344*n+204 := by rw [ht] at hU; omega
    have haEq : a=344*n+202 := by rw [hUeq] at ha; omega
    have hk' : 2*k=3752*n+2214 := by rw [hUeq,ht] at hcost; omega
    have hkEq : k=1876*n+1107 := by omega
    have hnCases : n%4=0 ∨ n%4=1 ∨ n%4=2 ∨ n%4=3 := by omega
    rcases hnCases with hn0 | hn1 | hn2 | hn3
    · have hqa : CCert.q a=CCert.q 10 := by
        apply CCert.q_congr_big
        · rw [haEq]; omega
        · decide
        · rw [haEq]; omega
      have hqk : CCert.q k=CCert.q 19 := by
        apply CCert.q_congr_big
        · rw [hkEq]; omega
        · decide
        · rw [hkEq]; omega
      have hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0)=false := by
        rw [hqa,hqk]
        exact q1_absent_1
      exact cReach_not_seen a k hseen hprev
    · have hqa : CCert.q a=CCert.q 18 := by
        apply CCert.q_congr_big
        · rw [haEq]; omega
        · decide
        · rw [haEq]; omega
      have hqk : CCert.q k=CCert.q 23 := by
        apply CCert.q_congr_big
        · rw [hkEq]; omega
        · decide
        · rw [hkEq]; omega
      have hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0)=false := by
        rw [hqa,hqk]
        exact q1_absent_2
      exact cReach_not_seen a k hseen hprev
    · have hqa : CCert.q a=CCert.q 10 := by
        apply CCert.q_congr_big
        · rw [haEq]; omega
        · decide
        · rw [haEq]; omega
      have hqk : CCert.q k=CCert.q 11 := by
        apply CCert.q_congr_big
        · rw [hkEq]; omega
        · decide
        · rw [hkEq]; omega
      have hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0)=false := by
        rw [hqa,hqk]
        exact q1_absent_3
      exact cReach_not_seen a k hseen hprev
    · have hqa : CCert.q a=CCert.q 18 := by
        apply CCert.q_congr_big
        · rw [haEq]; omega
        · decide
        · rw [haEq]; omega
      have hqk : CCert.q k=CCert.q 15 := by
        apply CCert.q_congr_big
        · rw [hkEq]; omega
        · decide
        · rw [hkEq]; omega
      have hseen : CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0)=false := by
        rw [hqa,hqk]
        exact q1_absent_0
      exact cReach_not_seen a k hseen hprev

#print axioms q0_X_not_reach
end BB6.Agent3U5Q0M16
