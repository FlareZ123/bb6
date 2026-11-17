import U5Q0CLineFilter
import U5Q0M16Residual
import U5Y3M8
import M0EvenEvenSumZero
import M32SectionEmbedding
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000

/-!
A source-only replacement for the M16 quotient at the U5 residual
cylinder w = 21 (mod 32).

The exact q=0 odd/odd parent fan of X_t=(44*t-1,42*t-1), when
t=32*n+19, has only q=0 and q=1. The q=0 parent is excluded by
the source filter's (V+q)=0 (mod 4), k=4 (mod 8) branch; the q=1
parent is excluded by its (V+q)=3 (mod 4) branch.

This composes with the existing two-step pullback from the y=3
terminal and the U5 residual identity. It is a source-proof draft
pending exact local Lean preflight; it is not a BB(6) decision.
-/

namespace BB6.Agent3U5CLineResidualClosure

open BB6.Agent3
open BB6.Agent46

private theorem section_reach_embeds_line (a k : Nat)
    (h : BB6.Agent3.CReach a k) :
    BB6CLine.Reach (a,k,0) := by
  have hr15 : BB6.Agent15.CReach a k := by
    simpa [BB6.Agent3.CReach, BB6.Agent15.CReach] using h
  exact BB6.Agent15.m32_section_reach_embeds hr15

/-- The exact original-section parent fan of X_t is blank-unreachable
    whenever t=19 (mod 32), using only source-level CLine filters. -/
theorem q0_X_not_reach_t19 (t n : Nat) (ht : t=32*n+19) :
    ¬ BB6.Agent3.CReach (44*t-1) (42*t-1) := by
  intro hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (44*t-1) (42*t-1) (by rw [ht]; omega) hX
  have hline : BB6CLine.Reach (a,k,0) :=
    section_reach_embeds_line a k hprev
  have hfilter :=
    BB6.Agent3U5CLineFilter.reachable_q0_parent_filter
      t a k (by rw [ht]; omega) hstep hline
  rcases hfilter with
    ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost,hnot3,hnot0k4⟩
  have hN : 43*t-1=16*(86*n+51) := by
    rw [ht]
    omega
  have hNmod32 : (43*t-1)%32=16 := by
    rw [hN]
    omega
  have hqle : q≤1 := by
    by_contra hnot
    have hq2 : 2≤q := by omega
    have hpow16 : 16∣4^q := by
      have h := Nat.pow_dvd_pow 4 hq2
      simpa using h
    obtain ⟨r,hr⟩ := hpow16
    obtain ⟨v,hv⟩ : ∃ v, U=2*v := ⟨U/2,by omega⟩
    have hdiv : 32∣4^q*U := by
      refine ⟨r*v,?_⟩
      calc
        4^q*U=(16*r)*(2*v) := by rw [hr,hv]
        _=(16*2)*(r*v) := by ac_rfl
        _=32*(r*v) := by norm_num
    have hdivN : 32∣43*t-1 := by
      rw [hpow]
      exact hdiv
    have hmod0 : (43*t-1)%32=0 :=
      Nat.mod_eq_zero_of_dvd hdivN
    omega
  have hqcases : q=0 ∨ q=1 := by omega
  rcases hqcases with hq0 | hq1
  · have hUeq : U=16*(86*n+51) := by
      have hU : U=43*t-1 := by
        simpa [hq0] using hpow.symm
      rw [hN] at hU
      exact hU
    have hV : U/2=8*(86*n+51) := by
      rw [hUeq]
      omega
    have hvq0 : (U/2+q)%4=0 := by
      rw [hq0,hV]
      omega
    have hcost0 :
        2*k+16*(86*n+51)=128*(32*n+19)-8 := by
      simpa [hq0,hUeq,ht] using hcost
    have hk8 : k%8=4 := by omega
    rcases hnot0k4 with hbad | hbad <;> omega
  · have hpow' : 4*U=43*t-1 := by
      simpa [hq1] using hpow
    have hUeq : U=4*(86*n+51) := by
      rw [hN] at hpow'
      omega
    have hV : U/2=2*(86*n+51) := by
      rw [hUeq]
      omega
    have hvq3 : (U/2+q)%4=3 := by
      rw [hq1,hV]
      omega
    exact hnot3 hvq3

private theorem q0_parent_reach_implies_X (t : Nat) (ht : 1≤t)
    (h : CReach (64*t+5) (32*t+3)) :
    CReach (44*t-1) (42*t-1) := by
  have h1 := (BB6.Agent3.oddodd_val3_blank_reach_iff
    (64*t+5) (32*t+3)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h
  have h1' : CReach (48*t+2) (40*t+1) := by
    have hx : ((64*t+5)+(32*t+3)-4)/2=48*t+2 := by omega
    have hy : ((64*t+5)+3*(32*t+3)-10)/4=40*t+1 := by omega
    simpa only [hx,hy] using h1
  have h2 := (BB6.Agent3.evenodd_four_blank_reach_iff
    (48*t+2) (40*t+1)
    (by omega) (by omega) (by omega) (by omega)).mp h1'
  have h2' : CReach (44*t-1) (42*t-1) := by
    have hx : ((48*t+2)+(40*t+1)-5)/2=44*t-1 := by omega
    have hy : ((48*t+2)+3*(40*t+1)-9)/4=42*t-1 := by omega
    simpa only [hx,hy] using h2
  exact h2'

/-- The q=0 y=3 predecessor on w=21 (mod 32) is unreachable
    without the M16 quotient: its two-step pullback is X_t, and
    the complete original-source q-fan is excluded by CRange/CBack. -/
theorem blank_no_u5_q0_parent_w21 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%32=21)
    (ht : 1≤t)
    (hparent : CReach (64*t+5) (32*t+3)) : False := by
  have hX := q0_parent_reach_implies_X t ht hparent
  have htmod := BB6.Agent3U5M16Residual.u5_m8_t_mod32
    w s m t hs hm hp hw
  obtain ⟨n,hn⟩ : ∃ n, t=32*n+19 := by
    refine ⟨t/32,?_⟩
    omega
  exact q0_X_not_reach_t19 t n hn hX

#print axioms q0_X_not_reach_t19
#print axioms blank_no_u5_q0_parent_w21

end BB6.Agent3U5CLineResidualClosure
