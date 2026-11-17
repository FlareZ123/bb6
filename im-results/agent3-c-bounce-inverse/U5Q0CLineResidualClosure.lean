import U5Q0CLineFilter
import U5Q0M16Residual
import U5Y3M8
import M0EvenEvenSumZero
import M32SectionEmbedding
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000

/-!
Source-only replacements for the M16 quotient at the U5 residual
cylinders w = 21 (mod 32) and w = 37 (mod 128).

The exact q=0 odd/odd parent fan of X_t=(44*t-1,42*t-1), when
t=32*n+19, has only q=0 and q=1. The q=0 parent is excluded by
the source filter's (V+q)=0 (mod 4), k=4 (mod 8) branch; the q=1
parent is excluded by its (V+q)=3 (mod 4) branch.

Both closures compose with the existing two-step pullback from the y=3
terminal and the U5 residual identity. The w=37 case additionally proves
a new zero-left CLine obstruction. These are source-proof drafts pending
exact local Lean preflight; they are not BB(6) decisions.
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


/-- If a high hub has first coordinate above 2, its final source step
    is either the ordinary high predecessor or the even zero-left
    branch. This is the exceptional case omitted by reached_hub_prev. -/
private theorem reached_hub_prev_or_zero (a c : Nat)
    (h : BB6CLine.Reach (a,2,c+4)) (ha : 2<a) :
    BB6CLine.Reach (a+1,1,c+5) ∨
      ∃ r, a=2*r+2 ∧ BB6CLine.Reach (0,r,c+7) := by
  cases h with
  | next s t hs hn =>
      rcases s with ⟨x,m,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp [BB6CLine.nextC] at hn
        · rcases m with _|m
          · simp [BB6CLine.nextC] at hn
          · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
            omega
        · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hm : m%2=0
          · simp only [BB6CLine.nextC,hm,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at hn
            rcases hn with ⟨haeq,hkeq,hceq⟩
            right
            refine ⟨m,?_ ,?_⟩
            · omega
            · have heq : (0,m,e+4)=(0,m,c+7) := by
                simp only [Prod.mk.injEq]
                exact ⟨rfl,rfl,by omega⟩
              exact heq ▸ hs
          · simp [BB6CLine.nextC,hm] at hn
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          rcases hn with ⟨haeq,hkeq,hceq⟩
          left
          have heq : (x+1,m,e+4)=(a+1,1,c+5) := by
            simp only [Prod.mk.injEq]
            omega
          exact heq ▸ hs

/-- The even zero-left source branch with residues (2,6) modulo 8
    cannot be in the authentic blank-start CLine orbit. Reverse the
    unique high tail to a k=2 hub; its high/reset alternatives violate
    the middle-zero or odd-zero source invariants. -/
private theorem zero_left_26_not_reach (r c : Nat)
    (hrge : 10≤r) (hcge : 4≤c)
    (hr8 : r%8=2) (hc8 : c%8=6)
    (h : BB6CLine.Reach (0,r,c)) : False := by
  have hrev := BB6.CBack.reverse_high 0 0 (c-4) (r-3) (by
    simpa [show r-3+3=r by omega, show c-4+4=c by omega] using h)
  have hrev' : BB6CLine.Reach (r-3,3,c+r-3) := by
    have hright : (c-4)+(r-3)+4=c+r-3 := by omega
    simpa [Nat.zero_add,hright] using hrev
  have hrevInput : BB6CLine.Reach (r-3,0+3,(c+r-7)+4) := by
    have hright : (c+r-7)+4=c+r-3 := by omega
    simpa [hright] using hrev'
  have hhub := BB6.CBack.reached_high_pred (r-3) 0 (c+r-7) hrevInput
  have hhub' : BB6CLine.Reach (r-2,2,c+r-2) := by
    have hleft : (r-3)+1=r-2 := by omega
    have hright : (c+r-7)+5=c+r-2 := by omega
    simpa [hleft,hright] using hhub
  have hAne : (r-2)%4≠2 := by omega
  have hprev := BB6.CBack.reached_hub_prev (r-2) (c+r-6) hhub' hAne
  have hprev' : BB6CLine.Reach (r-1,1,(c+r-5)+4) := by
    have hleft : (r-2)+1=r-1 := by omega
    have hright : (c+r-6)+5=c+r-5+4 := by omega
    simpa [hleft,hright] using hprev
  have hsplit := BB6.CBack.reached_one_high_or_reset (r-1) (c+r-5) hprev'
  rcases hsplit with hhigh | ⟨s,hsEq,hreset⟩
  · have hmid := BB6.Agent48.reached_middle_zero_mod4 r (c+r) hhigh
    have hr4 : r%4=2 := by omega
    omega
  · have hsMod : s%4=3 := by
      have hs2 : 2*s=c+r-2 := by omega
      omega
    have hsge : 5≤s := by omega
    have hsodd : s%2=1 := by omega
    have hleftMod : (r+1)%4=3 := by omega
    have hsumMod : ((r+1)+s)%4=2 := by omega
    have hhole := BB6.CRange.reached_odd_zero_mod4_hole
      (r+1) s hreset hsge hsodd
    rcases hhole with h0 | h3 <;> omega

/-- The exceptional q=1 parent for t=99 (mod 128) has a zero-left
    inverse branch with middle/right residues (2,6) modulo 8. The
    other possible hub predecessor immediately violates the
    middle-zero invariant. -/
private theorem q1_parent_not_reach_t99 (t n R U k : Nat)
    (ht : t=128*n+99)
    (hR : R=172*n+133)
    (hU : U=8*R)
    (hcost : 2*k+U+6=128*t-8) :
    ¬ BB6CLine.Reach (U-2,k,0) := by
  intro hreach
  have hk : k=64*t-7-4*R := by
    rw [hU] at hcost
    omega
  let A := U-2+k-5
  have hA : A=64*t+4*R-14 := by
    dsimp [A]
    rw [hU,hk]
    omega
  have hA16 : A%16=6 := by
    rw [hA,ht,hR]
    omega
  have hAgt : 2<A := by
    rw [hA,ht,hR]
    omega
  have hkOdd : k%2=1 := by
    rw [hk,ht,hR]
    omega
  have hkge : 7≤k := by
    rw [hk,ht,hR]
    omega
  have hreach0 : BB6CLine.Reach (U-2,(k-7)+7,0) := by
    have heq : (k-7)+7=k := by omega
    simpa [heq] using hreach
  have hhub := BB6.CBack.reached_zero_hub (U-2) (k-7) hreach0
  have hleft : U-2+(k-7)+2=A := by
    dsimp [A]
    omega
  have hright : (k-7)+5=k-2 := by omega
  have hhub' : BB6CLine.Reach (A,2,k-2) := by
    simpa [hleft,hright] using hhub
  have hcase := reached_hub_prev_or_zero A (k-6) hhub' hAgt
  rcases hcase with hhigh | ⟨r,hrEq,hzero⟩
  · have hprev' : BB6CLine.Reach (A+1,1,(k-5)+4) := by
      have heq : (k-6)+5=(k-5)+4 := by omega
      simpa [heq] using hhigh
    have hsplit := BB6.CBack.reached_one_high_or_reset (A+1) (k-5) hprev'
    rcases hsplit with hmid | ⟨s,hsEq,hsReset⟩
    · have hmid0 := BB6.Agent48.reached_middle_zero_mod4 (A+2) k hmid
      have hAplus2 : (A+2)%4=0 := by
        rw [hA16]
        omega
      omega
    · omega
  · have hr8 : r%8=2 := by
      rw [hrEq] at hA16
      omega
    have hc8 : (k+1)%8=6 := by
      rw [hk,ht,hR]
      omega
    have hrge : 10≤r := by
      rw [hrEq] at hA
      rw [ht,hR] at hA
      omega
    have hcge : 4≤k+1 := by
      rw [hk,ht,hR]
      omega
    exact zero_left_26_not_reach r (k+1) hrge hcge hr8 hc8 hzero

/-- The complete q-fan of X_t is blank-unreachable when t=99
    (mod 128). q=0 and q=2 are excluded by the CLine filter; q=1
    is eliminated by the new zero-left (2,6)-mod-8 obstruction. -/
theorem q0_X_not_reach_t99 (t n : Nat) (ht : t=128*n+99) :
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
  let R := 172*n+133
  have hR : R=172*n+133 := rfl
  have hN : 43*t-1=32*R := by
    rw [ht,hR]
    omega
  have hRmod4 : R%4=1 := by
    rw [hR]
    omega
  have hNmod128 : (43*t-1)%128=32 := by
    rw [hN]
    omega
  have hqle : q≤2 := by
    by_contra hnot
    have hq3 : 3≤q := by omega
    have hpow64 : 64∣4^q := by
      have h := Nat.pow_dvd_pow 4 hq3
      simpa using h
    obtain ⟨r,hr⟩ := hpow64
    obtain ⟨v,hv⟩ : ∃ v, U=2*v := ⟨U/2,by omega⟩
    have hdiv : 128∣4^q*U := by
      refine ⟨r*v,?_⟩
      calc
        4^q*U=(64*r)*(2*v) := by rw [hr,hv]
        _=(64*2)*(r*v) := by ac_rfl
        _=128*(r*v) := by norm_num
    have hdivN : 128∣43*t-1 := by
      rw [hpow]
      exact hdiv
    have hmod0 : (43*t-1)%128=0 :=
      Nat.mod_eq_zero_of_dvd hdivN
    omega
  have hqcases : q=0 ∨ q=1 ∨ q=2 := by omega
  rcases hqcases with hq0 | hq1 | hq2
  · have hUeq : U=32*R := by
      have hU : U=43*t-1 := by
        simpa [hq0] using hpow.symm
      rw [hN] at hU
      exact hU
    have hV : U/2=16*R := by
      rw [hUeq]
      omega
    have hvq0 : (U/2+q)%4=0 := by
      rw [hq0,hV]
      omega
    have hcost0 : 2*k+32*R=128*t-8 := by
      simpa [hq0,hUeq] using hcost
    have hk8 : k%8=4 := by
      rw [ht,hR] at hcost0
      omega
    rcases hnot0k4 with hbad | hbad <;> omega
  · have hUeq : U=8*R := by
      have hpow' : 4*U=43*t-1 := by
        simpa [hq1] using hpow
      rw [hN] at hpow'
      omega
    have hcost1 : 2*k+U+6=128*t-8 := by
      simpa [hq1] using hcost
    have hq1bad := q1_parent_not_reach_t99 t n R U k ht hR hUeq hcost1
    have hreach' : BB6CLine.Reach (U-2,k,0) := by
      simpa [ha] using hline
    exact hq1bad hreach'
  · have hUeq : U=2*R := by
      have hpow' : 16*U=43*t-1 := by
        simpa [hq2] using hpow
      rw [hN] at hpow'
      omega
    have hV : U/2=R := by
      rw [hUeq]
      omega
    have hvq3 : (U/2+q)%4=3 := by
      rw [hq2,hV,hR]
      omega
    exact hnot3 hvq3

/-- The q=0 y=3 predecessor on w=37 (mod 128) is unreachable
    without the M16 quotient: its two-step pullback is X_t, and
    the complete original-source q-fan is excluded by CRange/CBack. -/
theorem blank_no_u5_q0_parent_w37 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%128=37)
    (ht : 1≤t)
    (hparent : CReach (64*t+5) (32*t+3)) : False := by
  have hX := q0_parent_reach_implies_X t ht hparent
  have htmod := BB6.Agent3U5M16Residual.u5_m8_t_mod128_w37
    w s m t hs hm hp hw
  obtain ⟨n,hn⟩ : ∃ n, t=128*n+99 := by
    refine ⟨t/128,?_⟩
    omega
  exact q0_X_not_reach_t99 t n hn hX


#print axioms q0_X_not_reach_t19
#print axioms blank_no_u5_q0_parent_w21
#print axioms zero_left_26_not_reach
#print axioms q0_X_not_reach_t99
#print axioms blank_no_u5_q0_parent_w37

end BB6.Agent3U5CLineResidualClosure
