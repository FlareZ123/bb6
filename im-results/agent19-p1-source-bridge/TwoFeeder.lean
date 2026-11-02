import GDepth
import ResidualGateway
import EvenFamily

namespace BB6.Agent19.TwoFeeder

open BB6.HaltingFunnel (BlankReach T G T_odd_left_predecessor blank_even_hub_power)
open BB6.Agent19.Depth (ThreeShape G_preimages_mod8_four)
open BB6.Agent19.P1 (last_predecessor)

/-- A reachable odd-left, positive-right hub must have an earlier
    reachable even-left predecessor through the two-cell reduction. -/
theorem odd_positive_predecessor (a c:Nat) (ha:a%2=1) (hc:0<c)
    (hr:BlankReach a c) :
    ∃ u v, BlankReach u v ∧ u%2=0 ∧ a=u+3 ∧ c=v-2 := by
  obtain ⟨u,v,hu,hstep⟩ := last_predecessor a c hr (Or.inl (by omega))
  rcases T_odd_left_predecessor u v a c hstep ha with h | h
  · omega
  · obtain ⟨heven,hbound,hleft,hright⟩ := h
    exact ⟨u,v,hu,heven,hleft,hright⟩

/-- The c=3 branch cannot enter a 4K+4,3 hub when K is 2 modulo 8. -/
theorem G_no_one_input (K k:Nat) (hK:K%4=2) :
    G k 1 ≠ (4*K+4,3) := by
  intro h
  have hmod : (3+(4*K+4)/2+3)%8=4 := by omega
  have hs := (G_preimages_mod8_four (4*K+4) 3 k 1 (by omega) hmod).mp h
  obtain ⟨K',hb,hs⟩ := hs
  have hK' : K'=K := by omega
  subst K'
  rcases hs with ⟨hk,hc⟩ | ⟨hc,hk⟩ | ⟨hc,hk⟩ <;> omega

/-- Any incoming edge to a large positive even-left 3-hub must be
    the odd-left long-c branch, permitting exact algebraic inversion. -/
theorem T_to_K_three (K a c:Nat) (hK:K%4=2)
    (ht:T a c=some (4*K+4,3)) :
    a%2=1 ∧ 4≤c ∧ G (a/2+1) (c-2)=(4*K+4,3) := by
  by_cases h0:c=0
  · subst c
    simp [T] at ht
  · by_cases h1:c=1
    · subst c
      simp [T] at ht
    · by_cases ha:a%2=0
      · have hbranch : T a c=some (a+3,c-2) := by
          simp [T,h0,h1,ha]
        obtain ⟨hleft,hright⟩ :=
          Prod.mk.inj (Option.some.inj (hbranch.symm.trans ht))
        omega
      · by_cases h2:c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3:c=3
          · subst c
            have hbranch : T a 3=some (G (a/2) 1) := by
              simp [T,ha]
            have hh := Option.some.inj (hbranch.symm.trans ht)
            exact False.elim (G_no_one_input K (a/2) hK hh)
          · have hbranch : T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hresult := Option.some.inj (hbranch.symm.trans ht)
            have haodd : a%2=1 := by omega
            have hc4 : 4≤c := by omega
            exact ⟨haodd,hc4,hresult⟩

/-- A third recursive inverse branch is globally forbidden by the
    all-time even-left modular invariant. Hence exactly two explicit
    second-level feeder families remain for all K congruent 2 mod 8. -/
theorem reachable_two_feeders (K:Nat) (hK:K%4=2)
    (hr:BlankReach (4*K+4) 3) :
    BlankReach (2*K-4) (2*K+9) ∨
    BlankReach (3*K-2) (K+5) := by
  obtain ⟨a,c,hr0,ht⟩ := last_predecessor (4*K+4) 3 hr (Or.inr (by decide))
  obtain ⟨haodd,hc4,hG⟩ := T_to_K_three K a c hK ht
  have hmod : (3+(4*K+4)/2+3)%8=4 := by omega
  have hshape := (G_preimages_mod8_four (4*K+4) 3 (a/2+1) (c-2) (by omega) hmod).mp hG
  obtain ⟨K',hb,hs⟩ := hshape
  have hk : K'=K := by omega
  subst K'
  obtain ⟨u,v,hu,heven,haEq,hcEq⟩ :=
    odd_positive_predecessor a c haodd (by omega) hr0
  rcases hs with ⟨hkg,hcg⟩ | ⟨hcG,hkg⟩ | ⟨hcG,hkg⟩
  · left
    have huEq:u=2*K-4 := by omega
    have hvEq:v=2*K+9 := by omega
    simpa [huEq,hvEq] using hu
  · right
    have huEq:u=3*K-2 := by omega
    have hvEq:v=K+5 := by omega
    simpa [huEq,hvEq] using hu
  · obtain ⟨j,hpow⟩ := blank_even_hub_power u v hu (by omega) (by omega) heven
    let m:=K/4
    have hK : K=4*m+2 := by dsimp[m]; omega
    have huval : u=14*m+6 := by omega
    have hcontradiction : 14*m+18=14*2^j := by omega
    omega

theorem high_power_mod16 (n:Nat) (hn:4≤n) : (2^n)%16=0 := by
  have he : n=n-4+4 := by omega
  rw [he,Nat.pow_add]
  simp

/-- Infinite-family specialization to the unresolved critical indices
    n=16q+2, q>=1. Exactly two explicitly computed even-sector
    antecedent families need be excluded to decide these targets. -/
theorem critical_residual_two_feeders (n:Nat) (hn:10≤n) (hmod:n%8=2)
    (hr:BlankReach (14*2^n-2*n-16) 3) :
    ∃ K, 14*2^n-2*n-16=4*K+4 ∧
      (BlankReach (2*K-4) (2*K+9) ∨
       BlankReach (3*K-2) (K+5)) := by
  let b:=14*2^n-2*n-16
  have hpow:=BB6.Agent19.Depth.pow_bound n
  have hp16:=high_power_mod16 n (by omega)
  have hbig : 4≤b := by dsimp [b]; omega
  have hmod16 : b%16=12 := by dsimp [b]; omega
  let K:=(b-4)/4
  have hbval : b=4*K+4 := by dsimp [K]; omega
  have hK:K%4=2 := by omega
  refine ⟨K,hbval,?_⟩
  exact reachable_two_feeders K hK (by simpa [b,hbval] using hr)


/-- Each of the two permitted even-sector feeders actually reaches the
    odd-counter target in exactly two accelerated transitions. -/
theorem first_feeder_to_target (K:Nat) (hK:K%4=2)
    (hr:BlankReach (2*K-4) (2*K+9)) :
    BlankReach (4*K+4) 3 := by
  have hKbound : 2≤K := by omega
  have heven : (2*K-4)%2=0 := by omega
  have hstep1 : T (2*K-4) (2*K+9) = some (2*K-1,2*K+7) := by
    simp [T,heven]
    omega
  have hGshape : ThreeShape (4*K+4) 3 K (2*K+5) := by
    refine ⟨K,rfl,Or.inl ⟨rfl,by omega⟩⟩
  have hm : (3+(4*K+4)/2+3)%8=4 := by omega
  have hG : G K (2*K+5)=(4*K+4,3) :=
    (G_preimages_mod8_four (4*K+4) 3 K (2*K+5) (by omega) hm).mpr hGshape
  have hstep2 : T (2*K-1) (2*K+7) = some (4*K+4,3) := by
    have hpar : (2*K-1)%2=1 := by omega
    have hk : (2*K-1)/2+1=K := by omega
    simpa [T, hpar, hk, hG, show 2*K+7-2=2*K+5 by omega]
  exact BlankReach.next (2*K-1) (2*K+7) (4*K+4) 3
    (BlankReach.next (2*K-4) (2*K+9) (2*K-1) (2*K+7) hr hstep1) hstep2

theorem second_feeder_to_target (K:Nat) (hK:K%4=2)
    (hr:BlankReach (3*K-2) (K+5)) :
    BlankReach (4*K+4) 3 := by
  have hKbound : 2≤K := by omega
  have heven : (3*K-2)%2=0 := by omega
  have hstep1 : T (3*K-2) (K+5) = some (3*K+1,K+3) := by
    simp [T,heven]
    omega
  have hk : (3*K+1)/2+1=K+(K+1)/2+1 := by omega
  have hGshape : ThreeShape (4*K+4) 3 (K+(K+1)/2+1) (K+1) := by
    refine ⟨K,rfl,Or.inr (Or.inl ⟨by omega,rfl⟩)⟩
  have hm : (3+(4*K+4)/2+3)%8=4 := by omega
  have hG : G (K+(K+1)/2+1) (K+1)=(4*K+4,3) :=
    (G_preimages_mod8_four (4*K+4) 3 (K+(K+1)/2+1) (K+1) (by omega) hm).mpr hGshape
  have hstep2 : T (3*K+1) (K+3) = some (4*K+4,3) := by
    have hpar : (3*K+1)%2=1 := by omega
    have hnzero : K≠0 := by omega
    simpa [T, hpar, hk, hG, hnzero, show K+3-2=K+1 by omega,
      show K+3 ≠3 by omega]
  exact BlankReach.next (3*K+1) (K+3) (4*K+4) 3
    (BlankReach.next (3*K-2) (K+5) (3*K+1) (K+3) hr hstep1) hstep2

/-- Exact two-family equivalence at all residual K=2(mod8): this is
    fully quantified over all finite times and the real blank orbit. -/
theorem reach_two_feeders_iff (K:Nat) (hK:K%4=2) :
    BlankReach (4*K+4) 3 ↔
    BlankReach (2*K-4) (2*K+9) ∨ BlankReach (3*K-2) (K+5) := by
  constructor
  · exact reachable_two_feeders K hK
  · intro h
    rcases h with h | h
    · exact first_feeder_to_target K hK h
    · exact second_feeder_to_target K hK h

#print axioms BB6.Agent19.TwoFeeder.reach_two_feeders_iff

#print axioms BB6.Agent19.TwoFeeder.T_to_K_three
#print axioms BB6.Agent19.TwoFeeder.reachable_two_feeders
#print axioms BB6.Agent19.TwoFeeder.critical_residual_two_feeders
end BB6.Agent19.TwoFeeder
