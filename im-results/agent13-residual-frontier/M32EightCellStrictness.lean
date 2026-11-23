import CThreeSixM32Integration
import HighDyadicOlderGateFast
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace BB6.Agent13M32Integration

private theorem v2_one_of_mod4_two (N : Nat) (hN : N%4=2) :
    BB6.Agent11FastDepthGate.v2 N = 1 := by
  have hform : N = 2*(2*(N/4)+1) := by
    have h := Nat.mod_add_div N 4
    rw [hN] at h
    omega
  have hodd : (2*(N/4)+1)%2=1 := by omega
  have hpos : 0 < 2*(N/4)+1 := by omega
  calc
    BB6.Agent11FastDepthGate.v2 N =
        BB6.Agent11FastDepthGate.v2 (2*(2*(N/4)+1)) :=
      congrArg BB6.Agent11FastDepthGate.v2 hform
    _ = BB6.Agent11FastDepthGate.v2 (2*(N/4)+1)+1 :=
      BB6.Agent11FastDepthGate.v2_two_mul _ hpos
    _ = 1 := by
      rw [BB6.Agent11FastDepthGate.v2_odd _ hodd]

private theorem high_bound_eight (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

theorem sixForced_not_excluded_eight
    (j m k : Nat) (hm : 2≤m) (hjr : j%4=0)
    (hmr : m%32=(3*j+13)%32)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent11SixForced.sixForcedExcluded (2*j+3) k = false := by
  have hpow : 8 ∣ 2^(2*m+2) := by
    have hp : 2^3 ∣ 2^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^3=8 by decide] using hp
  have hprod : 8 ∣ 2^(2*m+2)*(j+3) := by
    rcases hpow with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    simp [Nat.mul_assoc]
  have hP : (2^(2*m+2)*(j+3))%8=0 :=
    Nat.mod_eq_zero_of_dvd hprod
  have hj8 : j%8=0 ∨ j%8=4 := by omega
  have hm8 : (j%8=0 ∧ m%8=5) ∨ (j%8=4 ∧ m%8=1) := by
    rcases hj8 with h0 | h4
    · have hm5 : m%8=5 := by omega
      exact Or.inl ⟨h0,hm5⟩
    · have hm1 : m%8=1 := by omega
      exact Or.inr ⟨h4,hm1⟩
  have hB : (j+3*m+5)%8=4 := by
    rcases hm8 with ⟨hJ,hM⟩ | ⟨hJ,hM⟩ <;> omega
  have hk8 : k%8=4 := by
    have hsum : (k+j+3*m+5)%8=0 := by
      rw [hstop]
      exact hP
    omega
  have hx8 : (2*j+3)%8=3 := by omega
  have hx16 : (2*j+3)%16 ≠ 5 := by
    rcases hj8 with h0 | h4 <;> omega
  have hsum8 : ((2*j+3)+k)%8=7 := by omega
  have hsum4 : ((2*j+3)+k)%4=3 := by omega
  have hkeven : k%2=0 := by omega
  have hxodd : (2*j+3)%2=1 := by omega
  simp [BB6.Agent11SixForced.sixForcedExcluded,
    BB6.Agent11SixForced.sixForcedNormalize,
    BB6.Agent3.oddLowGate,
    BB6.Agent3.evenSevenGate,
    BB6.Agent3.evenAffineGate,
    BB6.Agent46.sixEvenRightGate,
    BB6.Agent3ValSix.valSixGate,
    BB6.Agent11SixForced.evenOddFourGate,
    hx8,hx16,hsum8,hsum4,hkeven,hxodd]

theorem prior_high_allowed_eight
    (j m : Nat) (hj : 3≤j) (hm : 2≤m)
    (hjr : j%4=0) (hmr : m%32=(3*j+13)%32) :
    BB6.Agent11SixCriterion.highAllowed j m := by
  have hm4 : m%4=1 := by omega
  have hD4 : (j+3*m+3)%4=2 := by omega
  have hD2odd : (j+9*m+14)%2=1 := by omega
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
    dsimp [k]
    have hc := Nat.sub_add_cancel (high_bound_eight j m)
    omega
  have hk8 : 8≤k :=
    CCert.high_gateway_k_ge_eight j m k (by omega) hstop
  have hpow4 : 4 ∣ 2^(2*m+2) := by
    have hp : 2^2 ∣ 2^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^2=4 by decide] using hp
  have hprod4 : 4 ∣ 2^(2*m+2)*(j+3) := by
    rcases hpow4 with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    simp [Nat.mul_assoc]
  have hP4 : (2^(2*m+2)*(j+3))%4=0 :=
    Nat.mod_eq_zero_of_dvd hprod4
  have hB4 : (j+3*m+5)%4=0 := by omega
  have hsum4 : (k+j+3*m+5)%4=0 := by
    rw [hstop]
    exact hP4
  have hk4 : k%4=0 := by omega
  have hKplus4 : (k+2)%4=2 := by omega
  have hstopk : BB6.Agent11LateDepthGate.stopK j m = k := by
    rfl
  have hOlderNo : ∀ n, ¬ BB6.Agent11OlderGateFast.gate n j m := by
    intro n hn
    rcases hn with ⟨_,hres,_⟩
    have hv := BB6.Agent11OlderGateFast.v2_of_older_residue j m n hres
    have hV := v2_one_of_mod4_two (j+3*m+3) hD4
    rw [hV] at hv
    omega
  have hFast : BB6.Agent11FastDepthGate.candidateAllowedBool j m = true := by
    have hv := BB6.Agent11FastDepthGate.v2_odd (j+9*m+14) hD2odd
    simp [BB6.Agent11FastDepthGate.candidateAllowedBool,
      BB6.Agent11FastDepthGate.candidateDepth,hv]
  have hLateNo : ∀ r, ¬ BB6.Agent11LateDepthGate.gate r j m := by
    intro r hr
    rcases hr with ⟨hr2,_,_,hres,_⟩
    have hv := BB6.Agent11LateDepthGate.v2_of_late_residue
      (BB6.Agent11LateDepthGate.stopK j m) r hres
    have hV := v2_one_of_mod4_two (k+2) hKplus4
    rw [hstopk,hV] at hv
    omega
  have hLate : BB6.Agent11LateDepthGate.allowedBool j m = true :=
    (BB6.Agent11LateDepthGate.allowedBool_iff j m).2 hLateNo
  have hRect : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    refine ⟨?_,?_⟩
    · unfold BB6.Agent3.jointHighAllowed
      refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
    · omega
  have h19 : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    exact ⟨hRect,hOlderNo,by omega,by omega,by omega,by omega⟩
  have h11Joint : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by omega,by omega⟩
  have h19Five : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11Joint,by omega⟩
  have h29 : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hValSix : BB6.Agent3ValSix.highAllowedValSix j m := by
    unfold BB6.Agent3ValSix.highAllowedValSix
    exact ⟨h29,by omega,by omega⟩
  have hValSixThree : BB6.Agent3ValSix.highAllowedValSixThree j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
    exact ⟨hValSix,by omega⟩
  have hValSixFull : BB6.Agent3ValSix.highAllowedValSixFull j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hValSixThree,h19Five,by omega,by omega,by omega,
      BB6.Agent11Diagonal.norm_right_ne_four (2*j+3) k hk8 hk4⟩
  have hC58ValSix : BB6.Agent11C58ValSix.highAllowed j m := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hValSixFull,by omega⟩
  have hC58Bool : BB6.Agent11C58Boolean.highAllowed j m := by
    unfold BB6.Agent11C58Boolean.highAllowed
    exact ⟨hC58ValSix,hFast⟩
  have hLateFast : BB6.Agent11LateFastWrapper.highAllowed j m := by
    unfold BB6.Agent11LateFastWrapper.highAllowed
    exact ⟨hC58Bool,hLate⟩
  have hDiagLate : BB6.Agent11DiagonalLate.highAllowed j m := by
    unfold BB6.Agent11DiagonalLate.highAllowed
    exact ⟨hLateFast,by omega⟩
  have hDiagM0 : BB6.Agent11DiagonalM0.highAllowed j m := by
    unfold BB6.Agent11DiagonalM0.highAllowed
    exact ⟨hDiagLate,by omega⟩
  have hM0Deep : BB6.Agent11M0DeepFull.highAllowed j m := by
    unfold BB6.Agent11M0DeepFull.highAllowed
    exact ⟨hDiagM0,by omega⟩
  unfold BB6.Agent11SixCriterion.highAllowed
  exact ⟨hM0Deep,
    sixForced_not_excluded_eight j m k hm hjr hmr hstop⟩

private theorem high_pair_good_eight
    (j m : Nat) (hjr : j%4=0)
    (hmr : m%32=(3*j+13)%32) :
    CCert.highPairGood (j%32) (m%32) := by
  have hj32 : j%32=0 ∨ j%32=4 ∨ j%32=8 ∨ j%32=12 ∨
      j%32=16 ∨ j%32=20 ∨ j%32=24 ∨ j%32=28 := by omega
  have hmem : (j%32,m%32) ∈ CCert.newHighPairs := by
    rcases hj32 with h0|h4|h8|h12|h16|h20|h24|h28
    · have hm13 : m%32=13 := by omega
      simp [CCert.newHighPairs,h0,hm13]
    · have hm25 : m%32=25 := by omega
      simp [CCert.newHighPairs,h4,hm25]
    · have hm5 : m%32=5 := by omega
      simp [CCert.newHighPairs,h8,hm5]
    · have hm17 : m%32=17 := by omega
      simp [CCert.newHighPairs,h12,hm17]
    · have hm29 : m%32=29 := by omega
      simp [CCert.newHighPairs,h16,hm29]
    · have hm9 : m%32=9 := by omega
      simp [CCert.newHighPairs,h20,hm9]
    · have hm21 : m%32=21 := by omega
      simp [CCert.newHighPairs,h24,hm21]
    · have hm1 : m%32=1 := by omega
      simp [CCert.newHighPairs,h28,hm1]
  exact of_decide_eq_true
    ((List.all_eq_true.mp CCert.newHighPairs_excluded)
      (j%32,m%32) hmem)

theorem m32_eight_cell_strict
    (j m : Nat) (hj : 3≤j) (hm : 2≤m)
    (hjr : j%4=0) (hmr : m%32=(3*j+13)%32) :
    BB6.Agent11SixCriterion.highAllowed j m ∧
      ¬ highAllowedM32 j m := by
  have hprior := prior_high_allowed_eight j m hj hm hjr hmr
  have hgood := high_pair_good_eight j m hjr hmr
  refine ⟨hprior,?_⟩
  intro h
  exact (h.2 ⟨hj,hm⟩) hgood

#print axioms m32_eight_cell_strict
end BB6.Agent13M32Integration
