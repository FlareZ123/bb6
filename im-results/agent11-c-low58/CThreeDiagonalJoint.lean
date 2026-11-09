import ValSixC58
import CThreeDiagonal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Diagonal

/-- A forced affine predecessor of a right counter divisible by four
    terminates after at most one normalization step at an odd right
    counter. Thus it cannot normalize to right counter four. -/
theorem norm_right_ne_four (a k : Nat)
    (hk : 8 ≤ k) (hk4 : k%4=0) :
    (BB6.Agent15.affineNormalize a k).2 ≠ 4 := by
  by_cases hc : 4≤k ∧ k%2=0 ∧ (a+k)%4=1
  · have hn : ¬(4≤(k-2)/2 ∧ ((k-2)/2)%2=0 ∧
      ((a+k-2)+((k-2)/2))%4=1) := by omega
    rw [BB6.Agent15.affineNormalize, dif_pos hc,
      BB6.Agent15.affineNormalize, dif_neg hn]
    omega
  · rw [BB6.Agent15.affineNormalize, dif_neg hc]
    omega

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

private theorem diagonal_stop_k_mod_four (j m k : Nat)
    (hj : j%2=1) (hd : m%32=(j+25)%32)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : k%4=0 := by
  have hpow : 4 ∣ (2:Nat)^(2*m+2) := by
    have h : (2:Nat)^2 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hprod : 4 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    rcases hpow with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hzero : (k+j+3*m+5)%4=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod
  omega

/-- Every parameter in Agent4's full diagonal exclusion was admitted
    by the preceding Agent3/11/19/29 joint original-root criterion,
    including its recursive affine-terminal-right-four test. -/
theorem prior_high_admits_diagonal (j m : Nat)
    (hm : 4≤m) (hj : j%2=1)
    (hd : m%32=(j+25)%32) :
    BB6.Agent11C58ValSix.highAllowed j m := by
  have hbase : BB6.Agent3.jointHighAllowed j m := by
    unfold BB6.Agent3.jointHighAllowed
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase,by omega⟩
  have hdy : ∀ n, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hx⟩
    by_cases hn : n%2=0
    · simp [hn] at hx
      omega
    · simp [hn] at hx
      omega
  have h19 : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    exact ⟨hrect,hdy,by omega,by omega,by omega,by omega⟩
  have h29 : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hval : BB6.Agent3ValSix.highAllowedValSixThree j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨h29,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by omega,by omega⟩
  have hf : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
    dsimp [k]
    have hc := Nat.sub_add_cancel (high_bound j m)
    omega
  have hk4 : k%4=0 := diagonal_stop_k_mod_four j m k hj hd hstop
  have hk7 : 7≤k := BB6.Agent15.second_halt_k_ge_seven j m k hstop
  have hnorm : (BB6.Agent15.affineNormalize (2*j+3) k).2≠4 :=
    norm_right_ne_four (2*j+3) k (by omega) hk4
  have hfull : BB6.Agent3ValSix.highAllowedValSixFull j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hval,hf,by omega,by omega,by omega,hnorm⟩
  unfold BB6.Agent11C58ValSix.highAllowed
  exact ⟨hfull,by omega⟩

/-- Strictly stronger high parameter domain: remove the source-excluded
    entire odd diagonal while retaining all previous C58/ValSix gates. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11C58ValSix.highAllowed j m ∧
  ¬(4≤m ∧ j%2=1 ∧ m%32=(j+25)%32)

/-- Original Machine C blank halting iff the exact low or high
    fixed-target evaluator succeeds with all previous restrictions and
    the now source-excluded infinite diagonal removed. -/
theorem blank_halts_iff_diagonal :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11C58ValSix.blank_halts_iff_joint_val_six_c58]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      obtain ⟨time,ht⟩ := hr
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound j m)
        omega
      have hnot : ¬(4≤m ∧ j%2=1 ∧ m%32=(j+25)%32) := by
        rintro ⟨hm,hj,hd⟩
        exact (BB6.Agent4Three.high_stop_odd_diagonal_mod32
          j m k time hm hj hd hstop) ht
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- All diagonal parameters of sufficiently large m are strict
    exclusions of this genuinely stronger all-time criterion. -/
theorem diagonal_strict (j m : Nat)
    (hm : 4≤m) (hj : j%2=1)
    (hd : m%32=(j+25)%32) :
    BB6.Agent11C58ValSix.highAllowed j m ∧ ¬ highAllowed j m := by
  refine ⟨prior_high_admits_diagonal j m hm hj hd,?_⟩
  intro h
  exact h.2 ⟨hm,hj,hd⟩

#print axioms norm_right_ne_four
#print axioms diagonal_stop_k_mod_four
#print axioms prior_high_admits_diagonal
#print axioms blank_halts_iff_diagonal
#print axioms diagonal_strict
end BB6.Agent11Diagonal
