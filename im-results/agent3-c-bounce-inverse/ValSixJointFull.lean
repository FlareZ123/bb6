import ValSixJointM1
import JointFiveSieve
import AffineFourGlobal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix

/-- Low parameters after merging Agent11's two source-certified
    exclusions with the Agent3 low stopping criterion. -/
def lowAllowedValSixFull (m : Nat) : Prop :=
  BB6.Agent11Joint.lowAllowed m

/-- Complete currently known high-parameter sieve: Agent29's four
    mod-128 families and Agent3's three valuation-six families are in
    highAllowedValSixThree; Agent11's two missing-image families and
    Agent19's sum-seven four-link family are in Agent19Five.highAllowed;
    the final condition removes every affine-normalized right-four
    candidate. -/
def highAllowedValSixFull (j m : Nat) : Prop :=
  highAllowedValSixThree j m ∧
  BB6.Agent19Five.highAllowed j m ∧
  (BB6.Agent15.affineNormalize (2*j+3)
    (2^(2*m+2)*(j+3)-(j+3*m+5))).2 ≠ 4

private theorem low_bound_full (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_score_nonnegative_full (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

/-- Lossless original-source Machine C halting criterion after merging
    every currently certified low/high parameter restriction used by
    Agents 3, 11, 19, and 29, plus the general affine terminal-right-four
    exclusion. The fixed-target root decision is exact; the remaining
    parameter existentials are unbounded and undecided. -/
theorem blank_halts_iff_joint_val_six_full :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedValSixFull m ∧
        valSixMixedRootDecision 1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedValSixFull j m ∧
        valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [blank_halts_iff_joint_val_six_fast]
  constructor
  · rintro (⟨m,hlow,hroot⟩ | ⟨j,m,hhigh,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (valSixMixedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (low_bound_full m)
        omega
      have hnon1 : m%4≠1 := by
        intro hm
        exact (BB6.Agent11Low.blank_no_low_m_one_mod_four
          m k hm hstop).2 hr
      have hnon2 : m%16≠7 := by
        intro hm
        exact (BB6.Agent11Low.blank_no_low_m_seven_mod16
          m k hm hstop).2 hr
      exact Or.inl ⟨m,⟨hlow,hnon1,hnon2⟩,hroot⟩
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_score_nonnegative_full j m)
        omega
      have hbase : BB6.Agent19Joint.highAllowed j m := hhigh.1.1.1
      have hnon1 : (j+m)%4≠0 := by
        intro hjm
        exact (BB6.Agent11High.blank_no_high_jplusm_zero_modfour
          j m k hjm hstop).2 hr
      have hnon2 :
          ¬(2≤m ∧ (j+m)%16=6 ∧ m%4≠1) := by
        rintro ⟨hm,hjm,hm4⟩
        exact (BB6.Agent11High.blank_no_high_jplusm_six_mod16
          j m k hm hjm hm4 hstop) hr
      have h11 : BB6.Agent11Joint.highAllowed j m := by
        unfold BB6.Agent11Joint.highAllowed
        exact ⟨hbase,hnon1,hnon2⟩
      have hfourlink :
          ¬(m%16=10 ∧ (j+3*m+19)%64=0) := by
        rintro ⟨hm,hpair⟩
        exact BB6.Agent19Four.blank_no_high_fourlink
          j m k hm hpair hstop hr
      have h19 : BB6.Agent19Five.highAllowed j m := by
        unfold BB6.Agent19Five.highAllowed
        exact ⟨h11,hfourlink⟩
      have hr15 : BB6.Agent15.CReach (2*j+3) k := hr
      have hright4 :
          (BB6.Agent15.affineNormalize (2*j+3) k).2≠4 := by
        intro hfour
        have hclass :=
          (BB6.Agent29Bottom.blank_affine_four_odd_iff
            (2*j+3) k (by omega) hfour).mp hr15
        have hk7 := BB6.Agent15.second_halt_k_ge_seven j m k hstop
        omega
      exact Or.inr ⟨j,m,⟨hhigh,h19,hright4⟩,hroot⟩
  · rintro (⟨m,hallow,hroot⟩ |
      ⟨j,m,⟨hhigh,_,_⟩,hroot⟩)
    · exact Or.inl ⟨m,hallow.1,hroot⟩
    · exact Or.inr ⟨j,m,hhigh,hroot⟩

/-- The explicit m=1 tower is admitted by both prior high sieves,
    including Agent11's extra restrictions and Agent19's four-link
    family, before the affine terminal-right-four exclusion is applied. -/
theorem second_one_family_previous_sieves (r : Nat) :
    highAllowedValSixThree (BB6.Agent29Depth.secondOneJ r) 1 ∧
    BB6.Agent19Five.highAllowed (BB6.Agent29Depth.secondOneJ r) 1 := by
  have h3 := second_one_family_previously_allowed r
  have hbase : BB6.Agent19Joint.highAllowed
      (BB6.Agent29Depth.secondOneJ r) 1 := h3.1.1.1
  have hmod := BB6.Agent29Depth.secondOneJ_mod32 r
  have h11 : BB6.Agent11Joint.highAllowed
      (BB6.Agent29Depth.secondOneJ r) 1 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨hbase, by omega, by omega⟩
  have h19 : BB6.Agent19Five.highAllowed
      (BB6.Agent29Depth.secondOneJ r) 1 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11, by omega⟩
  exact ⟨h3,h19⟩

/-- The prior-admitted infinite m=1 tower is removed by the general
    affine terminal-right-four predicate. -/
theorem second_one_family_removed_by_affine_four (r : Nat) :
    ¬ highAllowedValSixFull (BB6.Agent29Depth.secondOneJ r) 1 := by
  intro h
  have hstop := BB6.Agent29Depth.second_one_family_stopping r
  have hpow : (2:Nat)^(2*1+2)=16 := by decide
  have hk :
      (2:Nat)^(2*1+2)*(BB6.Agent29Depth.secondOneJ r+3) -
        (BB6.Agent29Depth.secondOneJ r+3*1+5) =
      15*BB6.Agent29Depth.secondOneJ r+40 := by
    rw [hpow] at hstop ⊢
    omega
  have hfour :
      (BB6.Agent15.affineNormalize
        (2*BB6.Agent29Depth.secondOneJ r+3)
        (2^(2*1+2)*(BB6.Agent29Depth.secondOneJ r+3) -
          (BB6.Agent29Depth.secondOneJ r+3*1+5))).2=4 := by
    simpa [hk] using
      BB6.Agent29Depth.second_one_family_normalizes_four r
  exact h.2.2 hfour

#print axioms blank_halts_iff_joint_val_six_full
#print axioms second_one_family_previous_sieves
#print axioms second_one_family_removed_by_affine_four

end BB6.Agent3ValSix
