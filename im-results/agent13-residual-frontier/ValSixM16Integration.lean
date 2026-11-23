import ValSixJointFull
import M32SectionEmbedding
import CSourceBridge16
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13M16Integration

/-- A genuine blank-origin Machine C section point embeds in the unchanged
    three-counter CLine orbit, then in the kernel-checked M16 quotient.
    This is a necessary condition for *every* source-reachable section
    state, not only the hand-selected low/high progressions. -/
theorem cReach_implies_m16_seen (a k : Nat)
    (hr : BB6.Agent3.CReach a k) :
    CCert.seen (CCert.q a) (CCert.q k) (CCert.q 0) = true := by
  have hr15 : BB6.Agent15.CReach a k := by
    simpa [BB6.Agent3.CReach, BB6.Agent15.CReach] using hr
  have hline : BB6CLine.Reach (a,k,0) :=
    BB6.Agent15.m32_section_reach_embeds hr15
  have hcert := CCert.source_reachable_embeds16 hline
  exact CCert.reachable_seen hcert

/-- The exact ValSix low stopping family, filtered by the complete M16
    quotient's necessary seen condition. -/
def lowAllowedValSixM16 (m : Nat) : Prop :=
  BB6.Agent3ValSix.lowAllowedValSixFull m ∧
    CCert.seen (CCert.q 1)
      (CCert.q (2^(2*m+3)-(3*m+4))) (CCert.q 0) = true

/-- The exact ValSix high stopping family, filtered by the complete M16
    quotient's necessary seen condition. -/
def highAllowedValSixM16 (j m : Nat) : Prop :=
  BB6.Agent3ValSix.highAllowedValSixFull j m ∧
    CCert.seen (CCert.q (2*j+3))
      (CCert.q (2^(2*m+2)*(j+3)-(j+3*m+5))) (CCert.q 0) = true

/-- Lossless Machine C halting criterion with the complete M16 quotient
    condition attached to both stopping branches. The quotient predicate
    is a cheap finite-state necessary filter; the exact root decision and
    the unbounded parameter existentials are retained unchanged. -/
theorem blank_halts_iff_joint_val_six_m16 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedValSixM16 m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedValSixM16 j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent3ValSix.blank_halts_iff_joint_val_six_full]
  constructor
  · rintro (⟨m,hallow,hroot⟩ | ⟨j,m,hallow,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff 1 k).mp hroot
      have hs := cReach_implies_m16_seen 1 k hr
      exact Or.inl ⟨m,⟨hallow,hs⟩,hroot⟩
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hs := cReach_implies_m16_seen (2*j+3) k hr
      exact Or.inr ⟨j,m,⟨hallow,hs⟩,hroot⟩
  · rintro (⟨m,⟨hallow,_⟩,hroot⟩ |
      ⟨j,m,⟨hallow,_⟩,hroot⟩)
    · exact Or.inl ⟨m,hallow,hroot⟩
    · exact Or.inr ⟨j,m,hallow,hroot⟩

/-- The progression m=3, j=8r+6 survives the existing complete
    ValSix high parameter sieve. This makes the M16 rejection below a
    strict improvement to that explicit sieve, not a restatement. -/
theorem high_m16_family_survives_old_sieve (r : Nat) :
    BB6.Agent3ValSix.highAllowedValSixFull (8*r+6) 3 := by
  let j := 8*r+6
  have hbase : BB6.Agent3.jointHighAllowed j 3 := by
    unfold BB6.Agent3.jointHighAllowed
    dsimp [j]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j 3 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase,by dsimp [j]; omega⟩
  have hdy : ∀ n, ¬(n+4≤2*3+2 ∧
      (j+3*3+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,hres,_⟩
    have hres' : (j+12)%(2:Nat)^(n+4)=(2:Nat)^(n+2) := by
      simpa using hres
    have hp4 : (2:Nat)^2 ∣ (2:Nat)^(n+4) :=
      Nat.pow_dvd_pow 2 (by omega)
    have hdiv4 : 4 ∣ (2:Nat)^(n+4) := by
      simpa only [show (2:Nat)^2=4 by decide] using hp4
    have hmod := Nat.mod_mod_of_dvd (j+12) hdiv4
    rw [hres'] at hmod
    have hp4' : (2:Nat)^2 ∣ (2:Nat)^(n+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    have hdiv4' : 4 ∣ (2:Nat)^(n+2) := by
      simpa only [show (2:Nat)^2=4 by decide] using hp4'
    have hpowmod : (2:Nat)^(n+2)%4=0 :=
      Nat.mod_eq_zero_of_dvd hdiv4'
    rw [hpowmod] at hmod
    have hzero : (j+12)%4=0 := hmod.symm
    dsimp [j] at hzero
    omega
  have h19 : BB6.Agent19Joint.highAllowed j 3 := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨hrect,hdy,?_,?_,?_,?_⟩ <;> dsimp [j] <;> omega
  have h29 : BB6.Agent29Joint.highAllowedPlus j 3 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hval : BB6.Agent3ValSix.highAllowedValSixThree j 3 := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨h29,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j 3 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by dsimp [j]; omega,by dsimp [j]; omega⟩
  have hfive : BB6.Agent19Five.highAllowed j 3 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  let k := 2^(2*3+2)*(j+3)-(j+3*3+5)
  have hk : k=2040*r+2284 := by
    dsimp [k,j]
    norm_num
    omega
  have hguard : ¬(4≤k ∧ k%2=0 ∧ ((2*j+3)+k)%4=1) := by
    rw [hk]
    dsimp [j]
    omega
  have hnorm : BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
    simp [BB6.Agent15.affineNormalize,hguard]
  have hright : (BB6.Agent15.affineNormalize (2*j+3) k).2≠4 := by
    rw [hnorm,hk]
    omega
  have hall : BB6.Agent3ValSix.highAllowedValSixFull j 3 := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    refine ⟨hval,hfive,?_,?_,?_,?_⟩
    · dsimp [j]; omega
    · dsimp [j]; omega
    · omega
    · simpa [k] using hright
  exact hall

/-- Every member of the infinite progression m=3, j=8r+6 is removed
    by the M16 quotient: its projected target alternates between the
    absent states (15,12,0) and (15,20,0). -/
theorem high_m16_family_removed (r : Nat) :
    ¬ highAllowedValSixM16 (8*r+6) 3 := by
  intro h
  rcases h with ⟨_,hseen⟩
  have ha : CCert.q (2*(8*r+6)+3)=CCert.q 15 := by
    apply CCert.q_congr_big
    · omega
    · decide
    · omega
  have hk :
      2^(2*3+2)*(8*r+6+3)-(8*r+6+3*3+5)=2040*r+2284 := by
    norm_num
    omega
  by_cases heven : r%2=0
  · have hqk :
        CCert.q (2^(2*3+2)*(8*r+6+3)-(8*r+6+3*3+5)) =
          CCert.q 12 := by
      apply CCert.q_congr_big
      · rw [hk]
        omega
      · decide
      · rw [hk]
        omega
    have hfalse : CCert.seen (CCert.q 15) (CCert.q 12) (CCert.q 0)=false := by
      decide
    rw [ha,hqk,hfalse] at hseen
    cases hseen
  · have hodd : r%2=1 := by omega
    have hqk :
        CCert.q (2^(2*3+2)*(8*r+6+3)-(8*r+6+3*3+5)) =
          CCert.q 20 := by
      apply CCert.q_congr_big
      · rw [hk]
        omega
      · decide
      · rw [hk]
        omega
    have hfalse : CCert.seen (CCert.q 15) (CCert.q 20) (CCert.q 0)=false := by
      decide
    rw [ha,hqk,hfalse] at hseen
    cases hseen

/-- The M16 quotient filter removes a genuinely infinite progression
    admitted by the earlier exact high parameter sieve. -/
theorem high_m16_family_strict (r : Nat) :
    BB6.Agent3ValSix.highAllowedValSixFull (8*r+6) 3 ∧
      ¬ highAllowedValSixM16 (8*r+6) 3 :=
  ⟨high_m16_family_survives_old_sieve r,high_m16_family_removed r⟩

#print axioms cReach_implies_m16_seen
#print axioms blank_halts_iff_joint_val_six_m16
#print axioms high_m16_family_survives_old_sieve
#print axioms high_m16_family_removed
#print axioms high_m16_family_strict

end BB6.Agent13M16Integration
