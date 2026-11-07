import StrongJointResidual
import HighEvenRightSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighEvenRight

private theorem old_gate_no (q r : Nat) :
    ¬ ((8*q+18)%2^(r+4)=2^(r+2)) := by
  intro h
  have hdiv4 : 4∣2^(r+4) := by
    change (2:Nat)^2 ∣ 2^(r+4)
    exact Nat.pow_dvd_pow (a:=2) (m:=2) (n:=r+4) (by omega)
  have hmod4 := congrArg (fun z : Nat => z%4) h
  have hleft : (8*q+18)%2^(r+4)%4=(8*q+18)%4 :=
    Nat.mod_mod_of_dvd (8*q+18) hdiv4
  rw [hleft] at hmod4
  have hpow4 : (2^(r+2))%4=0 := by
    have hd : 4∣2^(r+2) := by
      change (2:Nat)^2 ∣ 2^(r+2)
      exact Nat.pow_dvd_pow (a:=2) (m:=2) (n:=r+2) (by omega)
    exact Nat.mod_eq_zero_of_dvd hd
  rw [hpow4] at hmod4
  have hactual : (8*q+18)%4=2 := by omega
  omega

private theorem c58_gate_no (q r : Nat) :
    ¬ ((8*q+47)%2^(r+4)=3*2^(r+2)) := by
  intro h
  have hdiv2 : 2∣2^(r+4) := by
    change (2:Nat)^1 ∣ 2^(r+4)
    exact Nat.pow_dvd_pow (a:=2) (m:=1) (n:=r+4) (by omega)
  have hmod2 := congrArg (fun z : Nat => z%2) h
  have hleft : (8*q+47)%2^(r+4)%2=(8*q+47)%2 :=
    Nat.mod_mod_of_dvd (8*q+47) hdiv2
  rw [hleft] at hmod2
  have hpow2 : 2∣2^(r+2) := by
    change (2:Nat)^1 ∣ 2^(r+2)
    exact Nat.pow_dvd_pow (a:=2) (m:=1) (n:=r+2) (by omega)
  have hrhs : (3*2^(r+2))%2=0 := by
    rw [Nat.mul_mod]
    rw [Nat.mod_eq_zero_of_dvd hpow2]
  rw [hrhs] at hmod2
  have hactual : (8*q+47)%2=1 := by omega
  omega

/-- The entire previously source-certified C58/ValSix and two-sided
    all-phase high sieve admits every member of this infinite progression. -/
theorem high_even_right_family_prior_allowed (q : Nat) :
    BB6.Agent24Phase.highAllowed (8*q+6) 3 := by
  let j : Nat := 8*q+6
  have hOld : ∀ r : Nat, ¬(r+4≤2*3+2 ∧
      (j+3*3+3)%2^(r+4)=2^(r+2) ∧
      (2*j+3)%8=(if r%2=0 then 7 else 3)) := by
    intro r
    rintro ⟨_,hpair,_⟩
    exact old_gate_no q r (by simpa [j] using hpair)
  have hC58 : ∀ r : Nat, ¬(2≤r ∧ 3≤3 ∧ r+4≤2*3+2 ∧
      3%4=(2*r+3)%4 ∧
      (j+9*3+14)%2^(r+4)=3*2^(r+2)) := by
    intro r
    rintro ⟨_,_,_,_,hpair⟩
    exact c58_gate_no q r (by simpa [j] using hpair)
  have hPhase : ¬ BB6.Agent46.allPhaseExcluded j 3 := by
    intro h
    rcases h with ⟨r,hr8,hwidth,_⟩
    dsimp [j] at hr8 hwidth
    omega
  have hArithmetic :=
    high_even_right_parent_arithmetic j 3
      (by dsimp [j]; omega) (by decide) (by dsimp [j]; omega)
  rcases hArithmetic with ⟨_,hk6,hxk8,_,_,_⟩
  have hguard : ¬(4≤(2:Nat)^(2*3+2)*(j+3)-(j+3*3+5) ∧
      ((2:Nat)^(2*3+2)*(j+3)-(j+3*3+5))%2=0 ∧
      (2*j+3+((2:Nat)^(2*3+2)*(j+3)-(j+3*3+5)))%4=1) := by
    have hxk4 :
        (2*j+3+((2:Nat)^(2*3+2)*(j+3)-(j+3*3+5)))%4=3 := by
      have h := hxk8
      dsimp [j] at h ⊢
      omega
    omega
  have hnorm :
      BB6.Agent15.affineNormalize (2*j+3)
        ((2:Nat)^(2*3+2)*(j+3)-(j+3*3+5)) =
      (2*j+3,((2:Nat)^(2*3+2)*(j+3)-(j+3*3+5))) := by
    simp [BB6.Agent15.affineNormalize,hguard]
  have hright :
      (BB6.Agent15.affineNormalize (2*j+3)
        ((2:Nat)^(2*3+2)*(j+3)-(j+3*3+5))).2≠4 := by
    rw [hnorm]
    dsimp [j] at hk6 ⊢
    omega
  have hJointBase : BB6.Agent3.jointHighAllowed j 3 := by
    unfold BB6.Agent3.jointHighAllowed
    dsimp [j]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hRect : BB6.Agent3.jointHighRectAllowed j 3 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hJointBase,by dsimp [j]; omega⟩
  have hAgent19 : BB6.Agent19Joint.highAllowed j 3 := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨hRect,hOld,?_,?_,?_,?_⟩ <;> dsimp [j] <;> omega
  have hAgent29 : BB6.Agent29Joint.highAllowedPlus j 3 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨hAgent19,by dsimp [j]; omega,by dsimp [j]; omega,
      by dsimp [j]; omega,by dsimp [j]; omega⟩
  have hValSix : BB6.Agent3ValSix.highAllowedValSixThree j 3 := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨hAgent29,by dsimp [j]; omega,by dsimp [j]; omega⟩,
      by dsimp [j]; omega⟩
  have hAgent11 : BB6.Agent11Joint.highAllowed j 3 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨hAgent19,by dsimp [j]; omega,by dsimp [j]; omega⟩
  have hFive : BB6.Agent19Five.highAllowed j 3 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨hAgent11,by dsimp [j]; omega⟩
  have hValFull : BB6.Agent3ValSix.highAllowedValSixFull j 3 := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hValSix,hFive,by dsimp [j]; omega,by dsimp [j]; omega,
      by dsimp [j]; omega,hright⟩
  have hC58ValSix : BB6.Agent11C58ValSix.highAllowed j 3 := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hValFull,by dsimp [j]; omega⟩
  have hAllDepth : BB6.Agent11C58AllDepth.highAllowed j 3 := by
    unfold BB6.Agent11C58AllDepth.highAllowed
    exact ⟨hC58ValSix,hC58⟩
  unfold BB6.Agent24Phase.highAllowed
  exact ⟨hAllDepth,hPhase⟩

/-- Exact source-authentic Machine C halting iff after removing this
    additional infinite high stopping family. The remaining parameter
    existential is still unbounded and undecided. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent24Phase.highAllowed j m ∧
  ¬(3≤m ∧ m%4=3 ∧ j%8=(m+3)%8)

theorem blank_halts_iff_high_even_right :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent24Phase.blank_halts_iff_c58_two_sided_all_phase]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · have hreach : BB6.Agent3.CReach (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5)) :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hnot : ¬(3≤m ∧ m%4=3 ∧ j%8=(m+3)%8) := by
        rintro ⟨hm,hm4,hj8⟩
        exact high_even_right_blank_unreachable j m hm hm4 hj8 hreach
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- An infinite progression of genuinely new high stopping indices:
    every pair was admitted by the complete prior all-phase sieve and
    is now excluded by the exact even-right source inverse. -/
theorem high_even_right_family_new (q : Nat) :
    BB6.Agent24Phase.highAllowed (8*q+6) 3 ∧
    ¬ highAllowed (8*q+6) 3 := by
  refine ⟨high_even_right_family_prior_allowed q,?_⟩
  intro h
  exact h.2 ⟨by omega,by omega,by omega⟩

theorem high_even_right_family_indices_distinct (s t : Nat)
    (h : 8*s+6=8*t+6) : s=t := by omega

#print axioms high_even_right_family_prior_allowed
#print axioms blank_halts_iff_high_even_right
#print axioms high_even_right_family_new
end BB6.Agent19HighEvenRight
