import StrongJointResidual
import HighEvenRightSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighEvenRight

private theorem residue_facts (j m : Nat) (hm4 : m%4=3)
    (hj8 : j%8=(m+3)%8) :
    j%2=0 ∧ m%2=1 ∧ (j%8=6 ∨ j%8=2) ∧
    (m%8=3 ∨ m%8=7) ∧
    (j+3*m+3)%8=2 ∧ (j+9*m+14)%2=1 := by
  have hm8 : m%8=3 ∨ m%8=7 := by omega
  have hj8' : j%8=6 ∨ j%8=2 := by
    rcases hm8 with h|h
    · have hplus : (m+3)%8=6 := by omega
      rw [hplus] at hj8
      omega
    · have hplus : (m+3)%8=2 := by omega
      rw [hplus] at hj8
      omega
  omega

private theorem old_gate_no (j m r : Nat) (hm4 : m%4=3)
    (hj8 : j%8=(m+3)%8) :
    ¬ ((j+3*m+3)%2^(r+4)=2^(r+2)) := by
  intro h
  have hdiv4 : 4∣2^(r+4) := by
    change (2:Nat)^2 ∣ 2^(r+4)
    exact Nat.pow_dvd_pow (a:=2) (m:=2) (n:=r+4) (by omega)
  have hmod4 := congrArg (fun z : Nat => z%4) h
  have hleft : (j+3*m+3)%2^(r+4)%4=(j+3*m+3)%4 :=
    Nat.mod_mod_of_dvd (j+3*m+3) hdiv4
  rw [hleft] at hmod4
  have hpow4 : (2^(r+2))%4=0 := by
    have hd : 4∣2^(r+2) := by
      change (2:Nat)^2 ∣ 2^(r+2)
      exact Nat.pow_dvd_pow (a:=2) (m:=2) (n:=r+2) (by omega)
    exact Nat.mod_eq_zero_of_dvd hd
  rw [hpow4] at hmod4
  have hactual : (j+3*m+3)%4=2 := by
    have hf := residue_facts j m hm4 hj8
    omega
  omega

private theorem c58_gate_no (j m r : Nat) (hm4 : m%4=3)
    (hj8 : j%8=(m+3)%8) :
    ¬ ((j+9*m+14)%2^(r+4)=3*2^(r+2)) := by
  intro h
  have hdiv2 : 2∣2^(r+4) := by
    change (2:Nat)^1 ∣ 2^(r+4)
    exact Nat.pow_dvd_pow (a:=2) (m:=1) (n:=r+4) (by omega)
  have hmod2 := congrArg (fun z : Nat => z%2) h
  have hleft : (j+9*m+14)%2^(r+4)%2=(j+9*m+14)%2 :=
    Nat.mod_mod_of_dvd (j+9*m+14) hdiv2
  rw [hleft] at hmod2
  have hpow2 : 2∣2^(r+2) := by
    change (2:Nat)^1 ∣ 2^(r+2)
    exact Nat.pow_dvd_pow (a:=2) (m:=1) (n:=r+2) (by omega)
  have hrhs : (3*2^(r+2))%2=0 := by
    rw [Nat.mul_mod]
    rw [Nat.mod_eq_zero_of_dvd hpow2]
  rw [hrhs] at hmod2
  have hactual : (j+9*m+14)%2=1 := by
    have hf := residue_facts j m hm4 hj8
    omega
  omega

private theorem phase_no (j m : Nat) (hm4 : m%4=3)
    (hj8 : j%8=(m+3)%8)
    (hPhase : ∃ r, 8≤r ∧ r+4≤2*m+2 ∧
      ((j%16=(2*r)%16 ∧ (j+3*m+3)%2^(r+4)=9*2^r) ∨
       (j%16=(12+2*r)%16 ∧ (j+3*m+3)%2^(r+4)=13*2^r))) : False := by
  rcases hPhase with ⟨r,hr8,_,hbranch⟩
  have hsum8 : (j+3*m+3)%8=2 := (residue_facts j m hm4 hj8).2.2.2.2.1
  rcases hbranch with ⟨_,hpair⟩ | ⟨_,hpair⟩
  · have hdiv8 : 8∣2^(r+4) := by
      change (2:Nat)^3 ∣ 2^(r+4)
      exact Nat.pow_dvd_pow (a:=2) (m:=3) (n:=r+4) (by omega)
    have hmod8 := congrArg (fun z : Nat => z%8) hpair
    have hleft : (j+3*m+3)%2^(r+4)%8=(j+3*m+3)%8 :=
      Nat.mod_mod_of_dvd (j+3*m+3) hdiv8
    rw [hleft] at hmod8
    have hpow : (2^r)%8=0 := by
      have hd : 8∣2^r := by
        change (2:Nat)^3 ∣ 2^r
        exact Nat.pow_dvd_pow (a:=2) (m:=3) (n:=r) (by omega)
      exact Nat.mod_eq_zero_of_dvd hd
    have hrhs : (9*2^r)%8=0 := by
      rw [Nat.mul_mod]
      rw [hpow]
    rw [hrhs] at hmod8
    omega
  · have hdiv8 : 8∣2^(r+4) := by
      change (2:Nat)^3 ∣ 2^(r+4)
      exact Nat.pow_dvd_pow (a:=2) (m:=3) (n:=r+4) (by omega)
    have hmod8 := congrArg (fun z : Nat => z%8) hpair
    have hleft : (j+3*m+3)%2^(r+4)%8=(j+3*m+3)%8 :=
      Nat.mod_mod_of_dvd (j+3*m+3) hdiv8
    rw [hleft] at hmod8
    have hpow : (2^r)%8=0 := by
      have hd : 8∣2^r := by
        change (2:Nat)^3 ∣ 2^r
        exact Nat.pow_dvd_pow (a:=2) (m:=3) (n:=r) (by omega)
      exact Nat.mod_eq_zero_of_dvd hd
    have hrhs : (13*2^r)%8=0 := by
      rw [Nat.mul_mod]
      rw [hpow]
    rw [hrhs] at hmod8
    omega

/-- Every parameter in this residue class survives the entire previous
    high sieve: Agent3/11/19/29's joint filters, all-depth dyadic gates,
    the C58 gate, affine normalization, and Agent24's two-sided phase gate. -/
theorem high_even_right_family_prior_allowed (j m : Nat)
    (hm : 3≤m) (hm4 : m%4=3) (hj8 : j%8=(m+3)%8) :
    BB6.Agent24Phase.highAllowed j m := by
  rcases residue_facts j m hm4 hj8 with
    ⟨hj2,hm2,hj8',hm8,hsum8,hodd⟩
  have hOld : ∀ r : Nat, ¬(r+4≤2*m+2 ∧
      (j+3*m+3)%2^(r+4)=2^(r+2) ∧
      (2*j+3)%8=(if r%2=0 then 7 else 3)) := by
    intro r
    rintro ⟨_,hpair,_⟩
    exact old_gate_no j m r hm4 hj8 hpair
  have hC58 : ∀ r : Nat, ¬(2≤r ∧ 3≤m ∧ r+4≤2*m+2 ∧
      m%4=(2*r+3)%4 ∧
      (j+9*m+14)%2^(r+4)=3*2^(r+2)) := by
    intro r
    rintro ⟨_,_,_,_,hpair⟩
    exact c58_gate_no j m r hm4 hj8 hpair
  have hPhase : ¬ BB6.Agent46.allPhaseExcluded j m := by
    intro h
    apply phase_no j m hm4 hj8
    simpa [BB6.Agent46.allPhaseExcluded] using h
  let k := BB6.Agent19HighEvenRight.highK j m
  have hArithmetic :=
    high_even_right_parent_arithmetic j m hm hm4 hj8
  rcases hArithmetic with ⟨_,hk6,hxk8,_,_,_⟩
  have hxk8' : (2*j+3+k)%8=3 := by simpa [k] using hxk8
  have hguard : ¬(4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1) := by
    have hxk4 : (2*j+3+k)%4=3 := by omega
    omega
  have hnorm : BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
    simp [BB6.Agent15.affineNormalize,hguard,k]
  have hright : (BB6.Agent15.affineNormalize (2*j+3) k).2≠4 := by
    rw [hnorm]
    omega
  have hJointBase : BB6.Agent3.jointHighAllowed j m := by
    unfold BB6.Agent3.jointHighAllowed
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hRect : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hJointBase,by omega⟩
  have hAgent19 : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨hRect,hOld,?_,?_,?_,?_⟩ <;> omega
  have hAgent29 : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨hAgent19,by omega,by omega,by omega,by omega⟩
  have hValSix : BB6.Agent3ValSix.highAllowedValSixThree j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨hAgent29,by omega,by omega⟩,by omega⟩
  have hAgent11 : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨hAgent19,by omega,by omega⟩
  have hFive : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨hAgent11,by omega⟩
  have hright' :
      (BB6.Agent15.affineNormalize (2*j+3)
        (2^(2*m+2)*(j+3)-(j+3*m+5))).2≠4 := by
    simpa [k,BB6.Agent19HighEvenRight.highK] using hright
  have hValFull : BB6.Agent3ValSix.highAllowedValSixFull j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hValSix,hFive,by omega,by omega,by omega,hright'⟩
  have hC58ValSix : BB6.Agent11C58ValSix.highAllowed j m := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hValFull,by omega⟩
  have hAllDepth : BB6.Agent11C58AllDepth.highAllowed j m := by
    unfold BB6.Agent11C58AllDepth.highAllowed
    exact ⟨hC58ValSix,hC58⟩
  unfold BB6.Agent24Phase.highAllowed
  exact ⟨hAllDepth,hPhase⟩

/-- Lossless original-source Machine C halting iff after adding the
    independent even-right high stopping exclusion. The remaining
    parameter existential is still unbounded and undecided. -/
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

/-- The source exclusion is independent of the complete previous
    all-phase high sieve for every parameter in the stated cylinder. -/
theorem high_even_right_family_new (j m : Nat)
    (hm : 3≤m) (hm4 : m%4=3) (hj8 : j%8=(m+3)%8) :
    BB6.Agent24Phase.highAllowed j m ∧ ¬ highAllowed j m := by
  refine ⟨high_even_right_family_prior_allowed j m hm hm4 hj8,?_⟩
  intro h
  exact h.2 ⟨hm,hm4,hj8⟩

/-- Explicit infinite two-parameter progression inside the new cylinder. -/
theorem high_even_right_progression_new (q n : Nat) :
    BB6.Agent24Phase.highAllowed (8*q+6) (8*n+3) ∧
    ¬ highAllowed (8*q+6) (8*n+3) := by
  apply high_even_right_family_new
  · omega
  · omega
  · omega

theorem high_even_right_progression_indices_injective :
    Function.Injective (fun p : Nat×Nat => (8*p.1+6,8*p.2+3)) := by
  intro a b h
  rcases a with ⟨q₁,n₁⟩
  rcases b with ⟨q₂,n₂⟩
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hq,hn⟩
  simp [omega]

#print axioms high_even_right_family_prior_allowed
#print axioms blank_halts_iff_high_even_right
#print axioms high_even_right_progression_new
end BB6.Agent19HighEvenRight
