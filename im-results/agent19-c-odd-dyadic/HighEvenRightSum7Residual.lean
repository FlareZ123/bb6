import HighEvenRightResidual
import HighEvenRightSum7Arithmetic
import HighEvenRightSum7Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighEvenRight

private theorem sum7_old_gate_no (j m r : Nat)
    (hA4 : (j+3*m+3)%4=2) :
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
  omega

private theorem sum7_c58_gate_no (j m r : Nat)
    (hB2 : (j+9*m+14)%2=1) :
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
  omega

private theorem sum7_phase_no (j m : Nat)
    (hA8 : (j+3*m+3)%8=2) :
    ¬ BB6.Agent46.allPhaseExcluded j m := by
  intro h
  change ∃ r, 8≤r ∧ r+4≤2*m+2 ∧
    ((j%16=(2*r)%16 ∧ (j+3*m+3)%2^(r+4)=9*2^r) ∨
     (j%16=(12+2*r)%16 ∧ (j+3*m+3)%2^(r+4)=13*2^r)) at h
  rcases h with ⟨r,hr8,_,hbranch⟩
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

/-- The entire exceptional sum-seven congruence cylinder survives
    the complete previous Agent24 high sieve. -/
theorem sum7_family_prior_allowed (j m : Nat)
    (hm5 : 5≤m) (hm4 : m%4=1)
    (hrel : (j+8)%32=(3*m+1)%32) :
    BB6.Agent24Phase.highAllowed j m := by
  have hj4 : j%4=0 := by
    have h := congrArg (fun z : Nat => z%4) hrel
    have hleft : (j+8)%32%4=(j+8)%4 :=
      Nat.mod_mod_of_dvd (j+8) (by decide : 4∣32)
    have hright : (3*m+1)%32%4=(3*m+1)%4 :=
      Nat.mod_mod_of_dvd (3*m+1) (by decide : 4∣32)
    rw [hleft,hright] at h
    omega
  have hrel8 : (j+8)%8=(3*m+1)%8 := by
    have h := congrArg (fun z : Nat => z%8) hrel
    have hleft : (j+8)%32%8=(j+8)%8 :=
      Nat.mod_mod_of_dvd (j+8) (by decide : 8∣32)
    have hright : (3*m+1)%32%8=(3*m+1)%8 :=
      Nat.mod_mod_of_dvd (3*m+1) (by decide : 8∣32)
    rw [hleft,hright] at h
    exact h
  have hjm4 : (j+m)%4=1 := by omega
  have hA4 : (j+3*m+3)%4=2 := by omega
  have hA8 : (j+3*m+3)%8=2 := by omega
  have hB2 : (j+9*m+14)%2=1 := by omega
  have hOld : ∀ n : Nat, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,hpair,_⟩
    exact sum7_old_gate_no j m n hA4 hpair
  have hC58 : ∀ n : Nat, ¬(2≤n ∧ 3≤m ∧ n+4≤2*m+2 ∧
      m%4=(2*n+3)%4 ∧
      (j+9*m+14)%2^(n+4)=3*2^(n+2)) := by
    intro n
    rintro ⟨_,_,_,_,hpair⟩
    exact sum7_c58_gate_no j m n hB2 hpair
  have hPhase : ¬ BB6.Agent46.allPhaseExcluded j m :=
    sum7_phase_no j m hA8
  rcases sum7_target_residues_of_congruence j m hm5 hm4 hrel with
    ⟨hk12,hk8,hxk8,hS32,hx4⟩
  let k : Nat := highK j m
  have hk12' : 12≤k := by simpa [k] using hk12
  have hk8' : k%8=4 := by simpa [k] using hk8
  have hxk8' : (2*j+3+k)%8=7 := by
    simpa [k] using hxk8
  have hxk4 : (2*j+3+k)%4=3 := by omega
  have hguard : ¬(4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1) := by omega
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
    exact ⟨hJointBase,by
      rintro ⟨hm32,hj32⟩
      omega⟩
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
    exact ⟨hValSix,hFive,by omega,by omega,by
      rintro ⟨hm32,hj32⟩
      omega,hright'⟩
  have hC58ValSix : BB6.Agent11C58ValSix.highAllowed j m := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hValFull,by omega⟩
  have hAllDepth : BB6.Agent11C58AllDepth.highAllowed j m := by
    unfold BB6.Agent11C58AllDepth.highAllowed
    exact ⟨hC58ValSix,hC58⟩
  unfold BB6.Agent24Phase.highAllowed
  exact ⟨hAllDepth,hPhase⟩

/-- Both independent high stopping exclusions are now part of the
    residual exact halting predicate. -/
def highAllowedWithSum7 (j m : Nat) : Prop :=
  BB6.Agent24Phase.highAllowed j m ∧
  ¬(3≤m ∧ m%4=3 ∧ j%8=(m+3)%8) ∧
  ¬(5≤m ∧ m%32=5 ∧ j%32=8)

theorem blank_halts_iff_high_even_right_and_sum7 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedWithSum7 j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent24Phase.blank_halts_iff_c58_two_sided_all_phase]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · have hreach : BB6.Agent3.CReach (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5)) :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hnotEvenRight : ¬(3≤m ∧ m%4=3 ∧ j%8=(m+3)%8) := by
        rintro ⟨hm,hm4,hj8⟩
        exact high_even_right_blank_unreachable j m hm hm4 hj8 hreach
      have hnotSum7 : ¬(5≤m ∧ m%32=5 ∧ j%32=8) := by
        rintro ⟨hm5,hm32,hj32⟩
        have hjEq : j=32*(j/32)+8 := by
          have h:=Nat.mod_add_div j 32
          rw [hj32] at h
          omega
        have hmEq : m=32*(m/32)+5 := by
          have h:=Nat.mod_add_div m 32
          rw [hm32] at h
          omega
        have hreach' : BB6.Agent3.CReach
            (2*(32*(j/32)+8)+3)
            (highK (32*(j/32)+8) (32*(m/32)+5)) := by
          simpa [hjEq,hmEq,BB6.Agent19HighEvenRight.highK] using hreach
        exact sum7_high_blank_unreachable (j/32) (m/32) hreach'
      exact Or.inr ⟨j,m,⟨hprior,hnotEvenRight,hnotSum7⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

theorem sum7_family_new (q r : Nat) :
    BB6.Agent24Phase.highAllowed (32*q+8) (32*r+5) ∧
    ¬ highAllowedWithSum7 (32*q+8) (32*r+5) := by
  refine ⟨sum7_family_prior_allowed q r,?_⟩
  intro h
  exact h.2.2 ⟨by omega,by omega,by omega⟩

theorem sum7_family_indices_injective :
    Function.Injective (fun p : Nat×Nat => (32*p.1+8,32*p.2+5)) := by
  intro a b h
  rcases a with ⟨q₁,r₁⟩
  rcases b with ⟨q₂,r₂⟩
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hq,hr⟩
  apply Prod.ext <;> omega

#print axioms sum7_family_prior_allowed
#print axioms sum7_every_parent_odd_image
#print axioms sum7_high_blank_unreachable
#print axioms blank_halts_iff_high_even_right_and_sum7
#print axioms sum7_family_new
end BB6.Agent19HighEvenRight
