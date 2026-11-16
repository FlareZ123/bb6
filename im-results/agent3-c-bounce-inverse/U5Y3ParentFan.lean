import SectionAllInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3U5DepthFan
open BB6.Agent46

/-- Powers of two occupy only the three nonzero residue classes modulo seven. -/
private theorem pow_two_mod_seven (n : Nat) :
    2^n%7=1 ∨ 2^n%7=2 ∨ 2^n%7=4 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ,Nat.mul_mod]
      rcases ih with h|h|h
      · rw [h]
        decide
      · rw [h]
        decide
      · rw [h]
        decide

/-- The u=5 residual equation gives the exact affine identity for m+1.
    Here r=201+420*M and 32*s=32+105*M+m. -/
theorem u5_residual_m_identity (M s m : Nat)
    (hs : 211*s+129=5*2^(201+420*M))
    (hm : 32*s=32+105*M+m) :
    211*(m+1)+10669+22155*M=160*2^(201+420*M) := by
  omega

/-- The affine identity forces the mod-seven residue used to eliminate the
    exceptional a=1 source branch. -/
theorem u5_residual_m_mod7 (M m : Nat)
    (h : 211*(m+1)+10669+22155*M=160*2^(201+420*M)) :
    (m+1)%7=5 := by
  have hpow : 2^(201+420*M)%7=1 := by
    rw [show 201+420*M=3*(67+140*M) by omega,
      Nat.pow_mul,Nat.pow_mod]
    have hbase : (2:Nat)^3%7=1 := by decide
    rw [hbase]
    simp
  have hleft :
      (211*(m+1)+10669+22155*M)%7=(m+2)%7 := by
    omega
  have hright :
      (160*2^(201+420*M))%7=6 := by
    rw [Nat.mul_mod]
    have h160 : (160:Nat)%7=6 := by decide
    rw [h160,hpow]
  have hmod :
      (211*(m+1)+10669+22155*M)%7 =
        (160*2^(201+420*M))%7 := by rw [h]
  rw [hleft,hright] at hmod
  omega

/-- Exact original-source parent fan for the u=5 terminal shape.
    The q=0 parent is explicit. Every q>=1 parent requires
    2^(2*q-2) | (m+1), with the displayed exact coordinates. The power
    inequality in the conclusion makes the fan finite for each fixed m. -/
theorem y3_u5_parent_fan (m a k : Nat)
    (hm7 : (m+1)%7=5)
    (hsec : secNext (a,k)=some (16*m+10,3)) :
    (a=8*(m+1)-3 ∧ k=4*(m+1)-1) ∨
    ∃ q U : Nat,
      1≤q ∧
      2^(2*q-2)≤m+1 ∧
      m+1=2^(2*q-2)*U ∧
      a+3=2*U ∧
      k+3*q+1=U*(2^(2*q+1)-1) := by
  have hp := (section_preimage_all_iff a k (16*m+10) 3).mp hsec
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
              rcases hp with ⟨_,n,hpow,_⟩ | ⟨h5,_⟩
              · have hpow' : m+1=2^n := by omega
                rw [hpow'] at hm7
                rcases pow_two_mod_seven n with h|h|h <;> omega
              · omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
      · by_cases hlow : 2*k≤a
        · have hcase : 16*m+10=a-2*k ∧ 3=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          omega
        · by_cases haeven : a%2=0
          · simp [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] at hp
          · have haodd : a%2=1 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
                if_neg hk0,if_neg hlow,if_neg haeven] at hp
            rcases hp with ⟨_,n,hpow,hcost⟩ | ⟨h5,_⟩
            · have hfac : 2*(a-1)+8=2*a+6 := by omega
              rw [hfac] at hpow hcost
              have hpow' : 16*(m+1)=2^n*(2*a+6) := by omega
              have hcost' : 2*k+a+9+3*n=16*m+20 := by omega
              have hfactorEven : (2*a+6)%2=0 := by omega
              have hpowEven : (2^n*(2*a+6))%2=0 := by
                simp [Nat.mul_mod,hfactorEven]
              have hcostSimpl :
                  2*k+a+9+3*n=2^n*(2*a+6)+4 := by omega
              have hnEven : n%2=0 := by
                have hmod : (2*k+a+9+3*n)%2=0 := by
                  rw [hcostSimpl]
                  simp [Nat.add_mod,hpowEven]
                omega
              obtain ⟨q,hq⟩ : ∃ q, n=2*q := by
                exact ⟨n/2,by omega⟩
              rw [hq] at hpow' hcost'
              by_cases hq0 : q=0
              · subst q
                rw [show (2:Nat)^(2*0)=1 by decide] at hpow'
                simp at hpow'
                have ha : a=8*(m+1)-3 := by omega
                have hk : k=4*(m+1)-1 := by omega
                exact Or.inl ⟨ha,hk⟩
              · have hqpos : 1≤q := by omega
                let U := (a+3)/2
                have hU : a+3=2*U := by
                  dsimp [U]
                  omega
                have hUpos : 1≤U := by
                  dsimp [U]
                  omega
                have hfacU : 2*a+6=4*U := by omega
                have hpowSplit : 2^(2*q)=2^(2*q-2)*4 := by
                  rw [show 2*q=(2*q-2)+2 by omega,Nat.pow_add]
                  simp
                have hfactor :
                    2^(2*q)*(2*a+6)=16*(2^(2*q-2)*U) := by
                  rw [hpowSplit,hfacU]
                  calc
                    (2^(2*q-2)*4)*(4*U)=
                        (4*4)*(2^(2*q-2)*U) := by ac_rfl
                    _=16*(2^(2*q-2)*U) := by
                      rw [show (4:Nat)*4=16 by decide]
                rw [hfactor] at hpow'
                have hdecomp : m+1=2^(2*q-2)*U := by omega
                have hpowPlus : 2^(2*q+1)=8*2^(2*q-2) := by
                  rw [show 2*q+1=(2*q-2)+3 by omega,Nat.pow_add]
                  rw [show (2:Nat)^3=8 by decide]
                  ac_rfl
                have hpowIdentity :
                    16*(2^(2*q-2)*U)=2*U*2^(2*q+1) := by
                  rw [hpowPlus]
                  have h16 : (2:Nat)*8=16 := by decide
                  calc
                    16*(2^(2*q-2)*U)=(2*8)*(2^(2*q-2)*U) := by rw [h16]
                    _=2*U*(8*2^(2*q-2)) := by ac_rfl
                have hcost3 :
                    2*k+a+9+6*q=16*(m+1)+4 := by omega
                rw [hdecomp] at hcost3
                have hA : a+9=2*U+6 := by omega
                rw [hpowIdentity] at hcost3
                have hcost4 :
                    2*k+2*U+6*q+2=2*U*2^(2*q+1) := by omega
                have hpowPos : 0<2^(2*q+1) := Nat.pow_pos (by decide)
                have hpowSub : 2^(2*q+1)-1+1=2^(2*q+1) := by omega
                have hdistrib :
                    2*U*(2^(2*q+1)-1)+2*U=2*U*2^(2*q+1) := by
                  calc
                    2*U*(2^(2*q+1)-1)+2*U =
                        2*U*((2^(2*q+1)-1)+1) := by
                          rw [Nat.mul_add]
                          simp
                    _=2*U*2^(2*q+1) := by rw [hpowSub]
                rw [←hdistrib] at hcost4
                have hprod :
                    2*U*(2^(2*q+1)-1)=2*(U*(2^(2*q+1)-1)) := by ac_rfl
                rw [hprod] at hcost4
                have hk : k+3*q+1=U*(2^(2*q+1)-1) := by omega
                have hbound : 2^(2*q-2)≤m+1 := by
                  calc
                    2^(2*q-2)=2^(2*q-2)*1 := by simp
                    _≤2^(2*q-2)*U := Nat.mul_le_mul_left _ hUpos
                    _=m+1 := hdecomp.symm
                exact Or.inr ⟨q,U,hqpos,hbound,hdecomp,hU,hk⟩
            · omega

/-- The u=5 residual equation now feeds directly into the exact parent fan;
    no selected congruence cylinder or bounded-time premise is required. -/
theorem u5_residual_y3_parent_fan (M s m a k : Nat)
    (hs : 211*s+129=5*2^(201+420*M))
    (hm : 32*s=32+105*M+m)
    (hsec : secNext (a,k)=some (302+512*s-4*(201+420*M),3)) :
    (a=8*(m+1)-3 ∧ k=4*(m+1)-1) ∨
    ∃ q U : Nat,
      1≤q ∧
      2^(2*q-2)≤m+1 ∧
      m+1=2^(2*q-2)*U ∧
      a+3=2*U ∧
      k+3*q+1=U*(2^(2*q+1)-1) := by
  have hid := u5_residual_m_identity M s m hs hm
  have hm7 := u5_residual_m_mod7 M m hid
  have hX : 302+512*s-4*(201+420*M)=16*m+10 := by omega
  have hsec' : secNext (a,k)=some (16*m+10,3) := by
    simpa only [hX] using hsec
  exact y3_u5_parent_fan m a k hm7 hsec'

#print axioms u5_residual_m_identity
#print axioms u5_residual_m_mod7
#print axioms y3_u5_parent_fan
#print axioms u5_residual_y3_parent_fan

end BB6.Agent3U5DepthFan
