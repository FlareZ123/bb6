import SectionAllInverse
import Lean.Elab.Tactic.Omega

/-! Intermediate source-parent fan for the q=0 odd/odd U5 target.
    This file is deliberately not imported by the main M8 proof until a
    local Lean preflight succeeds. -/

namespace BB6.Agent3U5Q0Fan
open BB6.Agent46

private theorem four_pow_mod43_ne_42 (r : Nat) :
    (4:Nat)^r % 43 ≠ 42 := by
  intro h
  have h7 : (4:Nat)^7 % 43 = 1 := by decide
  have hleft : ((4:Nat)^r)^7 % 43 = 1 := by
    calc
      ((4:Nat)^r)^7 % 43 = 4^(r*7) % 43 := by rw [← Nat.pow_mul]
      _ = 4^(7*r) % 43 := by rw [Nat.mul_comm]
      _ = (4^7)^r % 43 := by rw [Nat.pow_mul]
      _ = 1 := by
        rw [Nat.pow_mod, h7]
        simp
  have hright : ((4:Nat)^r)^7 % 43 = 42 := by
    rw [Nat.pow_mod, h]
    decide
  omega

/-- Every original-source predecessor of the odd/odd target
    (44*t-1,42*t-1), for t≥1, is in one exact even-a, even-depth
    bounce family. The exceptional a=0 branch is impossible modulo 43. -/
theorem q0_oddodd_parent_fan (t a k : Nat) (ht : 1≤t)
    (hsec : secNext (a,k)=some (44*t-1,42*t-1)) :
    ∃ q U, 43*t-1=4^q*U ∧ 4≤U ∧ U%2=0 ∧
      a=U-2 ∧ 0<k ∧ a<2*k ∧ 2*k+U+6*q=128*t-8 := by
  have hp := (section_preimage_all_iff a k (44*t-1) (42*t-1)).mp hsec
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · simp [sectionPreimageAll,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,hk0,hk1] at hp
        omega
      · simp only [sectionPreimageAll,if_pos rfl,if_neg hk0,
          if_neg hk1] at hp
        rcases hp with ⟨_,n,hpow,hcost⟩
            have hnEven : n%2=0 := by omega
            obtain ⟨r,hr⟩ : ∃ r, n=2*r := ⟨n/2,by omega⟩
            have hpow8 : 2^n*8=2^(n+3) := by
              rw [show (8:Nat)=2^3 by decide,←Nat.pow_add]
            have hsum : 2*(43*t-1)=2^(n+3) := by
              calc
                2*(43*t-1) = (44*t-1)+(42*t-1) := by omega
                _ = 2^n*8 := hpow
                _ = 2^(n+3) := hpow8
            have hpow2 : 43*t-1=2^(n+2) := by
              rw [show n+3=(n+2)+1 by omega,Nat.pow_succ] at hsum
              omega
            have hpow4 : 43*t-1=4^(r+1) := by
              rw [hr] at hpow2
              calc
                43*t-1 = 2^(2*r+2) := by simpa using hpow2
                _ = 2^(2*(r+1)) := by congr 1; omega
                _ = 4^(r+1) := by
                  rw [Nat.pow_mul,show (2:Nat)^2=4 by decide]
            have hmod : 4^(r+1)%43=42 := by
              rw [←hpow4]
              omega
            exact (four_pow_mod43_ne_42 (r+1)) hmod
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
              rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hodd : ((44*t-1)+(42*t-1)+1)%2=1 := by omega
                rw [hpow] at hodd
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageAll,ha0,ha1,hk0,hlow] at hp
          omega
        · by_cases heven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos heven] at hp
            rcases hp with ⟨_,n,hpow,hcost⟩
            have hfactor : 2*(a-1)+6=2*(a+2) := by omega
            rw [hfactor] at hpow
            rw [hfactor] at hcost
            have hsum : 2*(43*t-1)=2^n*(2*(a+2)) := by omega
            have hcost' : 2*k+a+7+3*n=128*t-3 := by omega
            have hnEven : n%2=0 := by omega
            obtain ⟨q,hq⟩ : ∃ q, n=2*q := ⟨n/2,by omega⟩
            have hpow' : 2*(43*t-1)=2*(4^q*(a+2)) := by
              rw [hq,Nat.pow_mul,show (2:Nat)^2=4 by decide] at hsum
              calc
                2*(43*t-1) = 4^q*(2*(a+2)) := hsum
                _ = 2*(4^q*(a+2)) := by ac_rfl
            have hU : 43*t-1=4^q*(a+2) := by omega
            have hcost'' : 2*k+(a+2)+6*q=128*t-8 := by omega
            refine ⟨q,a+2,hU,?_,?_,?_,?_,?_,hcost''⟩
            · omega
            · omega
            · omega
            · omega
            · omega
          · have haodd : a%2=1 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg heven] at hp
            rcases hp with ⟨_,n,hpow,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hfactor : 2*(a-1)+8=2*(a+3) := by omega
              rw [hfactor] at hpow
              have hodd : ((44*t-1)+(42*t-1)+1)%2=1 := by omega
              rw [hpow] at hodd
              have hEven : (2^n*(2*(a+3)))%2=0 := by
                rw [Nat.mul_mod]
                simp
              omega

#print axioms four_pow_mod43_ne_42
#print axioms q0_oddodd_parent_fan
end BB6.Agent3U5Q0Fan
