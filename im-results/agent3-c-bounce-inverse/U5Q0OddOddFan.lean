import SectionAllInverse
import Lean.Elab.Tactic.Omega

/-! Exact original-section predecessor fan for the q=0 odd/odd U5 target.
    This file classifies the source parents only; it does not by itself
    establish blank-orbit non-reachability. -/

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

private theorem pow_two_double_eq_four (q : Nat) :
    (2:Nat)^(2*q) = 4^q := by
  rw [Nat.pow_mul, show (2:Nat)^2 = 4 by decide]

/-- Every original-source predecessor of the odd/odd target
    (44*t-1,42*t-1), for t≥1, lies in one exact even-a, even-depth
    bounce family. The exceptional a=0 branch is impossible modulo 43. -/
theorem q0_oddodd_parent_fan (t a k : Nat) (ht : 1≤t)
    (hsec : secNext (a,k)=some (44*t-1,42*t-1)) :
    ∃ q U, 43*t-1=4^q*U ∧ 4≤U ∧ U%2=0 ∧
      a=U-2 ∧ 0<k ∧ a<2*k ∧ 2*k+U+6*q=128*t-8 := by
  have hp := (section_preimage_all_iff a k (44*t-1) (42*t-1)).mp hsec
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
      omega
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at hp
        rcases hp with ⟨_,n,hpow,hcost⟩
        have hcost' : 2*k+9+3*n=128*t-3 := by omega
        have hnEven : n%2=0 := by omega
        obtain ⟨r,hr⟩ : ∃ r, n=2*r := ⟨n/2,by omega⟩
        have hsum : 2*(43*t-1)=2^n*8 := by
          calc
            2*(43*t-1)=(44*t-1)+(42*t-1) := by omega
            _=2^n*8 := hpow
        have hpow3 : 2*(43*t-1)=2^(n+3) := by
          calc
            2*(43*t-1)=2^n*8 := hsum
            _=2^n*2^3 := by rw [show (8:Nat)=2^3 by decide]
            _=2^(n+3) := by rw [← Nat.pow_add]
        have hpow2 : 43*t-1=2^(n+2) := by
          rw [show n+3=(n+2)+1 by omega,Nat.pow_succ] at hpow3
          omega
        rw [hr] at hpow2
        have hpow4 : 2^(2*r+2)=4^(r+1) := by
          rw [show 2*r+2=2*(r+1) by omega,Nat.pow_mul,
            show (2:Nat)^2=4 by decide]
        have hpow4' : 43*t-1=4^(r+1) := by
          calc
            43*t-1=2^(2*r+2) := hpow2
            _=4^(r+1) := hpow4
        have hmod : 4^(r+1)%43=42 := by
          rw [← hpow4']
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
              rcases hp with ⟨hy3,n,hpow,_⟩ | ⟨hy5,n,hpow,_⟩
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
            rcases hp with ⟨hy4,n,hpow,hcost⟩
            have hfactor : 2*(a-1)+6=2*(a+2) := by omega
            rw [hfactor] at hpow
            have hsum : 2*(43*t-1)=2^n*(2*(a+2)) := by omega
            have hcost' : 2*k+a+7+3*n=128*t-3 := by omega
            have hnEven : n%2=0 := by omega
            obtain ⟨q,hq⟩ : ∃ q, n=2*q := ⟨n/2,by omega⟩
            rw [hq] at hsum hcost'
            have hscale : 2*(43*t-1)=2*(4^q*(a+2)) := by
              calc
                2*(43*t-1)=2^(2*q)*(2*(a+2)) := hsum
                _=4^q*(2*(a+2)) := by rw [pow_two_double_eq_four]
                _=2*(4^q*(a+2)) := by ac_rfl
            have hUeq : 43*t-1=4^q*(a+2) := by omega
            have hcostFinal : 2*k+(a+2)+6*q=128*t-8 := by omega
            exact ⟨q,a+2,hUeq,by omega,by omega,by omega,by omega,by omega,
              hcostFinal⟩
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg heven] at hp
            rcases hp with ⟨hy3,n,hpow,_⟩ | ⟨hy5,n,hpow,_⟩
            · omega
            · have hodd : ((44*t-1)+(42*t-1)+1)%2=1 := by omega
              rw [hpow] at hodd
              omega

/-- The fan is exact in both directions: every displayed parameter tuple
    realizes a genuine original-source transition, not merely a relaxed
    arithmetic predecessor. -/
theorem q0_oddodd_parent_fan_iff (t a k : Nat) (ht : 1≤t) :
    secNext (a,k)=some (44*t-1,42*t-1) ↔
    ∃ q U, 43*t-1=4^q*U ∧ 4≤U ∧ U%2=0 ∧
      a=U-2 ∧ 0<k ∧ a<2*k ∧ 2*k+U+6*q=128*t-8 := by
  constructor
  · exact q0_oddodd_parent_fan t a k ht
  · rintro ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
    have hUa : U=a+2 := by omega
    have ha0 : a≠0 := by omega
    have ha1 : a≠1 := by omega
    have hk0 : k≠0 := by omega
    have hlow' : ¬2*k≤a := by omega
    have haeven : a%2=0 := by omega
    have hsum : (44*t-1)+(42*t-1)=2^(2*q)*(2*(a+2)) := by
      calc
        (44*t-1)+(42*t-1)=2*(43*t-1) := by omega
        _=2*(4^q*U) := by rw [hpow]
        _=2^(2*q)*(2*(a+2)) := by
          rw [pow_two_double_eq_four,hUa]
          ac_rfl
    have hcost' : (2*k-a+3)+(2*(a-1)+6)+3*(2*q)=
        (44*t-1)+2*(42*t-1) := by
      have hcost'' : 2*k+a+7+6*q=128*t-3 := by omega
      omega
    have hpre : sectionPreimageAll a k (44*t-1) (42*t-1) := by
      simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
        if_neg hk0,if_neg hlow',if_pos haeven]
      exact ⟨by omega,2*q,hsum,hcost'⟩
    exact (section_preimage_all_iff a k (44*t-1) (42*t-1)).mpr hpre

#print axioms four_pow_mod43_ne_42
#print axioms q0_oddodd_parent_fan
#print axioms q0_oddodd_parent_fan_iff
end BB6.Agent3U5Q0Fan
