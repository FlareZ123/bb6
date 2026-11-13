import SectionAllInverse
import GenericSection
import EvenRightSixOrbit
import HighSumTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3Y3X2Mod16
open BB6.Agent46

/-- For x=2 mod 16, the y=3 bounce depth is forced to zero.
    A positive even depth would make x+6 divisible by 16; depth one
    is ruled out by the exact cost parity. -/
private theorem three_depth_zero_mod16_two (x a k n : Nat)
    (hx : x%16=2) (ha : a%2=1)
    (hpow : x+6=2^n*(2*a+6))
    (hcost : (2*k-a+3)+(2*a+6)+3*n=x+10) :
    n=0 := by
  cases n with
  | zero => rfl
  | succ n =>
      by_cases hn : n=0
      · subst n
        have hcost1 : (2*k-a+3)+(2*a+6)+3=x+10 := by
          simpa using hcost
        omega
      · have hn2 : 2≤n+1 := by omega
        have hpow4 : 4 ∣ 2^(n+1) := by
          have hp := Nat.pow_dvd_pow 2 hn2
          simpa only [show (2:Nat)^2=4 by decide] using hp
        have hfac4 : 4 ∣ 2*a+6 := by
          refine ⟨(a+3)/2,?_⟩
          omega
        have h16 : 16 ∣ x+6 := by
          rcases hpow4 with ⟨b,hb⟩
          rcases hfac4 with ⟨c,hc⟩
          refine ⟨b*c,?_⟩
          calc
            x+6 = 2^(n+1)*(2*a+6) := hpow
            _ = (4*b)*(4*c) := by rw [hb,hc]
            _ = 16*(b*c) := by ac_rfl
        have hmod : (x+6)%16=8 := by omega
        have hzero : (x+6)%16=0 :=
          Nat.mod_eq_zero_of_dvd h16
        omega

/-- Exact original-source y=3 parent classification on x=2 mod 16:
    every parent of (x,3), for x>=18, is (x/2,(x+2)/4). -/
theorem evenodd_three_parent_of_xmod16_two
    (a k x : Nat) (hx : x%16=2) (hlarge : 18≤x)
    (hsec : secNext (a,k)=some (x,3)) :
    a=x/2 ∧ k=(x+2)/4 := by
  have hp := (section_preimage_all_iff a k x 3).mp hsec
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · simp [sectionPreimageAll,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,hk0,hk1] at hp
      · simp [sectionPreimageAll,hk0,hk1] at hp
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
              rcases hp with ⟨_,n,hpow,_⟩ | ⟨h5,_⟩
              · have hdiv : 16 ∣ x+6 := by
                  refine ⟨2^n,?_⟩
                  calc
                    x+6 = 2^n*16 := hpow
                    _ = 16*(2^n) := by ac_rfl
                have hzero : (x+6)%16=0 :=
                  Nat.mod_eq_zero_of_dvd hdiv
                have hmod : (x+6)%16=8 := by omega
                omega
              · omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageAll,ha0,ha1,hk0,hlow] at hp
          omega
        · by_cases heven : a%2=0
          · simp [sectionPreimageAll,ha0,ha1,hk0,hlow,heven] at hp
          · have haodd : a%2=1 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
                  if_neg hk0,if_neg hlow,if_neg heven] at hp
            rcases hp with ⟨_,n,hpow,hcost⟩ | ⟨h5,_⟩
            · have hbase : 2*(a-1)+8=2*a+6 := by omega
              rw [hbase] at hpow
              rw [hbase] at hcost
              have hn := three_depth_zero_mod16_two x a k n hx haodd hpow hcost
              subst n
              have hax : x=2*a := by omega
              have hkc : 2*k=a+1 := by omega
              omega
            · omega

/-- Consequently the entire blank-origin orbit avoids the y=3, x=2 mod 16
    boundary: its unique parent has odd right counter and sum 2 mod 4. -/
theorem blank_no_y3_xmod16_two (x : Nat)
    (hx : x%16=2) (hlarge : 18≤x) :
    ¬ BB6.Agent3.CReach x 3 := by
  intro hr
  rcases hr with ⟨time,h⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at h
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some (x,3) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hk⟩ :=
            evenodd_three_parent_of_xmod16_two a k x hx hlarge hstep
          have hprev : BB6.Agent3.CReach (x/2) ((x+2)/4) := by
            refine ⟨t,?_⟩
            simpa [ha,hk] using hp
          exact BB6.Agent11High.blank_no_odd_sum_two
            (x/2) ((x+2)/4) (by omega) (by omega) (by omega) hprev

#print axioms evenodd_three_parent_of_xmod16_two
#print axioms blank_no_y3_xmod16_two
end BB6.Agent3Y3X2Mod16
