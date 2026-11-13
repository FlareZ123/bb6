import SectionAllInverse
import GenericSection
import OddOddVal3Orbit
import EvenOddFourExact
import HighSumTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Y3X256
open BB6.Agent46

/-- Exact source parents of (256*t+10,3).  The odd quotient
    (16*t+1) in x+6=16*(16*t+1) fixes v2(x+6)=4, so only
    bounce depths 0 and 2 survive the cost parity. -/
theorem y3_x256_parents (t a k : Nat) (ht : 1≤t)
    (hsec : secNext (a,k)=some (256*t+10,3)) :
    (a=128*t+5 ∧ k=64*t+3) ∨
    (a=32*t-1 ∧ k=112*t+3) := by
  have hp := (section_preimage_all_iff a k (256*t+10) 3).mp hsec
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · simp [sectionPreimageAll,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,hk0,hk1] at hp
        omega
      · simp [sectionPreimageAll,hk0,hk1] at hp
        omega
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
              · have hpow' : 16*t+1=2^n := by
                  have hh : 256*t+16=16*(16*t+1) := by omega
                  have hpow0 : 256*t+16=2^n*16 := by omega
                  omega
                have hodd : (16*t+1)%2=1 := by omega
                by_cases hn : n=0
                · subst n
                  simp at hpow'
                  omega
                · have hnpos : 1≤n := by omega
                  have hdiv : 2∣2^n := by
                    have hh : 2^1∣2^n := Nat.pow_dvd_pow 2 hnpos
                    simpa using hh
                  have heven : (2^n)%2=0 :=
                    Nat.mod_eq_zero_of_dvd hdiv
                  omega
              · omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageAll,ha0,ha1,hk0,hlow] at hp
          omega
        · by_cases heven : a%2=0
          · simp [sectionPreimageAll,ha0,ha1,hk0,hlow,heven] at hp
            omega
          · have haodd : a%2=1 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
                if_neg hk0,if_neg hlow,if_neg heven] at hp
            rcases hp with ⟨_,n,hpow,hcost⟩ | ⟨h5,_⟩
            · have hbase : 2*(a-1)+8=2*a+6 := by omega
              rw [hbase] at hpow
              rw [hbase] at hcost
              have hpow' : 256*t+16=2^n*(2*a+6) := by omega
              have hcost' :
                  (2*k-a+3)+(2*a+6)+3*n=256*t+20 := by omega
              have hnle : n≤2 := by
                by_contra hn
                have hn3 : 3≤n := by omega
                have hpowdiv : 8∣2^n := by
                  have hh : 2^3∣2^n := Nat.pow_dvd_pow 2 hn3
                  simpa only [show (2:Nat)^3=8 by norm_num] using hh
                have hfacdiv : 4∣2*a+6 := by
                  refine ⟨(a+3)/2,?_⟩
                  omega
                have hdiv : 32∣2^n*(2*a+6) := by
                  rcases hpowdiv with ⟨b,hb⟩
                  rcases hfacdiv with ⟨c,hc⟩
                  refine ⟨b*c,?_⟩
                  calc
                    2^n*(2*a+6)=(8*b)*(4*c) := by rw [hb,hc]
                    _=32*(b*c) := by ring
                rw [← hpow'] at hdiv
                have hmod : (256*t+16)%32=16 := by omega
                have hzero : (256*t+16)%32=0 :=
                  Nat.mod_eq_zero_of_dvd hdiv
                omega
              have hpar : 2*k+a+3*n=256*t+11 := by omega
              have hnEven : n%2=0 := by omega
              have hnCases : n=0 ∨ n=2 := by omega
              rcases hnCases with hn0|hn2
              · subst n
                have hax : 256*t+10=2*a := by omega
                have hkc : 2*k=a+1 := by omega
                left
                constructor <;> omega
              · subst n
                have hax : 256*t+16=8*(a+3) := by
                  norm_num at hpow'
                  omega
                have haeq : a=32*t-1 := by omega
                have hkeq : k=112*t+3 := by omega
                right
                exact ⟨haeq,hkeq⟩
            · omega

/-- The entire x=2 mod 16-adjacent x=10 mod 256 y=3 slice is
    excluded from the authentic blank orbit.  Both exact source parents
    are eliminated using previously source-certified odd/odd and even/odd
    inverse normalizers. -/
theorem blank_no_y3_x256 (t : Nat) (ht : 1≤t) :
    ¬ BB6.Agent3.CReach (256*t+10) 3 := by
  intro hr
  rcases hr with ⟨time,h⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at h
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨a,k⟩
          have hsec : secNext (a,k)=some (256*t+10,3) := by
            simpa [BB6.Agent8Section.run,hp] using h
          rcases y3_x256_parents t a k ht hsec with h0|h2
          · have hP0 : BB6.Agent3.CReach (128*t+5) (64*t+3) := by
              refine ⟨n,?_⟩
              simpa [h0.1,h0.2] using hp
            have hQ0 : BB6.Agent3.CReach (96*t+2) (80*t+1) := by
              apply (BB6.Agent3.oddodd_val3_blank_reach_iff
                (128*t+5) (64*t+3) (by omega) (by omega)
                (by omega) (by omega) (by omega)).mp
              exact hP0
            have hR0 : BB6.Agent3.CReach (88*t-1) (84*t-1) := by
              apply (BB6.Agent3.evenodd_four_blank_reach_iff
                (96*t+2) (80*t+1) (by omega) (by omega)
                (by omega) (by omega)).mp
              exact hQ0
            exact BB6.Agent11High.blank_no_odd_sum_two
              (88*t-1) (84*t-1) (by omega) (by omega) (by omega) hR0
          · have hP2 : BB6.Agent3.CReach (32*t-1) (112*t+3) := by
              refine ⟨n,?_⟩
              simpa [h2.1,h2.2] using hp
            exact BB6.Agent11High.blank_no_odd_sum_two
              (32*t-1) (112*t+3) (by omega) (by omega) (by omega) hP2

#print axioms y3_x256_parents
#print axioms blank_no_y3_x256
end BB6.Agent11Y3X256
