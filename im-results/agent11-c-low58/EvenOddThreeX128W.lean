import SectionAllInverse
import GenericSection
import OddOddVal3Orbit
import OddOddLowVal
import EvenOddFourExact
import HighSumTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Y3X128W
open BB6.Agent46

/-- Exact source parents of (128*w+10,3).  Since
    x+6=16*(8*w+1) with odd factor >1, the a=1 bounce branch is absent;
    the remaining odd-a bounce depths are exactly 0 and 2. -/
theorem y3_x128w_parents (w a k : Nat) (hw : 1≤w)
    (hsec : secNext (a,k)=some (128*w+10,3)) :
    (a=64*w+5 ∧ k=32*w+3) ∨
    (a=16*w-1 ∧ k=56*w+3) := by
  have hp := (section_preimage_all_iff a k (128*w+10) 3).mp hsec
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
              · have hpow' : 8*w+1=2^n := by
                  have hpow0 : 128*w+16=2^n*16 := by omega
                  have hh : 128*w+16=16*(8*w+1) := by omega
                  omega
                have hodd : (8*w+1)%2=1 := by omega
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
              have hpow' : 128*w+16=2^n*(2*a+6) := by omega
              have hcost' :
                  (2*k-a+3)+(2*a+6)+3*n=128*w+20 := by omega
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
                have hmod : (128*w+16)%32=16 := by omega
                have hzero : (128*w+16)%32=0 :=
                  Nat.mod_eq_zero_of_dvd hdiv
                omega
              have hpar : 2*k+a+3*n=128*w+11 := by omega
              have hnEven : n%2=0 := by omega
              have hnCases : n=0 ∨ n=2 := by omega
              rcases hnCases with hn0|hn2
              · subst n
                have hax : 128*w+10=2*a := by omega
                have hkc : 2*k=a+1 := by omega
                left
                constructor <;> omega
              · subst n
                have hax : 128*w+16=8*(a+3) := by
                  norm_num at hpow'
                  omega
                have haeq : a=16*w-1 := by omega
                have hkeq : k=56*w+3 := by omega
                right
                exact ⟨haeq,hkeq⟩
            · omega

/-- A broad exact y=3 boundary slice.  The two possible parents are
    eliminated either immediately by the odd-sum-two image, or through
    the existing odd/odd valuation-three, even/odd four, and odd/odd
    low-valuation inverse normalizers. -/
theorem blank_no_y3_x128w (w : Nat) (hw : 1≤w)
    (hcase : w%2=0 ∨ w%8=5) :
    ¬ BB6.Agent3.CReach (128*w+10) 3 := by
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
          have hsec : secNext (a,k)=some (128*w+10,3) := by
            simpa [BB6.Agent8Section.run,hp] using h
          rcases y3_x128w_parents w a k hw hsec with h0|h2
          · have hP0 : BB6.Agent3.CReach (64*w+5) (32*w+3) := by
              refine ⟨n,?_⟩
              simpa [h0.1,h0.2] using hp
            have hQ0 : BB6.Agent3.CReach (48*w+2) (40*w+1) := by
              apply (BB6.Agent3.oddodd_val3_blank_reach_iff
                (64*w+5) (32*w+3) (by omega) (by omega)
                (by omega) (by omega) (by omega)).mp
              exact hP0
            have hR0 : BB6.Agent3.CReach (44*w-1) (42*w-1) := by
              apply (BB6.Agent3.evenodd_four_blank_reach_iff
                (48*w+2) (40*w+1) (by omega) (by omega)
                (by omega) (by omega)).mp
              exact hQ0
            rcases hcase with hweven|hw5
            · exact BB6.Agent11High.blank_no_odd_sum_two
                (44*w-1) (42*w-1) (by omega) (by omega) (by omega) hR0
            · have hS0 : BB6.Agent3.CReach (43*w-3) ((85*w-7)/2) := by
                apply (BB6.Agent3.oddodd_lowval_blank_reach_iff
                  (44*w-1) (42*w-1) (by omega) (by omega)
                  (by omega) (by omega) (by omega)).mp
                exact hR0
              rcases hS0 with ⟨time2,h2⟩
              cases time2 with
              | zero =>
                  simp [BB6.Agent8Section.run] at h2
                  omega
              | succ n2 =>
                  have himage := BB6.Agent3.blank_section_odd_image
                    n2 (43*w-3) ((85*w-7)/2) h2 (by omega) (by omega)
                  have hsum : ((43*w-3)+((85*w-7)/2))%4=1 := by omega
                  omega
          · exact BB6.Agent11High.blank_no_odd_sum_two
              (16*w-1) (56*w+3) (by omega) (by omega) (by omega) (by
                refine ⟨n,?_⟩
                simpa [h2.1,h2.2] using hp)

/-- The earlier x=10 mod 256 slice is the even-w specialization. -/
theorem blank_no_y3_x256 (t : Nat) (ht : 1≤t) :
    ¬ BB6.Agent3.CReach (256*t+10) 3 := by
  have hw : 1≤2*t := by omega
  have heven : (2*t)%2=0 := by omega
  have h := blank_no_y3_x128w (2*t) hw (Or.inl heven)
  simpa using h

#print axioms y3_x128w_parents
#print axioms blank_no_y3_x128w
#print axioms blank_no_y3_x256
end BB6.Agent11Y3X128W
