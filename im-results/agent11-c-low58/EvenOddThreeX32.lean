import SectionAllInverse
import GenericSection
import OddOddVal3Orbit
import HighSumTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Y3X32
open BB6.Agent46
open BB6.Agent3

/-- For t≥1, the complete original-source predecessor fan of (32t+10,3)
    has exactly two members.  The 2-adic valuation of x+6 is exactly four,
    and the source cost parity forces the bounce depth to be 0 or 2. -/
theorem y3_x32_parents (t a k : Nat) (ht : 1≤t)
    (h : secNext (a,k)=some (32*t+10,3)) :
    (a=16*t+5 ∧ k=8*t+3) ∨ (a=4*t-1 ∧ k=14*t+3) := by
  have hp := (section_preimage_all_iff a k (32*t+10) 3).mp h
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
        omega
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
        omega
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
              rcases hp with ⟨_,n,hpow,_⟩ | ⟨h5,_⟩
              · have hpow' : 32*t+16=2^n*16 := by omega
                have hfactor : 32*t+16=16*(2*t+1) := by omega
                have heq : 2*t+1=2^n := by omega
                have hodd : (2*t+1)%2=1 := by omega
                by_cases hn0 : n=0
                · subst n
                  norm_num at heq
                  omega
                · have hdiv : 2∣2^n := by
                    have hh : 2^1∣2^n := Nat.pow_dvd_pow 2 (by omega)
                    simpa using hh
                  have heven : (2^n)%2=0 :=
                    Nat.mod_eq_zero_of_dvd hdiv
                  omega
              · omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
      · by_cases hlow : 2*k≤a
        · have hcase : 32*t+10=a-2*k ∧ 3=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          omega
        · by_cases haeven : a%2=0
          · simp [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] at hp
            omega
          · have hodd : (a-1)%2=0 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at hp
            rcases hp with ⟨_,n,hpow,hcost⟩ | ⟨h5,_⟩
            · have hpow' : 32*t+16=2^n*(2*a+6) := by omega
              have hcost' :
                  (2*k-a+3)+(2*a+6)+3*n=32*t+20 := by omega
              have hnle : n≤2 := by
                by_contra hn
                have hn3 : 3≤n := by omega
                have hdiv8 : 8∣2^n := by
                  have hh : 2^3∣2^n := Nat.pow_dvd_pow 2 hn3
                  simpa using hh
                have hdiv4 : 4∣2*a+6 := by
                  refine ⟨(a+3)/2,?_⟩
                  omega
                have hdiv32 : 32∣2^n*(2*a+6) := by
                  rcases hdiv8 with ⟨b,hb⟩
                  rcases hdiv4 with ⟨c,hc⟩
                  refine ⟨b*c,?_⟩
                  calc
                    2^n*(2*a+6)=(8*b)*(4*c) := by rw [hb,hc]
                    _=32*(b*c) := by ring
                have hmod : (32*t+16)%32=16 := by omega
                have hzero : (32*t+16)%32=0 := by
                  rw [← hpow']
                  exact Nat.mod_eq_zero_of_dvd hdiv32
                omega
              have hnCases : n=0 ∨ n=1 ∨ n=2 := by omega
              rcases hnCases with hn0|hn1|hn2
              · subst n
                norm_num at hpow' hcost'
                left
                constructor <;> omega
              · subst n
                norm_num at hpow' hcost'
                omega
              · subst n
                norm_num at hpow' hcost'
                right
                constructor <;> omega
            · omega

/-- For even t, the second source parent of (32t+10,3) is
    excluded by the source-certified odd-sum-two obstruction.  Therefore
    any blank reachability must pass through the first parent, and the
    val-3 odd/odd inverse then forces the even/odd state (12t+2,10t+1). -/
theorem y3_x32_even_t_reach_implies_q0 (t : Nat)
    (ht : 1≤t) (hteven : t%2=0)
    (h : CReach (32*t+10) 3) :
    CReach (12*t+2) (10*t+1) := by
  rcases h with ⟨time,hh⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hh
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at hh
      | some p =>
          rcases p with ⟨a,k⟩
          have hsec : secNext (a,k)=some (32*t+10,3) := by
            simpa [BB6.Agent8Section.run,hp] using hh
          rcases y3_x32_parents t a k ht hsec with h0|h2
          · have hP0 : CReach (16*t+5) (8*t+3) := by
              refine ⟨n,?_⟩
              simpa [h0.1,h0.2] using hp
            have hQ0 := (oddodd_val3_blank_reach_iff
              (16*t+5) (8*t+3)
              (by omega) (by omega) (by omega)
              (by omega) (by omega)).mp hP0
            convert hQ0 using 1 <;> omega
          · have hP2 : CReach (4*t-1) (14*t+3) := by
              refine ⟨n,?_⟩
              simpa [h2.1,h2.2] using hp
            exact False.elim (BB6.Agent11High.blank_no_odd_sum_two
              (4*t-1) (14*t+3)
              (by omega) (by omega) (by omega) hP2)

#print axioms y3_x32_parents
#print axioms oddeven_sum3_blank_reach_iff
#print axioms y3_x32_even_t_reach_implies_q0
end BB6.Agent11Y3X32
