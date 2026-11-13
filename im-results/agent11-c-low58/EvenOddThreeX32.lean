import SectionAllInverse
import GenericSection
import OddOddVal3Orbit
import OddOddLowVal
import EvenOddFourExact
import OddEvenInverse
import HighSumTwo
import M0EvenEvenSumZero
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

/-- The odd-first/even-right sum-three sector has a unique direct parent,
    hence blank reachability is equivalent to reachability of that parent. -/
theorem oddeven_sum3_blank_reach_iff (x y : Nat)
    (hy : 6≤y) (hx : x%2=1) (he : y%2=0)
    (hs : (x+y)%8=3) :
    CReach x y ↔ CReach (x+y-2) ((y-2)/2) := by
  let a := x+y-2
  let k := (y-2)/2
  have ha0 : a≠0 := by dsimp [a]; omega
  have ha1 : a≠1 := by dsimp [a]; omega
  have hk0 : k≠0 := by dsimp [k]; omega
  have hlow : 2*k≤a := by dsimp [a,k]; omega
  have hedge : secNext (a,k)=some (x,y) := by
    apply (section_preimage_all_iff a k x y).mpr
    simp [sectionPreimageAll,ha0,ha1,hk0,hlow]
    dsimp [a,k]
    omega
  have hunique : ∀ b c, secNext (b,c)=some (x,y) → b=a ∧ c=k := by
    intro b c hbc
    have hh := section_oddeven_sum3_mod8_inverse b c x y hy hx he hs hbc
    rcases hh with ⟨hb,hc⟩
    constructor <;> dsimp [a,k] <;> omega
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero =>
        simp [BB6.Agent8Section.run] at hn
        omega
    | succ n =>
        cases hr : BB6.Agent8Section.run secNext n (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hr] at hn
        | some p =>
            rcases p with ⟨b,c⟩
            have hsrc : secNext (b,c)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hr] using hn
            have hbc := hunique b c hsrc
            exact ⟨n,by simpa [hbc.1,hbc.2] using hr⟩
  · rintro ⟨n,hn⟩
    exact ⟨n+1,by simp [BB6.Agent8Section.run,hn,hedge]⟩

/-- The y=3 terminal is blank-unreachable on the infinite cylinder
    x=1024z+650.  Both exact source parents are eliminated: the n=2
    parent by odd-sum-two, and the n=0 parent by val-3, even/odd-four,
    odd/odd-lowval, then odd-sum-one. -/
theorem blank_no_y3_x32 (z : Nat) :
    ¬ CReach (1024*z+650) 3 := by
  let q := 8*z+5
  let t := 4*q
  have ht : 1≤t := by dsimp [t,q]; omega
  have htarget : 1024*z+650=32*t+10 := by
    dsimp [t,q]
    omega
  have hmain : ¬ CReach (32*t+10) 3 := by
    intro hr
    rcases hr with ⟨n,hn⟩
    cases n with
    | zero =>
        simp [BB6.Agent8Section.run] at hn
        omega
    | succ n =>
        cases hprev : BB6.Agent8Section.run secNext n (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hprev] at hn
        | some p =>
            rcases p with ⟨a,k⟩
            have hsrc : secNext (a,k)=some (32*t+10,3) := by
              simpa [BB6.Agent8Section.run,hprev] using hn
            rcases y3_x32_parents t a k ht hsrc with hP0|hP2
            · have hreachP0 : CReach (16*t+5) (8*t+3) := by
                refine ⟨n,?_⟩
                simpa [hP0.1,hP0.2] using hprev
              have hQ0 : CReach (12*t+2) (10*t+1) := by
                have hh := (oddodd_val3_blank_reach_iff
                  (16*t+5) (8*t+3)
                  (by omega) (by omega) (by omega)
                  (by dsimp [t,q]; omega) (by omega)).mp hreachP0
                convert hh using 1 <;> omega
              have hR0 : CReach (11*t-1) ((21*t-2)/2) := by
                have hh := (evenodd_four_blank_reach_iff
                  (12*t+2) (10*t+1)
                  (by omega) (by omega) (by omega)
                  (by dsimp [t,q]; omega)).mp hQ0
                convert hh using 1 <;> omega
              have hS0 : CReach (43*q-3) ((85*q-7)/2) := by
                have hh := (oddodd_lowval_blank_reach_iff
                  (11*t-1) ((21*t-2)/2)
                  (by dsimp [t,q]; omega)
                  (by dsimp [t,q]; omega)
                  (by dsimp [t,q]; omega)
                  (by dsimp [t,q]; omega)
                  (by dsimp [t,q]; omega)
                  (by dsimp [t,q]; omega)).mp hR0
                convert hh using 1 <;> dsimp [t,q] <;> omega
              have hforbid := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
                (43*q-3) ((85*q-7)/2)
                (by dsimp [q]; omega)
                (by dsimp [q]; omega)
                (by dsimp [q]; omega)
                (by dsimp [q]; omega)
              exact hforbid hS0
            · have hreachP2 : CReach (16*q-1) (56*q+3) := by
                refine ⟨n,?_⟩
                simpa [hP2.1,hP2.2,t,q] using hprev
              exact BB6.Agent11High.blank_no_odd_sum_two
                (16*q-1) (56*q+3)
                (by dsimp [q]; omega)
                (by dsimp [q]; omega)
                (by dsimp [q]; omega)
                hreachP2
  simpa [htarget] using hmain

#print axioms y3_x32_parents
#print axioms oddeven_sum3_blank_reach_iff
#print axioms blank_no_y3_x32
end BB6.Agent11Y3X32
