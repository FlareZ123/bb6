import SectionAllInverse
import GenericSection
import OddOddLowVal
import EvenRightSixOrbit
import HighSumTwo
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Y3X314
open BB6.Agent46

/-- Exact original-source predecessor fan of (512*v+314,3).
    Its x+6 value is 64*(8*v+5), whose 2-adic valuation is exactly six.
    The exceptional a=1 branch is impossible; the remaining bounce depths
    are exactly n=0,2,4. -/
theorem y3_x314_parents (v a k : Nat)
    (hsec : secNext (a,k)=some (512*v+314,3)) :
    (a=256*v+157 ∧ k=128*v+79) ∨
    (a=64*v+37 ∧ k=224*v+136) ∨
    (a=16*v+7 ∧ k=248*v+148) := by
  have hp := (section_preimage_all_iff a k (512*v+314) 3).mp hsec
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
              · have hpow' : 4*(8*v+5)=2^n := by omega
                have hnlt : n<3 := by
                  by_contra hnlt
                  have hn3 : 3≤n := by omega
                  have hdiv : 8∣2^n := by
                    have hh : 2^3∣2^n := Nat.pow_dvd_pow 2 hn3
                    simpa only [show (2:Nat)^3=8 by decide] using hh
                  have hzero : (2^n)%8=0 :=
                    Nat.mod_eq_zero_of_dvd hdiv
                  have hmod : (4*(8*v+5))%8=4 := by omega
                  omega
                have hnge : 2≤n := by
                  by_contra hnge
                  have hnsmall : n<2 := by omega
                  interval_cases n <;> norm_num at hpow' <;> omega
                have hn : n=2 := by omega
                subst n
                norm_num at hpow'
                omega
              · omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
      · by_cases hlow : 2*k≤a
        · have hcase : 512*v+314=a-2*k ∧ 3=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          omega
        · by_cases haeven : a%2=0
          · simp [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] at hp
            omega
          · have haodd : a%2=1 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
                  if_neg hk0,if_neg hlow,if_neg haeven] at hp
            rcases hp with ⟨_,n,hpow,hcost⟩ | ⟨h5,_⟩
            · have hpow' : 512*v+320=2^n*(2*a+6) := by omega
              have hcost' :
                  (2*k-a+3)+(2*a+6)+3*n=512*v+324 := by omega
              have hnle : n≤4 := by
                by_contra hnle
                have hn5 : 5≤n := by omega
                have hpowdiv : 32∣2^n := by
                  have hh : 2^5∣2^n := Nat.pow_dvd_pow 2 hn5
                  simpa only [show (2:Nat)^5=32 by decide] using hh
                have hfacdiv : 4∣2*a+6 := by
                  refine ⟨(a+3)/2,?_⟩
                  omega
                have hdiv : 128∣2^n*(2*a+6) := by
                  rcases hpowdiv with ⟨b,hb⟩
                  rcases hfacdiv with ⟨c,hc⟩
                  refine ⟨b*c,?_⟩
                  calc
                    2^n*(2*a+6)=(32*b)*(4*c) := by rw [hb,hc]
                    _=128*(b*c) := by ring
                rw [←hpow'] at hdiv
                have hzero : (512*v+320)%128=0 :=
                  Nat.mod_eq_zero_of_dvd hdiv
                have hmod : (512*v+320)%128=64 := by omega
                omega
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
              have hnCases : n=0 ∨ n=2 ∨ n=4 := by omega
              rcases hnCases with hn0|hn2|hn4
              · subst n
                norm_num at hpow' hcost'
                left
                constructor <;> omega
              · subst n
                norm_num at hpow' hcost'
                right
                left
                constructor <;> omega
              · subst n
                norm_num at hpow' hcost'
                right
                right
                constructor <;> omega
            · omega

private theorem no_y3_x314_parent0 (v : Nat) :
    ¬ BB6.Agent3.CReach (256*v+157) (128*v+79) := by
  intro hr
  have hQ := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    (256*v+157) (128*v+79)
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).mp hr
  have hQ' : BB6.Agent3.CReach (192*v+116) (160*v+96) := by
    convert hQ using 1 <;> omega
  have hR := (BB6.Agent46.six_even_right_blank_reach_iff
    (192*v+116) (160*v+96)
    (by omega) (by omega) (by omega) (by omega)).mp hQ'
  have hR' : BB6.Agent3.CReach (352*v+210) (80*v+47) := by
    convert hR using 1 <;> omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    (352*v+210) (80*v+47)
    (by omega) (by omega) (by omega) (by omega) hR'

private theorem no_y3_x314_parent1 (v : Nat) :
    ¬ BB6.Agent3.CReach (64*v+37) (224*v+136) := by
  intro hr
  have hQ := (BB6.Agent46.six_even_right_blank_reach_iff
    (64*v+37) (224*v+136)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hQ' : BB6.Agent3.CReach (288*v+171) (112*v+67) := by
    convert hQ using 1 <;> omega
  exact BB6.Agent11High.blank_no_odd_sum_two
    (288*v+171) (112*v+67)
    (by omega) (by omega) (by omega) hQ'

private theorem no_y3_x314_parent2 (v : Nat) :
    ¬ BB6.Agent3.CReach (16*v+7) (248*v+148) := by
  intro hr
  have hQ := (BB6.Agent46.six_even_right_blank_reach_iff
    (16*v+7) (248*v+148)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hQ' : BB6.Agent3.CReach (264*v+153) (124*v+73) := by
    convert hQ using 1 <;> omega
  exact BB6.Agent11High.blank_no_odd_sum_two
    (264*v+153) (124*v+73)
    (by omega) (by omega) (by omega) hQ'

/-- The complete y=3 boundary family x=314 mod 512 is blank-unreachable.
    The exact source parent fan has three members; each is reduced by
    original-section inverse theorems to a forbidden odd-right image. -/
theorem blank_no_y3_x314_mod512 (v : Nat) :
    ¬ BB6.Agent3.CReach (512*v+314) 3 := by
  intro hr
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          have hsec : secNext (a,k)=some (512*v+314,3) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          rcases y3_x314_parents v a k hsec with h0|h1|h2
          · have hP : BB6.Agent3.CReach (256*v+157) (128*v+79) := by
              refine ⟨n,?_⟩
              simpa [h0.1,h0.2] using hp
            exact no_y3_x314_parent0 v hP
          · have hP : BB6.Agent3.CReach (64*v+37) (224*v+136) := by
              refine ⟨n,?_⟩
              simpa [h1.1,h1.2] using hp
            exact no_y3_x314_parent1 v hP
          · have hP : BB6.Agent3.CReach (16*v+7) (248*v+148) := by
              refine ⟨n,?_⟩
              simpa [h2.1,h2.2] using hp
            exact no_y3_x314_parent2 v hP

private theorem nat_le_two_pow (n : Nat) : n≤2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 0<2^n := Nat.pow_pos (by decide)
      calc
        n+1 ≤ 2^n+1 := Nat.add_le_add_right ih 1
        _ ≤ 2^n+2^n := by omega
        _ = 2^(n+1) := by rw [Nat.pow_succ]; ring

/-- The u=5 residual parameter slice t=32*w+5 has
    r=2301+13440*w and x=512*v+314.  Its defining equation for s
    supplies the size bound needed to make v natural. -/
theorem blank_no_u5_residual_t32w5 (w s : Nat)
    (hs : 211*s+129=5*2^(2301+13440*w)) :
    ¬ BB6.Agent3.CReach (302+512*s-4*(2301+13440*w)) 3 := by
  have hrle : 2301+13440*w≤2^(2301+13440*w) :=
    nat_le_two_pow (2301+13440*w)
  have hmul := Nat.mul_le_mul_left 5 hrle
  rw [←hs] at hmul
  have hineq : 11376+67200*w≤211*s := by omega
  have hstrong : 211*(139+840*w)≤8*(211*s) := by
    have hineq8 : 8*(11376+67200*w)≤8*(211*s) :=
      Nat.mul_le_mul_left 8 hineq
    omega
  have hsize : 139+840*w≤8*s := by omega
  let U := 8*s-139-840*w
  have hUeq : 8*s=U+139+840*w := by
    dsimp [U]
    omega
  have hUmod : U%8=5 := by
    dsimp [U]
    omega
  have hUge : 5≤U := by omega
  have hX : 302+512*s-4*(2301+13440*w)=64*U-6 := by
    dsimp [U]
    omega
  let v := (U-5)/8
  have hUdecomp : U=8*v+5 := by
    dsimp [v]
    omega
  have hXdecomp :
      302+512*s-4*(2301+13440*w)=512*v+314 := by
    rw [hX,hUdecomp]
    omega
  rw [hXdecomp]
  exact blank_no_y3_x314_mod512 v

#print axioms y3_x314_parents
#print axioms blank_no_y3_x314_mod512
#print axioms blank_no_u5_residual_t32w5

end BB6.Agent11Y3X314
