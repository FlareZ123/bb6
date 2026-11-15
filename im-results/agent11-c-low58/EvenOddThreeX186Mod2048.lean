import SectionAllInverse
import GenericSection
import OddOddLowVal
import EvenRightSixOrbit
import HighSumTwo
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3U5X186
open BB6.Agent46

/-- Exact original-source predecessor fan of (2048*v+186,3).
    Here x+6=64*(32*v+3), so the a=1 branch is impossible and
    the odd-a bounce depths are exactly 0, 2, and 4. -/
theorem y3_x186_parents (v a k : Nat)
    (hsec : secNext (a,k)=some (2048*v+186,3)) :
    (a=1024*v+93 ∧ k=512*v+47) ∨
    (a=256*v+21 ∧ k=896*v+80) ∨
    (a=64*v+3 ∧ k=992*v+86) := by
  have hp := (section_preimage_all_iff a k (2048*v+186) 3).mp hsec
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
              · have hpow' : 4*(32*v+3)=2^n := by omega
                have hnlt : n<3 := by
                  by_cases hn3 : 3≤n
                  · have hdiv : 8∣2^n := by
                      have hh : 2^3∣2^n := Nat.pow_dvd_pow 2 hn3
                      simpa only [show (2:Nat)^3=8 by decide] using hh
                    have hzero : (2^n)%8=0 :=
                      Nat.mod_eq_zero_of_dvd hdiv
                    have hmod : (4*(32*v+3))%8=4 := by omega
                    rw [← hpow'] at hzero
                    omega
                  · omega
                have hn0 : n=0 ∨ n=1 ∨ n=2 := by omega
                rcases hn0 with hn0|hn1|hn2
                · subst n
                  change 4*(32*v+3)=1 at hpow'
                  omega
                · subst n
                  change 4*(32*v+3)=2 at hpow'
                  omega
                · subst n
                  simp only [show (2:Nat)^2=4 by decide] at hpow'
                  omega
              · omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
      · by_cases hlow : 2*k≤a
        · have hcase : 2048*v+186=a-2*k ∧ 3=2*k+2 := by
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
              have hpow' : 2048*v+192=2^n*(2*a+6) := by omega
              have hcost' :
                  (2*k-a+3)+(2*a+6)+3*n=2048*v+196 := by omega
              have hnle : n≤4 := by
                by_cases hn5 : 5≤n
                · have hpowdiv : 32∣2^n := by
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
                      _=128*(b*c) := by
                        simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
                  rw [←hpow'] at hdiv
                  have hzero : (2048*v+192)%128=0 :=
                    Nat.mod_eq_zero_of_dvd hdiv
                  have hmod : (2048*v+192)%128=64 := by omega
                  omega
                · omega
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
                rw [show (2:Nat)^0=1 by decide] at hpow'
                left
                constructor <;> omega
              · subst n
                rw [show (2:Nat)^2=4 by decide] at hpow'
                right
                left
                constructor <;> omega
              · subst n
                rw [show (2:Nat)^4=16 by decide] at hpow'
                right
                right
                constructor <;> omega
            · omega

private theorem no_y3_x186_parent0 (v : Nat) :
    ¬ BB6.Agent3.CReach (1024*v+93) (512*v+47) := by
  intro hr
  have hQ := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    (1024*v+93) (512*v+47)
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).mp hr
  have hQ' : BB6.Agent3.CReach (768*v+68) (640*v+56) := by
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (768*v+68,640*v+56))
    have hx : ((1024*v+93)+(512*v+47)-4)/2=768*v+68 := by omega
    have hy : ((1024*v+93)+3*(512*v+47)-10)/4=640*v+56 := by omega
    simpa only [hx,hy] using hQ
  have hR := (BB6.Agent46.six_even_right_blank_reach_iff
    (768*v+68) (640*v+56)
    (by omega) (by omega) (by omega) (by omega)).mp hQ'
  have hR' : BB6.Agent3.CReach (1408*v+122) (320*v+27) := by
    have hx : ((768*v+68)+(640*v+56)-2)=1408*v+122 := by omega
    have hy : (640*v+56-2)/2=320*v+27 := by omega
    rw [hx,hy] at hR
    exact hR
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    (1408*v+122) (320*v+27)
    (by omega) (by omega) (by omega) (by omega) hR'

private theorem no_y3_x186_parent1 (v : Nat) :
    ¬ BB6.Agent3.CReach (256*v+21) (896*v+80) := by
  intro hr
  have hQ := (BB6.Agent46.six_even_right_blank_reach_iff
    (256*v+21) (896*v+80)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hQ' : BB6.Agent3.CReach (1152*v+99) (448*v+39) := by
    have hx : ((256*v+21)+(896*v+80)-2)=1152*v+99 := by omega
    have hy : (896*v+80-2)/2=448*v+39 := by omega
    rw [hx,hy] at hQ
    exact hQ
  exact BB6.Agent11High.blank_no_odd_sum_two
    (1152*v+99) (448*v+39)
    (by omega) (by omega) (by omega) hQ'

private theorem no_y3_x186_parent2 (v : Nat) :
    ¬ BB6.Agent3.CReach (64*v+3) (992*v+86) := by
  intro hr
  have hQ1 := (BB6.Agent46.six_even_right_blank_reach_iff
    (64*v+3) (992*v+86)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hQ1' : BB6.Agent3.CReach (1056*v+87) (496*v+42) := by
    have hx : ((64*v+3)+(992*v+86)-2)=1056*v+87 := by omega
    have hy : (992*v+86-2)/2=496*v+42 := by omega
    rw [hx,hy] at hQ1
    exact hQ1
  have hQ2 := (BB6.Agent46.six_even_right_blank_reach_iff
    (1056*v+87) (496*v+42)
    (by omega) (by omega) (by omega) (by omega)).mp hQ1'
  have hQ2' : BB6.Agent3.CReach (1552*v+127) (248*v+20) := by
    have hx : ((1056*v+87)+(496*v+42)-2)=1552*v+127 := by omega
    have hy : (496*v+42-2)/2=248*v+20 := by omega
    rw [hx,hy] at hQ2
    exact hQ2
  have hQ3 := (BB6.Agent46.six_even_right_blank_reach_iff
    (1552*v+127) (248*v+20)
    (by omega) (by omega) (by omega) (by omega)).mp hQ2'
  have hQ3' : BB6.Agent3.CReach (1800*v+145) (124*v+9) := by
    have hx : ((1552*v+127)+(248*v+20)-2)=1800*v+145 := by omega
    have hy : (248*v+20-2)/2=124*v+9 := by omega
    rw [hx,hy] at hQ3
    exact hQ3
  exact BB6.Agent11High.blank_no_odd_sum_two
    (1800*v+145) (124*v+9)
    (by omega) (by omega) (by omega) hQ3'

/-- The complete y=3 boundary family x=186 mod 2048 is blank-unreachable.
    The exact source parent fan has three members; each is reduced by
    original-section inverse theorems to a forbidden odd-right image. -/
theorem blank_no_y3_x186_mod2048 (v : Nat) :
    ¬ BB6.Agent3.CReach (2048*v+186) 3 := by
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
          have hsec : secNext (a,k)=some (2048*v+186,3) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          rcases y3_x186_parents v a k hsec with h0|h1|h2
          · have hP : BB6.Agent3.CReach (1024*v+93) (512*v+47) := by
              refine ⟨n,?_⟩
              simpa [h0.1,h0.2] using hp
            exact no_y3_x186_parent0 v hP
          · have hP : BB6.Agent3.CReach (256*v+21) (896*v+80) := by
              refine ⟨n,?_⟩
              simpa [h1.1,h1.2] using hp
            exact no_y3_x186_parent1 v hP
          · have hP : BB6.Agent3.CReach (64*v+3) (992*v+86) := by
              refine ⟨n,?_⟩
              simpa [h2.1,h2.2] using hp
            exact no_y3_x186_parent2 v hP

private theorem nat_le_two_pow (n : Nat) : n≤2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 0<2^n := Nat.pow_pos (by decide)
      calc
        n+1 ≤ 2^n+1 := Nat.add_le_add_right ih 1
        _ ≤ 2^n+2^n := by omega
        _ = 2^(n+1) := by rw [Nat.pow_succ]; omega

private theorem u5_s_mod8 (z s : Nat)
    (hs : 211*s+129=5*2^(19101+53760*z)) : s%8=5 := by
  have hr3 : 3≤19101+53760*z := by omega
  have hdiv : 8∣2^(19101+53760*z) := by
    have hh : 2^3∣2^(19101+53760*z) := Nat.pow_dvd_pow 2 hr3
    simpa only [show (2:Nat)^3=8 by decide] using hh
  have hzero : (2^(19101+53760*z))%8=0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  have hpow : (5*2^(19101+53760*z))%8=0 := by
    simp [Nat.mul_mod,hzero]
  have heq : (211*s+129)%8=0 := by rw [hs]; exact hpow
  omega

/-- The residual M=128*z+45 slice has terminal x=2048*v+186.
    This theorem closes the terminal y=3 state only; the separate
    repeated six-even-right composition is needed to exclude its feeder. -/
set_option maxHeartbeats 1000000 in
theorem blank_no_u5_residual_m128z45 (z s : Nat)
    (hs : 211*s+129=5*2^(19101+53760*z)) :
    ¬ BB6.Agent3.CReach (302+512*s-4*(19101+53760*z)) 3 := by
  let M := 128*z+45
  let r := 19101+53760*z
  have hsmod : s%8=5 := u5_s_mod8 z s hs
  let m := 32*(s-1)-105*M
  have hsize : 43+105*M≤32*s := by
    have hrle : r≤2^r := nat_le_two_pow r
    have hmul : 5*r≤211*s+129 := by
      have hh := Nat.mul_le_mul_left 5 hrle
      rw [←hs] at hh
      exact hh
    have hmul32 : 32*(5*r)≤32*(211*s+129) :=
      Nat.mul_le_mul_left 32 hmul
    dsimp [r,M] at *
    omega
  have hs1 : 1≤s := by omega
  have hmge : 11≤m := by
    dsimp [m]
    omega
  have hsdecomp : s=8*(s/8)+5 := by omega
  have hmMod : m%128=11 := by
    dsimp [m,M]
    rw [hsdecomp]
    omega
  let v := (m-11)/128
  have hmdecomp : m=128*v+11 := by
    dsimp [v]
    omega
  clear hs
  have hX : 302+512*s-4*r=16*m+10 := by
    dsimp [m,M,r]
    omega
  have hXdecomp :
      302+512*s-4*(19101+53760*z)=2048*v+186 := by
    rw [hX,hmdecomp]
    omega
  rw [hXdecomp]
  exact blank_no_y3_x186_mod2048 v

#print axioms y3_x186_parents
#print axioms blank_no_y3_x186_mod2048
#print axioms blank_no_u5_residual_m128z45

end BB6.Agent3U5X186
