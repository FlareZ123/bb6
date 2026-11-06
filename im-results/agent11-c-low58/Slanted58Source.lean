import SectionAllInverse
import EvenRightSixOrbit
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C58Slanted
open BB6.Agent46
private theorem v5_no_large_depth (u v h a n : Nat) (ha : a%2=0)
  (hp : 64*u+448*v+128*h+96=2^n*(2*a+4)) : n<4 := by
  by_cases hn : n<4
  · exact hn
  have hn4 : 4≤n := by omega
  have hdiv16 : 16 ∣ (2:Nat)^n := by
    have hd : (2:Nat)^4 ∣ (2:Nat)^n := Nat.pow_dvd_pow 2 hn4
    simpa only [show (2:Nat)^4=16 by decide] using hd
  have hdiv4 : 4 ∣ 2*a+4 := by omega
  rcases hdiv16 with ⟨u,hu⟩
  rcases hdiv4 with ⟨w,hw⟩
  have hdiv64 : 64 ∣ 2^n*(2*a+4) := by
    refine ⟨u*w, ?_⟩
    rw [hu,hw]
    simp only [show (64:Nat)=16*4 by decide]
    ac_rfl
  rcases hdiv64 with ⟨z,hz⟩
  omega

private theorem even_candidate (u v h a k n : Nat)
  (ha : a%2=0)
  (hp : 64*u+448*v+128*h+96=2^n*(2*a+4))
  (hc : 2*k+a+7+3*n=64*u+512*v+144*h+109) :
  (a=32*u+224*v+64*h+46 ∧ k=16*u+144*v+40*h+28) ∨
  (a=8*u+56*v+16*h+10 ∧ k=28*u+228*v+64*h+43) := by
  have hn4 := v5_no_large_depth u v h a n ha hp
  have hn_even : n%2=0 := by omega
  have hn : n=0 ∨ n=2 := by omega
  rcases hn with rfl | rfl
  · left
    simp only [show (2:Nat)^0=1 by decide, Nat.one_mul] at hp
    omega
  · right
    simp only [show (2:Nat)^2=4 by decide] at hp
    omega

private theorem not_pow8 (u v h n : Nat) : 64*u+448*v+128*h+96 ≠ (2:Nat)^n*8 := by
  intro hp
  by_cases hn : n<3
  · have hn_cases : n=0 ∨ n=1 ∨ n=2 := by omega
    rcases hn_cases with rfl | rfl | rfl
    · simp only [show (2:Nat)^0=1 by decide] at hp
      omega
    · simp only [show (2:Nat)^1=2 by decide] at hp
      omega
    · simp only [show (2:Nat)^2=4 by decide] at hp
      omega
  · have hn3 : 3≤n := by omega
    have hdiv8 : 8 ∣ (2:Nat)^n := by
      have hd : (2:Nat)^3 ∣ (2:Nat)^n := Nat.pow_dvd_pow 2 hn3
      simpa only [show (2:Nat)^3=8 by decide] using hd
    rcases hdiv8 with ⟨z,hz⟩
    rw [hz] at hp
    have h64 : 64 ∣ 64*u+448*v+128*h+96 := by
      refine ⟨z, ?_⟩
      omega
    rcases h64 with ⟨w,hw⟩
    omega

private theorem p2_parent_iff (u v h a k : Nat)
    (hh : sectionPreimageAll a k (64*u+384*v+112*h+83) (64*v+16*h+13)) :
    (a=32*u+224*v+64*h+46 ∧ k=16*u+144*v+40*h+28) ∨
    (a=8*u+56*v+16*h+10 ∧ k=28*u+228*v+64*h+43) := by
  unfold sectionPreimageAll at hh
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp only [if_pos ha0, if_pos hk0] at hh
    · by_cases hk1 : k=1
      · simp only [if_pos ha0, if_neg hk0, if_pos hk1] at hh
        omega
      · simp only [if_pos ha0, if_neg hk0, if_neg hk1] at hh
        rcases hh with ⟨_,n,hp,_⟩
        exact False.elim (not_pow8 u v h n (by omega))
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp only [if_neg ha0, if_pos ha1, if_pos hk0] at hh
        omega
      · by_cases hk1 : k=1
        · simp only [if_neg ha0, if_pos ha1, if_neg hk0, if_pos hk1] at hh
          omega
        · by_cases hk2 : k=2
          · simp only [if_neg ha0, if_pos ha1, if_neg hk0, if_neg hk1, if_pos hk2] at hh
            omega
          · by_cases hk3 : k=3
            · simp only [if_neg ha0, if_pos ha1, if_neg hk0, if_neg hk1, if_neg hk2, if_pos hk3] at hh
              omega
            · simp only [if_neg ha0, if_pos ha1, if_neg hk0, if_neg hk1, if_neg hk2, if_neg hk3] at hh
              rcases hh with ⟨h3,_⟩ | ⟨_,n,hp,_⟩
              · omega
              · omega
    · by_cases hk0 : k=0
      · simp only [if_neg ha0, if_neg ha1, if_pos hk0] at hh
        omega
      · by_cases hd : 2*k≤a
        · simp only [if_neg ha0, if_neg ha1, if_neg hk0, if_pos hd] at hh
          omega
        · by_cases hae : a%2=0
          · simp only [if_neg ha0, if_neg ha1, if_neg hk0, if_neg hd, if_pos hae] at hh
            rcases hh with ⟨_,n,hp,hc⟩
            have hminus : 2*(a-1)+6=2*a+4 := by omega
            rw [hminus] at hp
            have hcost : 2*k+a+7+3*n=64*u+512*v+144*h+109 := by omega
            exact even_candidate u v h a k n hae (by omega) hcost
          · simp only [if_neg ha0, if_neg ha1, if_neg hk0, if_neg hd, if_neg hae] at hh
            rcases hh with ⟨h3,_⟩ | ⟨_,n,hp,_⟩
            · omega
            · have hdiv2 : 2 ∣ (2:Nat)^n*(2*(a-1)+8) := by
                refine ⟨(2:Nat)^n*((a-1)+4), ?_⟩
                have hf : 2*(a-1)+8=2*((a-1)+4) := by omega
                rw [hf]
                ac_rfl
              rcases hdiv2 with ⟨w,hw⟩
              omega

private theorem excluded_odd_sum_one (x y : Nat) (hy : 5≤y)
    (hodd : y%2=1) (hs : (x+y)%4=1) :
    ¬ BB6.Agent3.CReach x y := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
    simp [BB6.Agent8Section.run] at hr
    omega
  | succ n =>
    have hi := BB6.Agent3.blank_section_odd_image n x y hr hy hodd
    omega

/-- Every section predecessor of the intermediate odd-odd root belongs
    to one of two exact affine families, both truly blank-unreachable. -/
theorem no_root_middle (u v h : Nat) :
    ¬ BB6.Agent3.CReach (64*u+384*v+112*h+83) (64*v+16*h+13) := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
    simp [BB6.Agent8Section.run] at hr
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at hr
    | some p =>
      rcases p with ⟨a,k⟩
      have hedge : secNext (a,k)=some (64*u+384*v+112*h+83,64*v+16*h+13) := by
        simpa [BB6.Agent8Section.run,hp] using hr
      have hpossible := (section_preimage_all_iff a k (64*u+384*v+112*h+83) (64*v+16*h+13)).mp hedge
      rcases p2_parent_iff u v h a k hpossible with ⟨ha,hk⟩ | ⟨ha,hk⟩
      · have hrA : BB6.Agent3.CReach (32*u+224*v+64*h+46) (16*u+144*v+40*h+28) := by
          exact ⟨t, by simpa only [ha,hk] using hp⟩
        have hrC := (six_even_right_blank_reach_iff
          (32*u+224*v+64*h+46) (16*u+144*v+40*h+28)
          (by omega) (by omega) (by omega) (by omega)).mp hrA
        have hrC' : BB6.Agent3.CReach (48*u+368*v+104*h+72) (8*u+72*v+20*h+13) := by
          have heqx : (32*u+224*v+64*h+46)+(16*u+144*v+40*h+28)-2=48*u+368*v+104*h+72 := by omega
          have heqy : ((16*u+144*v+40*h+28)-2)/2=8*u+72*v+20*h+13 := by omega
          simpa only [heqx,heqy] using hrC
        exact excluded_odd_sum_one (48*u+368*v+104*h+72) (8*u+72*v+20*h+13)
          (by omega) (by omega) (by omega) hrC'
      · have hrB : BB6.Agent3.CReach (8*u+56*v+16*h+10) (28*u+228*v+64*h+43) := by
          exact ⟨t, by simpa only [ha,hk] using hp⟩
        exact excluded_odd_sum_one (8*u+56*v+16*h+10) (28*u+228*v+64*h+43)
          (by omega) (by omega) (by omega) hrB

/-- Infinite right-counter cylinder missing from the real blank-origin
    Machine C section orbit, via two forced even-right inverse transitions
    followed by the complete source inverse grammar. -/
theorem blank_no_parametric_slanted_58 (u v h : Nat) :
    ¬ BB6.Agent3.CReach (64*u+16*h+1) (256*v+64*h+58) := by
  intro hr
  have h1 := (six_even_right_blank_reach_iff (64*u+16*h+1) (256*v+64*h+58)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have h1' : BB6.Agent3.CReach (64*u+256*v+80*h+57) (128*v+32*h+28) := by
    have hx : (64*u+16*h+1)+(256*v+64*h+58)-2=64*u+256*v+80*h+57 := by omega
    have hy : ((256*v+64*h+58)-2)/2=128*v+32*h+28 := by omega
    simpa only [hx,hy] using h1
  have h2 := (six_even_right_blank_reach_iff (64*u+256*v+80*h+57) (128*v+32*h+28)
    (by omega) (by omega) (by omega) (by omega)).mp h1'
  have h2' : BB6.Agent3.CReach (64*u+384*v+112*h+83) (64*v+16*h+13) := by
    have hx : (64*u+256*v+80*h+57)+(128*v+32*h+28)-2=64*u+384*v+112*h+83 := by omega
    have hy : ((128*v+32*h+28)-2)/2=64*v+16*h+13 := by omega
    simpa only [hx,hy] using h2
  exact no_root_middle u v h h2'



/-- Four concurrent true blank-root obstructions in one exact affine
    parameterization. The original x=1 (mod64), y=58 (mod256) rectangle
    is the h=0 subfamily. -/
theorem blank_no_slanted_58 (u v h : Nat) :
    ¬ BB6.Agent3.CReach (64*u+16*h+1) (256*v+64*h+58) :=
  blank_no_parametric_slanted_58 u v h

#print axioms blank_no_slanted_58
end BB6.Agent11C58Slanted
