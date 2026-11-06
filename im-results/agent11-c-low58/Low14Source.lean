import SectionAllInverse
import EvenRightSixOrbit
import Agent3CImage
import SectionDyadic
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C14
open BB6.Agent46

private theorem no_special_depth (t n : Nat)
  (hp : 64*t+16=(2:Nat)^n*16) : t=0 ∧ n=0 := by
  by_cases hn : n<2
  · have hcase : n=0 ∨ n=1 := by omega
    rcases hcase with rfl | rfl
    · simp only [show (2:Nat)^0=1 by decide, Nat.one_mul] at hp
      omega
    · simp only [show (2:Nat)^1=2 by decide] at hp
      omega
  · have hdiv4 : 4 ∣ (2:Nat)^n := by
      have hd : (2:Nat)^2 ∣ (2:Nat)^n := Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^2=4 by decide] using hd
    rcases hdiv4 with ⟨z,hz⟩
    have hdiv64 : 64 ∣ 64*t+16 := by
      refine ⟨z,?_⟩
      rw [hz] at hp
      omega
    rcases hdiv64 with ⟨w,hw⟩
    omega

private theorem odd_depth_only_one (t a n : Nat) (ha : a%2=1)
  (hp : 64*t+16=(2:Nat)^(n+1)*(a+3))
  (hnodd : n%2=1) : n=1 := by
  have hnlt : n<3 := by
    by_cases hn : n<3
    · exact hn
    have hn3 : 3≤n := by omega
    have hdiv16 : 16 ∣ (2:Nat)^(n+1) := by
      have hd : (2:Nat)^4 ∣ (2:Nat)^(n+1) :=
        Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^4=16 by decide] using hd
    have hdiv2 : 2 ∣ a+3 := by omega
    rcases hdiv16 with ⟨w,hw⟩
    rcases hdiv2 with ⟨z,hz⟩
    rw [hw,hz] at hp
    have hdiv32 : 32 ∣ 64*t+16 := by
      refine ⟨w*z,?_⟩
      calc
        64*t+16 = (16*w)*(2*z) := hp
        _ = 32*(w*z) := by
          simp only [show (32:Nat)=16*2 by decide]
          ac_rfl
    rcases hdiv32 with ⟨u,hu⟩
    omega
  omega

private theorem first_parent (t a k : Nat)
    (hh : sectionPreimageAll a k 1 (64*t+14)) :
    (a=64*t+13 ∧ k=32*t+6) ∨
    (a=16*t+1 ∧ k=56*t+9) ∨
    (t=0 ∧ a=1 ∧ k=9) := by
  unfold sectionPreimageAll at hh
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp only [if_pos ha0, if_pos hk0] at hh
    · by_cases hk1 : k=1
      · simp only [if_pos ha0, if_neg hk0, if_pos hk1] at hh
        omega
      · simp only [if_pos ha0, if_neg hk0, if_neg hk1] at hh
        rcases hh with ⟨_,n,hpow,_⟩
        have hd : 8 ∣ (2:Nat)^n*8 := by
          refine ⟨(2:Nat)^n,?_⟩
          omega
        rcases hd with ⟨w,hw⟩
        omega
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
              rcases hh with ⟨h3,_⟩ | ⟨_,n,hp,hc⟩
              · omega
              · obtain ⟨ht,hn⟩ := no_special_depth t n (by omega)
                right
                right
                subst n
                omega
    · by_cases hk0 : k=0
      · simp only [if_neg ha0, if_neg ha1, if_pos hk0] at hh
        omega
      · by_cases hd : 2*k≤a
        · simp only [if_neg ha0, if_neg ha1, if_neg hk0, if_pos hd] at hh
          left
          omega
        · by_cases hae : a%2=0
          · simp only [if_neg ha0, if_neg ha1, if_neg hk0, if_neg hd, if_pos hae] at hh
            rcases hh with ⟨_,n,hpow,_⟩
            have hdiv2 : 2 ∣ (2:Nat)^n*(2*(a-1)+6) := by
              refine ⟨(2:Nat)^n*((a-1)+3),?_⟩
              have he : 2*(a-1)+6=2*((a-1)+3) := by omega
              rw [he]
              ac_rfl
            rcases hdiv2 with ⟨w,hw⟩
            omega
          · simp only [if_neg ha0, if_neg ha1, if_neg hk0, if_neg hd, if_neg hae] at hh
            rcases hh with ⟨h3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · have haodd : a%2=1 := by omega
              have he : 2*(a-1)+8=2*(a+3) := by omega
              rw [he] at hpow
              have hp : 64*t+16=2^(n+1)*(a+3) := by
                calc
                  64*t+16 = (2:Nat)^n*(2*(a+3)) := by omega
                  _ = ((2:Nat)^n*2)*(a+3) := by ac_rfl
                  _ = (2:Nat)^(n+1)*(a+3) := by rw [Nat.pow_succ]
              have hc : 2*k+a+9+3*n=128*t+31 := by omega
              have hnodd : n%2=1 := by omega
              have hn := odd_depth_only_one t a n haodd hp hnodd
              right
              left
              rw [hn] at hp hc
              simp only [show (2:Nat)^(1+1)=4 by decide] at hp
              omega

private theorem excluded_odd_mod2 (x y : Nat)
  (hodd : y%2=1) (hs : (x+y)%4=2)
  (hfirst : x≠5) : ¬ BB6.Agent3.CReach x y := by
  rintro ⟨time,hr⟩
  have he := BB6Agent38.blank_section_mod4 time x y hr hodd hs
  have hx := (Prod.mk.inj he).1
  exact hfirst hx

private theorem no_root_one_14_positive (t : Nat) (ht : 1≤t) :
    ¬ BB6.Agent3.CReach 1 (64*t+14) := by
  rintro ⟨time,hr⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at hr
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at hr
    | some p =>
      rcases p with ⟨a,k⟩
      have hedge : secNext (a,k)=some (1,64*t+14) := by
        simpa [BB6.Agent8Section.run,hp] using hr
      have hi := (section_preimage_all_iff a k 1 (64*t+14)).mp hedge
      rcases first_parent t a k hi with ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨hz,ha,hk⟩
      · have hr1 : BB6.Agent3.CReach (64*t+13) (32*t+6) :=
          ⟨n, by simpa only [ha,hk] using hp⟩
        have hr2 := (six_even_right_blank_reach_iff (64*t+13) (32*t+6)
          (by omega) (by omega) (by omega) (by omega)).mp hr1
        have hr2' : BB6.Agent3.CReach (96*t+17) (16*t+2) := by
          have ha : (64*t+13)+(32*t+6)-2=96*t+17 := by omega
          have hk : ((32*t+6)-2)/2=16*t+2 := by omega
          simpa only [ha,hk] using hr2
        have hr3 := (six_even_right_blank_reach_iff (96*t+17) (16*t+2)
          (by omega) (by omega) (by omega) (by omega)).mp hr2'
        have hr3' : BB6.Agent3.CReach (112*t+17) (8*t) := by
          have ha : (96*t+17)+(16*t+2)-2=112*t+17 := by omega
          have hk : ((16*t+2)-2)/2=8*t := by omega
          simpa only [ha,hk] using hr3
        have hr4 := (six_even_right_blank_reach_iff (112*t+17) (8*t)
          (by omega) (by omega) (by omega) (by omega)).mp hr3'
        have hr4' : BB6.Agent3.CReach (120*t+15) (4*t-1) := by
          have ha : (112*t+17)+(8*t)-2=120*t+15 := by omega
          have hk : ((8*t)-2)/2=4*t-1 := by omega
          simpa only [ha,hk] using hr4
        exact excluded_odd_mod2 (120*t+15) (4*t-1)
          (by omega) (by omega) (by omega) hr4'
      · have hparent : BB6.Agent3.CReach (16*t+1) (56*t+9) :=
          ⟨n, by simpa only [ha,hk] using hp⟩
        exact excluded_odd_mod2 (16*t+1) (56*t+9)
          (by omega) (by omega) (by omega) hparent
      · omega

private theorem no_root_one_14_zero : ¬ BB6.Agent3.CReach 1 14 := by
  rintro ⟨time,hr⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at hr
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at hr
    | some p =>
      rcases p with ⟨a,k⟩
      have hedge : secNext (a,k)=some (1,14) := by
        simpa [BB6.Agent8Section.run,hp] using hr
      have hi := (section_preimage_all_iff a k 1 14).mp hedge
      rcases first_parent 0 a k hi with ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨hz,ha,hk⟩
      · have hr1 : BB6.Agent3.CReach 13 6 :=
          ⟨n, by simpa only [ha,hk] using hp⟩
        have hr2 := (six_even_right_blank_reach_iff 13 6
          (by decide) (by decide) (by decide) (by decide)).mp hr1
        rcases hr2 with ⟨time,hr2⟩
        have hx : 13+6-2=17 := by decide
        have hk : (6-2)/2=2 := by decide
        rw [hx,hk] at hr2
        exact BB6.Agent15.blank_no_right_two time 17 hr2
      · have hparent : BB6.Agent3.CReach 1 9 :=
          ⟨n, by simpa only [ha,hk] using hp⟩
        exact excluded_odd_mod2 1 9
          (by decide) (by decide) (by decide) hparent
      · have hparent : BB6.Agent3.CReach 1 9 :=
          ⟨n, by simpa only [ha,hk] using hp⟩
        exact excluded_odd_mod2 1 9
          (by decide) (by decide) (by decide) hparent

/-- A full residue modulo 64 of low Machine C stop targets is
    genuine blank-unreachable, including the small base value. -/
theorem blank_no_one_14_mod64 (t : Nat) :
    ¬ BB6.Agent3.CReach 1 (64*t+14) := by
  by_cases ht : t=0
  · subst t
    simpa using no_root_one_14_zero
  · exact no_root_one_14_positive t (by omega)

/-- Every original low gate parameter m=58 modulo 64 misses the
    true blank-origin Machine C section orbit. -/
theorem blank_no_low_m_58 (m k : Nat) (hm : m%64=58)
    (hstop : k+3*m+4=2^(2*m+3)) : ¬ BB6.Agent3.CReach 1 k := by
  have hm58 : 58≤m := by omega
  have hpow64 : 64 ∣ (2:Nat)^(2*m+3) := by
    have hd : (2:Nat)^6 ∣ (2:Nat)^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^6=64 by decide] using hd
  have hmod : k%64=14 := by
    rcases hpow64 with ⟨w,hw⟩
    rw [hw] at hstop
    omega
  have hrepr : k=64*((k-14)/64)+14 := by omega
  rw [hrepr]
  exact blank_no_one_14_mod64 ((k-14)/64)

#print axioms blank_no_one_14_mod64
#print axioms blank_no_low_m_58
end BB6.Agent11C14
