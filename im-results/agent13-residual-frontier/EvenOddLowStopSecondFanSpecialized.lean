import FullSectionInverse
import EvenOddLowStopEvenUnique
import OddOddLowVal
import EvenRightSixOrbit
import One307Source
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace BB6.Agent13LowSecondFanSpecialized
open BB6.Agent46

/-- Exact original-section inverse criterion for odd x, even y and
    section mass x+y+1 congruent to 8 mod 16. The entire unbounded
    high-bounce fan collapses to depth one by cost parity and divisibility. -/
theorem depth_one_or_direct (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=0) (hy8 : 8≤y)
    (hm : (x+y+1)%16=8) :
    sectionPreimageCriterion a k x y ↔
      (a=x+y-2 ∧ k=(y-2)/2) ∨
      (a%2=1 ∧ 3≤a ∧ a<2*k ∧ x+y+1=4*(a+3) ∧ 2*k+a+10=x+2*y) := by
  constructor
  · intro h
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,hk0] at h
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,ha0,hk0,hk1] at h
          omega
        · simp only [sectionPreimageCriterion,if_pos ha0,if_neg hk0,if_neg hk1] at h
          obtain ⟨n, hp, _⟩ := h
          omega
    · by_cases ha1 : a=1
      · by_cases hk0 : k=0
        · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
        · by_cases hk1 : k=1
          · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1] at h
          · by_cases hk2 : k=2
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2] at h
              omega
            · by_cases hk3 : k=3
              · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at h
                omega
              · simp only [sectionPreimageCriterion,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
                obtain ⟨n,hp,_⟩ := h
                omega
      · by_cases hk0 : k=0
        · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
        · by_cases hl : 2*k≤a
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_pos hl] at h
            left
            omega
          · by_cases he : a%2=0
            · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hl,if_pos he] at h
              obtain ⟨n,hp,_⟩ := h
              have heven : (x+y)%2=0 := by rw [hp]; simp [Nat.mul_mod]
              omega
            · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hl,if_neg he] at h
              obtain ⟨n,hp,hc⟩ := h
              have hnodd : n%2=1 := by omega
              have hnlt : n<3 := by
                by_cases hn : n<3
                · exact hn
                · exfalso
                  have hdiv : (2:Nat)^3 ∣ 2^n := Nat.pow_dvd_pow 2 (by omega)
                  have h8 : 8∣2^n := by simpa using hdiv
                  obtain ⟨b,hb⟩ := h8
                  rw [hb,show 2*(a-1)+8=2*(a+3) by omega] at hp
                  have hh : 16∣x+y+1 := by
                    refine ⟨b*(a+3),?_⟩
                    calc
                      x+y+1 = 8*b*(2*(a+3)) := hp
                      _ = 16*(b*(a+3)) := by rw [show 16=8*2 by decide]; ac_rfl
                  have := Nat.mod_eq_zero_of_dvd hh
                  omega
              have hn1 : n=1 := by omega
              subst n
              simp only [Nat.pow_one] at hp
              right
              omega
  · rintro (⟨ha,hk⟩ | ⟨haodd,ha3,hr,hmass,hcost⟩)
    · subst a
      subst k
      have ha0 : x+y-2≠0 := by omega
      have ha1 : x+y-2≠1 := by omega
      have hk0 : (y-2)/2≠0 := by omega
      have hl : 2*((y-2)/2)≤x+y-2 := by omega
      simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_pos hl]
      omega
    · have ha0 : a≠0 := by omega
      have ha1 : a≠1 := by omega
      have hk0 : k≠0 := by omega
      have hl : ¬ 2*k≤a := by omega
      have he : ¬ a%2=0 := by omega
      simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hl,if_neg he]
      refine ⟨1,?_,?_⟩ <;> omega

theorem source_depth_one_or_direct (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=0) (hy8 : 8≤y)
    (hm : (x+y+1)%16=8) :
    secNext (a,k)=some (x,y) ↔
      (a=x+y-2 ∧ k=(y-2)/2) ∨
      (a%2=1 ∧ 3≤a ∧ a<2*k ∧ x+y+1=4*(a+3) ∧ 2*k+a+10=x+2*y) :=
  (complete_section_inverse a k x y (by omega)).trans
    (depth_one_or_direct a k x y hx hy hy8 hm)

theorem specialized_target (u : Nat) (hu : u%256=171) :
    (173*u+24)%2=1 ∧ ((339*u+47)/2)%2=0 ∧
    8≤(339*u+47)/2 ∧ (173*u+24+(339*u+47)/2+1)%16=8 := by omega

theorem high_parent_arithmetic (u a k : Nat) (hu : u%256=171)
    (ha : a%2=1) (_ha3 : 3≤a) (hr : a<2*k)
    (hm : 173*u+24+(339*u+47)/2+1=4*(a+3))
    (hc : 2*k+a+10=173*u+24+2*((339*u+47)/2)) :
    k%2=1 ∧ 5≤k ∧ (a+k)%4=0 ∧ (a+k)%16≠0 ∧ 24≤a+k ∧
    5≤(a+3*k-10)/4 ∧ ((a+3*k-10)/4)%2=1 ∧
    ((a+k-4)/2+(a+3*k-10)/4)%4=1 := by
  have haEq : 8*a=685*u+73 := by omega
  have hkEq : 16*k=3411*u+415 := by omega
  omega

theorem direct_parent_arithmetic (u : Nat) (hu : u%256=171) :
    let X:=173*u+24
    let Y:=(339*u+47)/2
    let a:=X+Y-2
    let k:=(Y-2)/2
    let e:=(a+k-4)/2
    let f:=(a+3*k-10)/4
    let g:=e+f-2
    let h:=(f-2)/2
    a%2=1 ∧ k%2=1 ∧ 5≤k ∧ (a+k)%4=0 ∧ (a+k)%16≠0 ∧ 24≤a+k ∧
    6≤f ∧ f%2=0 ∧ (e+f)%8=4 ∧ 5≤h ∧ h%2=1 ∧ (g+h)%4=1 := by
  dsimp
  omega

/-- All payloads u=171 mod 256 are forbidden at P, independent
    of the exponential low-stop relation. Both exact parent types
    terminate at the source odd-image obstruction. -/
theorem second_payload_unreachable (u : Nat) (hu : u%256=171) :
    ¬ BB6.Agent3.CReach (173*u+24) ((339*u+47)/2) := by
  intro root
  obtain ⟨hx,hy,hy8,hm⟩ := specialized_target u hu
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (173*u+24) ((339*u+47)/2) (by omega) root
  rcases (source_depth_one_or_direct a k _ _ hx hy hy8 hm).mp hedge with hdir|hhigh
  · obtain ⟨ha,hk⟩ := hdir
    subst a
    subst k
    obtain ⟨ha,hk,hk5,h4,h16,hsize,hf6,hfe,hefsum,hh5,hho,hghsum⟩ :=
      direct_parent_arithmetic u hu
    have hE := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (173*u+24+(339*u+47)/2-2) (((339*u+47)/2-2)/2)
      ha hk hk5 h4 h16 hsize).mp hpre
    let e := (173*u+24+(339*u+47)/2-2+((339*u+47)/2-2)/2-4)/2
    let f := (173*u+24+(339*u+47)/2-2+3*(((339*u+47)/2-2)/2)-10)/4
    have hE' : BB6.Agent3.CReach e f := hE
    have hF := (six_even_right_blank_reach_iff e f hf6 hfe
      (by change (e+f)%8≠0; dsimp [e,f]; omega)
      (by change (e+f)%8≠7; dsimp [e,f]; omega)).mp hE'
    exact BB6.Agent13TwoParent.odd_forbidden_image
      (e+f-2) ((f-2)/2) hh5 hho (Or.inl hghsum) hF
  · obtain ⟨ha,ha3,hr,hmass,hcost⟩ := hhigh
    obtain ⟨hk,hk5,h4,h16,hsize,hy5,hyo,hsum⟩ :=
      high_parent_arithmetic u a k hu ha ha3 hr hmass hcost
    have hp := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      a k ha hk hk5 h4 h16 hsize).mp hpre
    exact BB6.Agent13TwoParent.odd_forbidden_image
      ((a+k-4)/2) ((a+3*k-10)/4) hy5 hyo (Or.inl hsum) hp

theorem low_stop_arithmetic (z m k : Nat)
    (hm : m=512*z+67) (hz : z%128=14)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ∃ u, k=256*u+51 ∧ u+6*z+1=2^(1024*z+129) ∧ u%256=171 := by
  have hpow : 2^(2*m+3)=256*2^(1024*z+129) := by
    rw [show 2*m+3=(1024*z+129)+8 by omega,Nat.pow_add]
    change 2^(1024*z+129)*256=256*2^(1024*z+129)
    exact Nat.mul_comm _ _
  rw [hpow] at hstop
  have hkmod : k%256=51 := by omega
  let u := k/256
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 256
    dsimp [u]
    omega
  have hu : u+6*z+1=2^(1024*z+129) := by omega
  have hdiv : (2:Nat)^8 ∣ 2^(1024*z+129) := Nat.pow_dvd_pow 2 (by omega)
  have hmod : (2^(1024*z+129))%256=0 := Nat.mod_eq_zero_of_dvd hdiv
  exact ⟨u,hk,hu,by omega⟩

/-- Complete blank-root exclusion of the authentic low stopping cylinder. -/
theorem low_stop_m67_z14_mod128_unreachable
    (z m k : Nat)
    (hm : m=512*z+67) (hz : z%128=14)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  obtain ⟨u,hk,hu,hu256⟩ := low_stop_arithmetic z m k hm hz hstop
  intro h
  rw [hk] at h
  have hR := BB6.Agent13One307.four_step_to_rectangle u h
  have hP := BB6.Agent13LowEvenRoot.even_low_ray_reach_forces_unique_parent
    z u hu (by omega) hR
  exact second_payload_unreachable u hu256 hP

#print axioms depth_one_or_direct
#print axioms source_depth_one_or_direct
#print axioms second_payload_unreachable
#print axioms low_stop_m67_z14_mod128_unreachable
end BB6.Agent13LowSecondFanSpecialized
