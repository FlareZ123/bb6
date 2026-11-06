import SectionAllInverse
import AffineNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4RightEight
open BB6.Agent46

private theorem odd_not_eight_multiple (u n : Nat) :
    8*u+11 ≠ 2^n*8 := by
  intro h
  have h1 : (8*u+11)%8=3 := by omega
  have h2 : (2^n*8)%8=0 := by simp [Nat.mul_mod]
  omega

private theorem four_not_sixteen_multiple (u n : Nat) :
    8*u+12 ≠ 2^n*16 := by
  intro h
  have h1 : (8*u+12)%8=4 := by omega
  have h2 : (2^n*16)%8=0 := by simp [Nat.mul_mod]
  omega

private theorem even_bounce_sum_even (n t : Nat) :
    (2^n*(2*t+6))%2=0 := by
  simp [Nat.mul_mod]

private theorem odd_bounce_sum_even (n t : Nat) :
    (2^n*(2*t+8))%2=0 := by
  simp [Nat.mul_mod]

private theorem odd_bounce_no_eight_three (u a k n : Nat)
    (ha : a%2=1) (hregion : a<2*k)
    (hs : 8*u+12=2^n*(2*(a-1)+8))
    (hc : (2*k-a+3)+(2*(a-1)+8)+3*n=8*u+21) : False := by
  cases n with
  | zero =>
      simp at hs hc
      omega
  | succ n =>
      obtain ⟨z,hz⟩ : ∃ z:Nat, a=2*z+1 := ⟨a/2,by omega⟩
      rw [hz] at hs
      have hf : 2*(2*z+1-1)+8=4*(z+2) := by omega
      rw [hf,Nat.pow_succ] at hs
      have hh : 2^n*2*(4*(z+2))=8*(2^n*(z+2)) := by
        calc
          _ = (2*4)*(2^n*(z+2)) := by ac_rfl
          _ = _ := by simp
      rw [hh] at hs
      omega

/-- Every genuine source transition into (8u+3,8) has exactly the
    direct predecessor (8u+9,3). No extra recursive-bounce parent exists. -/
theorem target_three_eight_unique_parent (a k u : Nat)
    (h : secNext (a,k)=some (8*u+3,8)) :
    a=8*u+9 ∧ k=3 := by
  have hi := (section_preimage_all_iff a k (8*u+3) 8).mp h
  unfold sectionPreimageAll at hi
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [ha0,hk0] at hi
    · by_cases hk1 : k=1
      · simp [ha0,hk0,hk1] at hi
      · simp [ha0,hk0,hk1] at hi
        obtain ⟨n,hs,_⟩ := hi
        exact False.elim (odd_not_eight_multiple u n hs)
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0] at hi
      · by_cases hk1 : k=1
        · simp [ha0,ha1,hk0,hk1] at hi
        · by_cases hk2 : k=2
          · simp [ha0,ha1,hk0,hk1,hk2] at hi
          · by_cases hk3 : k=3
            · simp [ha0,ha1,hk0,hk1,hk2,hk3] at hi
            · simp [ha0,ha1,hk0,hk1,hk2,hk3] at hi
              obtain ⟨n,hs,_⟩ := hi
              exact False.elim (four_not_sixteen_multiple u n hs)
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0] at hi
      · by_cases hlow : 2*k≤a
        · simp [ha0,ha1,hk0,hlow] at hi
          omega
        · by_cases heven : a%2=0
          · simp [ha0,ha1,hk0,hlow,heven] at hi
            obtain ⟨n,hs,_⟩ := hi
            have hm := even_bounce_sum_even n (a-1)
            rw [←hs] at hm
            omega
          · simp [ha0,ha1,hk0,hlow,heven] at hi
            obtain ⟨n,hs,hc⟩ := hi
            exact False.elim (odd_bounce_no_eight_three u a k n
              (by omega) (by omega) hs (by omega))

/-- Source image of the right-three fibre has even first coordinate. -/
theorem section_right_three_even (a k x : Nat)
    (h : secNext (a,k)=some (x,3)) : x%2=0 := by
  have hi := (section_preimage_all_iff a k x 3).mp h
  unfold sectionPreimageAll at hi
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [ha0,hk0] at hi
    · by_cases hk1 : k=1
      · simp [ha0,hk0,hk1] at hi
      · simp [ha0,hk0,hk1] at hi
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0] at hi
      · by_cases hk1 : k=1
        · simp [ha0,ha1,hk0,hk1] at hi
          omega
        · by_cases hk2 : k=2
          · simp [ha0,ha1,hk0,hk1,hk2] at hi
          · by_cases hk3 : k=3
            · simp [ha0,ha1,hk0,hk1,hk2,hk3] at hi
            · simp [ha0,ha1,hk0,hk1,hk2,hk3] at hi
              obtain ⟨n,hs,_⟩ := hi
              have hp : (2^n*16)%2=0 := by simp [Nat.mul_mod]
              omega
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0] at hi
      · by_cases hlow : 2*k≤a
        · simp [ha0,ha1,hk0,hlow] at hi
          omega
        · by_cases heven : a%2=0
          · simp [ha0,ha1,hk0,hlow,heven] at hi
          · simp [ha0,ha1,hk0,hlow,heven] at hi
            obtain ⟨n,hs,_⟩ := hi
            have hp := odd_bounce_sum_even n (a-1)
            omega

/-- No section of the authentic blank orbit has odd left coordinate and
    right counter three, including the initial exceptional section. -/
theorem blank_no_odd_three (a : Nat) (ha : a%2=1) :
    ¬ BB6.Agent15.CReach a 3 := by
  rintro ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
          obtain ⟨b,c⟩ := p
          have he : secNext (b,c)=some (a,3) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          have hx := section_right_three_even b c a he
          omega

/-- Original-machine section: a full infinite family of right-eight
    states is unreachable from its genuine blank origin. -/
theorem blank_no_three_eight (u : Nat) :
    ¬ BB6.Agent15.CReach (8*u+3) 8 := by
  rintro ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
          obtain ⟨a,k⟩ := p
          have he : secNext (a,k)=some (8*u+3,8) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          obtain ⟨ha,hk⟩ := target_three_eight_unique_parent a k u he
          subst a
          subst k
          exact blank_no_odd_three (8*u+9) (by omega) ⟨t,hp⟩

#print axioms target_three_eight_unique_parent
#print axioms section_right_three_even
#print axioms blank_no_odd_three
#print axioms blank_no_three_eight
end BB6.Agent4RightEight
