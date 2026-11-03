import SectionAllInverse
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem eight_output_pow_no_zero (x y n : Nat)
    (hs : (x+y)%16=8) (hsize : 24≤x+y)
    (h : x+y=2^n*8) : False := by
  cases n with
  | zero => simp at h; omega
  | succ n =>
      rw [Nat.pow_succ] at h
      have hd : 16 ∣ x+y := by
        refine ⟨2^n,?_⟩
        omega
      omega

private theorem eight_output_pow_depth (x y n b : Nat)
    (hs : (x+y)%16=8) (hb : 4 ∣ b)
    (h : x+y=2^n*b) : n≤1 := by
  by_cases hn : n≤1
  · exact hn
  have hpow : 4 ∣ 2^n := by
    change 2^2 ∣ 2^n
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hpow
  obtain ⟨v,hv⟩ := hb
  have hdiv : 16 ∣ x+y := by
    refine ⟨u*v, ?_⟩
    calc
      x+y = 2^n*b := h
      _ = (4*u)*(4*v) := by rw [hu,hv]
      _ = 16*(u*v) := by ac_rfl
  omega

/-- Every output in the odd two-dimensional sliver has just one
    possible source, characterized by two linear equations. -/
theorem odd_sliver_parent_equations (a k x y : Nat)
    (hx : x%8=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=8) (hsize : 24≤x+y)
    (h : secNext (a,k)=some (x,y)) :
    x+y=2*a+4 ∧ x+3*y=4*k+10 := by
  have hp := (section_preimage_all_iff a k x y).mp h
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at hp
        obtain ⟨_,n,hpow,_⟩ := hp
        exact False.elim (eight_output_pow_no_zero x y n hs hsize hpow)
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
              rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hd : 2 ∣ 2^n*16 := ⟨2^n*8,by omega⟩
                omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageAll,ha0,ha1,hk0,hlow] at hp
          omega
        · by_cases heven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos heven] at hp
            obtain ⟨_,n,hpow,hcost⟩ := hp
            have hbase : 4 ∣ 2*(a-1)+6 := by
              refine ⟨a/2+1,?_⟩
              omega
            have hdepth := eight_output_pow_depth x y n _ hs hbase hpow
            cases n with
            | zero => simp at hpow hcost; omega
            | succ n =>
                have hn : n=0 := by omega
                subst n
                simp at hpow hcost
                omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg heven] at hp
            rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hd : 2 ∣ 2^n*(2*(a-1)+8) := by
                refine ⟨2^n*((a-1)+4),?_⟩
                calc
                  2^n*(2*(a-1)+8)=2^n*(2*((a-1)+4)) := by congr 1 <;> omega
                  _=2*(2^n*((a-1)+4)) := by ac_rfl
              omega

/-- The sole parent, when it exists, belongs to the previously
    certified true-blank forbidden parity cone. -/
theorem odd_sliver_parents_forbidden (a k x y : Nat)
    (hx : x%8=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=8) (hsize : 24≤x+y)
    (h : secNext (a,k)=some (x,y)) :
    a%4=2 ∧ k%4=3 ∧ 7≤k := by
  obtain ⟨hsum,hcost⟩ := odd_sliver_parent_equations a k x y hx hy hy5 hs hsize h
  omega

/-- Genuinely blank-origin all-time exclusion for the complete
    two-dimensional congruence wedge; no finite-time cutoff. -/
theorem odd_sliver_blank_unreachable (x y time : Nat)
    (hx : x%8=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=8) (hsize : 24≤x+y) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h; omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          rcases p with ⟨a,k⟩
          have he : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hk,hk7⟩ := odd_sliver_parents_forbidden a k x y hx hy hy5 hs hsize he
          let u := a/4
          let v := k/4-1
          have haeq : a=4*u+2 := by dsimp [u]; omega
          have hkeq : k=4*(v+1)+3 := by dsimp [v]; omega
          rw [haeq,hkeq] at hp
          exact blank_no_two_three_high n u v hp

#print axioms odd_sliver_parent_equations
#print axioms odd_sliver_parents_forbidden
#print axioms odd_sliver_blank_unreachable

/-- First explicit two-parameter unavailable sector, including the
    previous one-seven target line as p=0,q>=1. -/
theorem sliver_A_blank_unreachable (p q time : Nat) (hpq : 1≤p+q) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (16*p+1,16*q+7) := by
  apply odd_sliver_blank_unreachable
  all_goals omega

/-- The complementary two-parameter unavailable sector. -/
theorem sliver_B_blank_unreachable (p q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (16*p+9,16*q+15) := by
  apply odd_sliver_blank_unreachable
  all_goals omega

#print axioms sliver_A_blank_unreachable
#print axioms sliver_B_blank_unreachable
end BB6.Agent3
