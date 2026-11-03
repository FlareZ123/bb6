import OddSliver
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem eightodd_power_depth (x y n b : Nat)
    (hs : (x+y+1)%16=8) (hb : 4 ∣ b)
    (h : x+y+1=2^n*b) : n≤1 := by
  by_cases hn : n≤1
  · exact hn
  have hpow : 4 ∣ 2^n := by
    change 2^2 ∣ 2^n
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hpow
  obtain ⟨v,hv⟩ := hb
  have hdiv : 16 ∣ x+y+1 := by
    refine ⟨u*v, ?_⟩
    calc
      x+y+1 = 2^n*b := h
      _ = (4*u)*(4*v) := by rw [hu,hv]
      _ = 16*(u*v) := by ac_rfl
  omega

/-- Complete actual-source inverse on the second large odd-output wedge.
    All bounce depths except zero are excluded uniformly by 2-adic cost. -/
theorem odd_seven_parent_equations (a k x y : Nat)
    (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y+1)%16=8) (hsize : 23≤x+y)
    (h : secNext (a,k)=some (x,y)) :
    x+y=2*a+5 ∧ x+3*y=4*k+9 := by
  have hp := (section_preimage_all_iff a k x y).mp h
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at hp
        obtain ⟨_,n,hpow,_⟩ := hp
        have hd : 2 ∣ 2^n*8 := ⟨2^n*4,by omega⟩
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
              rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hd : 16 ∣ 2^n*16 := ⟨2^n,by omega⟩
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
            obtain ⟨_,n,hpow,_⟩ := hp
            have hd : 2 ∣ 2^n*(2*(a-1)+6) := by
              refine ⟨2^n*((a-1)+3),?_⟩
              calc
                2^n*(2*(a-1)+6)=2^n*(2*((a-1)+3)) := by congr 1 <;> omega
                _=2*(2^n*((a-1)+3)) := by ac_rfl
            omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg heven] at hp
            rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,hcost⟩
            · omega
            · have hb : 4 ∣ 2*(a-1)+8 := by
                refine ⟨(a-1)/2+2,?_⟩
                omega
              have hdepth := eightodd_power_depth x y n _ hs hb hpow
              cases n with
              | zero => simp at hpow hcost; omega
              | succ n =>
                  have hn : n=0 := by omega
                  subst n
                  simp at hpow hcost
                  omega

/-- Exact iff: each such output has precisely one genuine predecessor. -/
theorem odd_seven_parent_iff (a k x y : Nat)
    (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y+1)%16=8) (hsize : 23≤x+y) :
    secNext (a,k)=some (x,y) ↔
      x+y=2*a+5 ∧ x+3*y=4*k+9 := by
  constructor
  · exact odd_seven_parent_equations a k x y hx hy hy5 hs hsize
  · rintro ⟨hsum,hcost⟩
    have ha0 : a≠0 := by omega
    have ha1 : a≠1 := by omega
    have hk0 : k≠0 := by omega
    have hlow : ¬2*k≤a := by omega
    have hodd : a%2≠0 := by omega
    apply (section_preimage_all_iff a k x y).mpr
    simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_neg hodd]
    right
    refine ⟨by omega,0,?_,?_⟩ <;> simp <;> omega

/-- Infinite two-dimensional family of outputs invisible to the B8/M32
    reachability certificate, each with sole parent in the forbidden wedge. -/
theorem odd_seven_slope_blank_unreachable (p q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (8*p,8*p+64*q+23) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some s =>
          rcases s with ⟨a,k⟩
          have ht : secNext (a,k)=some (8*p,8*p+64*q+23) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hk⟩ := (odd_seven_parent_iff a k (8*p) (8*p+64*q+23)
            (by omega) (by omega) (by omega) (by omega) (by omega)).mp ht
          have haeq : a=8*p+32*q+9 := by omega
          have hkeq : k=8*p+48*q+15 := by omega
          have hparent : BB6.Agent8Section.run secNext n (some (5,1)) =
              some (8*p+32*q+9,8*p+48*q+15) := by rwa [haeq,hkeq] at hp
          exact odd_sliver_blank_unreachable (8*p+32*q+9) (8*p+48*q+15) n
            (by omega) (by omega) (by omega) (by omega) (by omega) hparent

#print axioms odd_seven_parent_equations
#print axioms odd_seven_parent_iff
#print axioms odd_seven_slope_blank_unreachable
end BB6.Agent3
