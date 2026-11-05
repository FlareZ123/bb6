import BounceInverse
import FastSectionDef
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

private theorem pow_two_even_new (n : Nat) (hn : 1≤n) :
    ∃ u : Nat, 2^n=2*u := by
  obtain ⟨m,hm⟩ : ∃ m, n=m+1 := ⟨n-1,by omega⟩
  refine ⟨2^m,?_⟩
  rw [hm,Nat.pow_succ]
  omega

/-- Uniform forced predecessor in an even/even output sector that the
    former sum-one affine theorem did not cover. -/
theorem section_eveneven_sum_four_mod8_inverse (a k x y : Nat)
    (hy : 6≤y) (hx : x%2=0) (hyEven : y%2=0)
    (hs : (x+y)%8=4)
    (h : secNext (a,k)=some (x,y)) :
    a=x+y-2 ∧ k=(y-2)/2 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h <;> omega
      · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        obtain ⟨n,hn,_⟩ :=
          bounce_odd_output_invariants (2*k+1) 1 x y (by decide) hb
        have hm : x+y=8*(2^n) := by omega
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h <;> omega
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h <;> omega
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h <;> omega
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h <;> omega
            · have hb : (bounce 4 (2*k-3)).2=some (x,y) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              obtain ⟨n,hn,_⟩ :=
                bounce_even_output_invariants (2*k-3) 4 x y
                  (by decide) (by omega) hb
              have hm : x+y+1=16*(2^n) := by omega
              omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h <;> omega
      · by_cases hreg : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hreg] at h
          constructor <;> omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hreg] using h
          by_cases he : a%2=0
          · have hodd : (a-1)%2=1 := by omega
            obtain ⟨n,hsum,hcost⟩ :=
              bounce_odd_output_invariants (2*k-a+3) (a-1) x y hodd hb
            have hsum' : x+y=2^n*(2*(a-1)+6) := by omega
            have hcost' : 2*k+a+7+3*n=x+2*y := by omega
            by_cases hn0 : n=0
            · subst n
              simp at hsum' hcost'
              omega
            · obtain ⟨u,hu⟩ := pow_two_even_new n (by omega)
              obtain ⟨v,hv⟩ : ∃ v : Nat, 2*(a-1)+6=4*v :=
                ⟨a/2+1,by omega⟩
              have hm : x+y=8*(u*v) := by
                calc
                  x+y=2^n*(2*(a-1)+6) := hsum'
                  _ = (2*u)*(4*v) := by rw [hu,hv]
                  _ = 8*(u*v) := by ring
              omega
          · have heven : (a-1)%2=0 := by omega
            obtain ⟨n,hn,_⟩ :=
              bounce_even_output_invariants (2*k-a+3) (a-1)
                x y heven (by omega) hb
            have hm : x+y+1=2*(2^n*(a+3)) := by
              calc
                x+y+1=2^n*(2*(a-1)+8) := hn
                _ = 2^n*(2*(a+3)) := by congr 1 <;> omega
                _ = 2*(2^n*(a+3)) := by ac_rfl
            omega

/-- When the second coordinate is even and the sum is two mod four,
    no bounce return can be the parent; the direct affine predecessor is forced. -/
theorem section_even_sum_two_mod4_inverse (a k x y : Nat)
    (hy : 6≤y) (hyEven : y%2=0) (hs : (x+y)%4=2)
    (h : secNext (a,k)=some (x,y)) :
    a=x+y-2 ∧ k=(y-2)/2 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h <;> omega
      · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        exact False.elim ((BB6Agent38.bounce_mod4 _ _ _ _ hb) hs)
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h <;> omega
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h <;> omega
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h <;> omega
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h <;> omega
            · have hb : (bounce 4 (2*k-3)).2=some (x,y) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              exact False.elim ((BB6Agent38.bounce_mod4 _ _ _ _ hb) hs)
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h <;> omega
      · by_cases hreg : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hreg] at h
          constructor <;> omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hreg] using h
          exact False.elim ((BB6Agent38.bounce_mod4 _ _ _ _ hb) hs)

#print axioms section_eveneven_sum_four_mod8_inverse
#print axioms section_even_sum_two_mod4_inverse
end BB6.Agent46
