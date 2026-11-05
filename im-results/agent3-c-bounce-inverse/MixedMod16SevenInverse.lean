import FullSectionInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- In an even-bounce source branch with the output sum+1 equal to
    8 modulo16, the exponential recursion depth is exactly one when
    the section's genuine input/output parity and counter equations hold.
    Neither simulated depth limits nor candidate search are used. -/
private theorem even_branch_mod16_one (n a k x y : Nat)
    (ha : 2≤a) (hodd : a%2=1) (hk : a<2*k)
    (hx : x%2=1) (hy : y%2=0) (hmod : (x+y+1)%16=8)
    (hpow : x+y+1=2^n*(2*(a-1)+8))
    (hcost : (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) :
    n=1 ∧ 4*(a+3)=x+y+1 ∧ 2*k=x+2*y-a-10 := by
  have hbase : ∃ v : Nat, 2*(a-1)+8=4*v := by
    refine ⟨(a+3)/2,?_⟩
    omega
  by_cases hn0 : n=0
  · subst n
    simp at hpow
    omega
  by_cases hn1 : n=1
  · subst n
    rw [show (2:Nat)^1=2 by decide] at hpow
    omega
  have hn2 : 2≤n := by omega
  have hdiv : 16 ∣ 2^n*(2*(a-1)+8) := by
    obtain ⟨v,hv⟩ := hbase
    have hpow4 : 4 ∣ 2^n := by
      change 2^2 ∣ 2^n
      exact Nat.pow_dvd_pow 2 hn2
    obtain ⟨w,hw⟩ := hpow4
    refine ⟨w*v,?_⟩
    rw [hw,hv]
    calc
      4*w*(4*v) = (4*4)*(w*v) := by ac_rfl
      _ = 16*(w*v) := by rfl
  have hrem : (x+y+1)%16=0 := by
    rw [hpow]
    exact Nat.mod_eq_zero_of_dvd hdiv
  omega

/-- At most TWO exact possible predecessor forms in the previously
    branching original-source even-right sector y even, x odd,
    x+y+1=8(mod16): one direct section edge or a depth-one even bounce.
    This is source-complete, independent of counter size or bounce budget. -/
theorem mod16_seven_exact_predecessors (a k x y : Nat)
    (hy : 5≤y) (hx : x%2=1) (he : y%2=0)
    (hmod : (x+y+1)%16=8)
    (hed : secNext (a,k)=some (x,y)) :
    (a=x+y-2 ∧ k=(y-2)/2) ∨
    (4*(a+3)=x+y+1 ∧ 2*k=x+2*y-a-10) := by
  have hc := (complete_section_inverse a k x y hy).mp hed
  unfold sectionPreimageCriterion at hc
  by_cases ha0 : a=0
  · simp only [if_pos ha0] at hc
    by_cases hk0 : k=0
    · simp only [if_pos hk0] at hc
    · simp only [if_neg hk0] at hc
      by_cases hk1 : k=1
      · simp only [if_pos hk1] at hc
        omega
      · simp only [if_neg hk1] at hc
        rcases hc with ⟨n,hs,_⟩
        have hdiv : 2 ∣ 2^n*8 := by
          refine ⟨2^n*4,?_⟩
          omega
        have hsum : (x+y)%2=0 := by
          rw [hs]
          exact Nat.mod_eq_zero_of_dvd hdiv
        omega
  · simp only [if_neg ha0] at hc
    by_cases ha1 : a=1
    · simp only [if_pos ha1] at hc
      by_cases hk0 : k=0
      · simp only [if_pos hk0] at hc
      · simp only [if_neg hk0] at hc
        by_cases hk1 : k=1
        · simp only [if_pos hk1] at hc
        · simp only [if_neg hk1] at hc
          by_cases hk2 : k=2
          · simp only [if_pos hk2] at hc
            omega
          · simp only [if_neg hk2] at hc
            by_cases hk3 : k=3
            · simp only [if_pos hk3] at hc
              omega
            · simp only [if_neg hk3] at hc
              rcases hc with ⟨n,hs,_⟩
              have hdiv : 16 ∣ 2^n*16 := by
                refine ⟨2^n,?_⟩
                omega
              have hsum : (x+y+1)%16=0 := by
                rw [hs]
                exact Nat.mod_eq_zero_of_dvd hdiv
              omega
    · simp only [if_neg ha1] at hc
      by_cases hk0 : k=0
      · simp only [if_pos hk0] at hc
      · simp only [if_neg hk0] at hc
        by_cases hlow : 2*k≤a
        · simp only [if_pos hlow] at hc
          left
          omega
        · simp only [if_neg hlow] at hc
          by_cases haEven : a%2=0
          · simp only [if_pos haEven] at hc
            rcases hc with ⟨n,hs,_⟩
            have hdiv : 2 ∣ 2^n*(2*(a-1)+6) := by
              refine ⟨2^n*((a-1)+3),?_⟩
              have hf : 2*(a-1)+6=2*((a-1)+3) := by omega
              rw [hf]
              ac_rfl
            have hsum : (x+y)%2=0 := by
              rw [hs]
              exact Nat.mod_eq_zero_of_dvd hdiv
            omega
          · simp only [if_neg haEven] at hc
            rcases hc with ⟨n,hs,hcounter⟩
            have hbranch := even_branch_mod16_one n a k x y
              (by omega) (by omega) (by omega) hx he hmod hs hcounter
            exact Or.inr ⟨hbranch.2.1,hbranch.2.2⟩

#print axioms mod16_seven_exact_predecessors
end BB6.Agent3
