import FullSectionInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem oddodd_sum16_bounce_depth (n a k x y : Nat)
    (ha : 2≤a) (haeven : a%2=0) (hk : a<2*k)
    (hx : x%2=1) (hy : y%2=1) (hmod : (x+y)%32=16)
    (hsum : x+y=2^n*(2*(a-1)+6))
    (hcost : (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y) :
    n=0 ∨ n=2 := by
  have hnEven : n%2=0 := by omega
  by_cases hzero : n=0
  · exact Or.inl hzero
  by_cases htwo : n=2
  · exact Or.inr htwo
  have hn3 : 3≤n := by omega
  have hbase : ∃ v : Nat, 2*(a-1)+6=4*v := by
    refine ⟨a/2+1,?_⟩
    omega
  have hpow8 : 8 ∣ (2:Nat)^n := by
    change 2^3 ∣ 2^n
    exact Nat.pow_dvd_pow 2 hn3
  obtain ⟨w,hw⟩ := hpow8
  obtain ⟨v,hv⟩ := hbase
  have hdiv : 32 ∣ x+y := by
    refine ⟨w*v,?_⟩
    rw [hsum,hw,hv]
    calc
      8*w*(4*v)=(8*4)*(w*v) := by ac_rfl
      _=32*(w*v) := by rfl
  have hrem : (x+y)%32=0 := Nat.mod_eq_zero_of_dvd hdiv
  omega

/-- For source odd/odd outputs with sum 16 modulo32, every actual edge
    has ONE of exactly two explicitly arithmetical parent forms, from
    odd bounce depth zero or depth two. The distinction covers all
    possible source bounce depths without cutoff. -/
theorem oddodd_sum16_mod32_two_predecessors (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hsize : 64≤y)
    (hmod : (x+y)%32=16) (hed : secNext (a,k)=some (x,y)) :
    (a=(x+y-4)/2 ∧ k=(x+3*y-10)/4) ∨
    (a=(x+y-16)/8 ∧ k=(7*x+15*y-88)/16) := by
  have hc := (complete_section_inverse a k x y (by omega)).mp hed
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
        by_cases hn0 : n=0
        · subst n
          simp at hs
          omega
        by_cases hn1 : n=1
        · subst n
          simp at hs
          omega
        have hn2 : 2≤n := by omega
        have hp : 4 ∣ (2:Nat)^n := by
          change 2^2 ∣ 2^n
          exact Nat.pow_dvd_pow 2 hn2
        obtain ⟨w,hw⟩ := hp
        have hdiv : 32 ∣ x+y := by
          refine ⟨w,?_⟩
          rw [hs,hw]
          omega
        have hm : (x+y)%32=0 := Nat.mod_eq_zero_of_dvd hdiv
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
              have hdiv : 2 ∣ x+y+1 := by
                refine ⟨2^n*8,?_⟩
                rw [hs]
                omega
              have hm : (x+y+1)%2=0 := Nat.mod_eq_zero_of_dvd hdiv
              omega
    · simp only [if_neg ha1] at hc
      by_cases hk0 : k=0
      · simp only [if_pos hk0] at hc
      · simp only [if_neg hk0] at hc
        by_cases hlow : 2*k≤a
        · simp only [if_pos hlow] at hc
          omega
        · simp only [if_neg hlow] at hc
          by_cases he : a%2=0
          · simp only [if_pos he] at hc
            rcases hc with ⟨n,hs,hcost⟩
            have hd := oddodd_sum16_bounce_depth n a k x y
              (by omega) he (by omega) hx hy hmod hs hcost
            rcases hd with hzero | htwo
            · subst n
              simp at hs hcost
              left
              omega
            · subst n
              simp at hs hcost
              right
              omega
          · simp only [if_neg he] at hc
            rcases hc with ⟨n,hs,_⟩
            have hdiv : 2 ∣ x+y+1 := by
              refine ⟨2^n*(a+3),?_⟩
              have hf : 2*(a-1)+8=2*(a+3) := by omega
              rw [hs,hf]
              ac_rfl
            have hm : (x+y+1)%2=0 := Nat.mod_eq_zero_of_dvd hdiv
            omega

#print axioms oddodd_sum16_mod32_two_predecessors
end BB6.Agent3
