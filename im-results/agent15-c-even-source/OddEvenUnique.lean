import FullSectionInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- In the high odd-first bounce, an odd/even output cannot have
    coordinate sum 3 modulo 8: depth zero violates parity; positive
    depth forces sum congruent to 7 modulo 8. -/
private theorem no_odd_high (a k x y n : Nat)
    (ha : a%2=1) (hregion : a<2*k) (hx : x%2=1) (hy : y%2=0)
    (hs : (x+y)%8=3)
    (hp : x+y+1=2^n*(2*(a-1)+8))
    (hc : (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) : False := by
  cases n with
  | zero =>
      simp at hp hc
      omega
  | succ n =>
      have hb : 2*(a-1)+8=4*(a/2+2) := by omega
      have hdiv : x+y+1=8*(2^n*(a/2+2)) := by
        calc
          x+y+1=2^(n+1)*(2*(a-1)+8) := hp
          _=2^(n+1)*(4*(a/2+2)) := by rw [hb]
          _=8*(2^n*(a/2+2)) := by
            rw [Nat.pow_succ]
            calc
              2^n*2*(4*(a/2+2))=(2*4)*(2^n*(a/2+2)) := by ac_rfl
              _=8*(2^n*(a/2+2)) := by
                have hh : (2:Nat)*4=8 := by decide
                rw [hh]
      omega

/-- Complete input-side inverse for the odd/even sum-three-mod-eight cone. -/
theorem odd_even_criterion_forces_affine (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=0) (h6 : 6≤y)
    (hs : (x+y)%8=3)
    (h : sectionPreimageCriterion a k x y) :
    a=x+y-2 ∧ k=(y-2)/2 := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [sectionPreimageCriterion,ha0,hk0,hk1] at h
        omega
      · simp only [sectionPreimageCriterion,ha0,hk0,hk1,ite_true,ite_false] at h
        rcases h with ⟨n,hpow,_⟩
        have hr : x+y=8*(2^n) := by simpa [Nat.mul_comm] using hpow
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
            · simp only [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3,ite_true,ite_false] at h
              rcases h with ⟨n,hpow,_⟩
              have ht : x+y+1=16*(2^n) := by simpa [Nat.mul_comm] using hpow
              omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageCriterion,ha0,ha1,hk0,hlow] at h
          omega
        · by_cases hae : a%2=0
          · simp only [sectionPreimageCriterion,ha0,ha1,hk0,hlow,hae,ite_true,ite_false] at h
            rcases h with ⟨n,hpow,_⟩
            have he : x+y=2*(2^n*(a+2)) := by
              have hb : 2*(a-1)+6=2*(a+2) := by omega
              rw [hb] at hpow
              calc
                x+y=2^n*(2*(a+2)) := hpow
                _=2*(2^n*(a+2)) := by ac_rfl
            omega
          · simp only [sectionPreimageCriterion,ha0,ha1,hk0,hlow,hae,ite_true,ite_false] at h
            rcases h with ⟨n,hpow,hcost⟩
            exact False.elim
              (no_odd_high a k x y n (by omega) (by omega) hx hy hs hpow hcost)

theorem odd_even_criterion_iff_affine (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=0) (h6 : 6≤y)
    (hs : (x+y)%8=3) :
    sectionPreimageCriterion a k x y ↔
      a=x+y-2 ∧ k=(y-2)/2 := by
  constructor
  · exact odd_even_criterion_forces_affine a k x y hx hy h6 hs
  · rintro ⟨rfl,rfl⟩
    have ha0 : x+y-2≠0 := by omega
    have ha1 : x+y-2≠1 := by omega
    have hk0 : (y-2)/2≠0 := by omega
    have hlow : 2*((y-2)/2)≤x+y-2 := by omega
    simp [sectionPreimageCriterion,ha0,ha1,hk0,hlow]
    omega

/-- All source-predecessor branches, including unbounded bounce depth. -/
theorem section_odd_even_iff_affine (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=0) (h6 : 6≤y)
    (hs : (x+y)%8=3) :
    secNext (a,k)=some (x,y) ↔
      a=x+y-2 ∧ k=(y-2)/2 := by
  rw [complete_section_inverse a k x y (by omega)]
  exact odd_even_criterion_iff_affine a k x y hx hy h6 hs

#print axioms section_odd_even_iff_affine
end BB6.Agent46
