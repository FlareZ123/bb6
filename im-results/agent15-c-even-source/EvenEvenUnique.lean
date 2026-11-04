import FullSectionInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- A high even-bounce predecessor would force a sum divisible by eight.
    Its zero-depth alternative contradicts parity of the exact bounce cost. -/
private theorem no_even_high (a k x y n : Nat)
    (ha : a%2=0) (hx : x%2=0) (hy : y%2=0)
    (hs : (x+y)%8≠0)
    (hp : x+y=2^n*(2*a+4))
    (hc : (2*k-a+3)+(2*a+4)+3*n=x+2*y) : False := by
  cases n with
  | zero =>
      simp at hp hc
      omega
  | succ n =>
      have ha' : a=2*(a/2) := by omega
      have hb : 2*a+4=4*(a/2+1) := by omega
      have hdiv : x+y=8*(2^n*(a/2+1)) := by
        calc
          x+y=2^(n+1)*(2*a+4) := hp
          _ = 2^(n+1)*(4*(a/2+1)) := by rw [hb]
          _ = 8*(2^n*(a/2+1)) := by
            rw [Nat.pow_succ]
            have hh : (2:Nat)*4=8 := by decide
            calc
              2^n*2*(4*(a/2+1)) = (2*4)*(2^n*(a/2+1)) := by ac_rfl
              _ = 8*(2^n*(a/2+1)) := by rw [hh]
      omega

/-- Extra exact inverse sector for even/even outputs with y>=6 and
    total coordinate sum not divisible by eight. -/
theorem even_even_criterion_forces_affine (a k x y : Nat)
    (hx : x%2=0) (hy : y%2=0) (h6 : 6≤y)
    (hs : (x+y)%8≠0)
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
            rcases h with ⟨n,hpow,hcost⟩
            have haa : 2*(a-1)+6=2*a+4 := by omega
            exact False.elim (no_even_high a k x y n hae hx hy hs (haa ▸ hpow) (haa ▸ hcost))
          · simp only [sectionPreimageCriterion,ha0,ha1,hk0,hlow,hae,ite_true,ite_false] at h
            rcases h with ⟨n,hpow,_⟩
            have ht : x+y+1=2*(2^n*(a+3)) := by
              have hform : 2*(a-1)+8=2*(a+3) := by omega
              rw [hform] at hpow
              calc x+y+1=2^n*(2*(a+3)) := hpow
                   _ = 2*(2^n*(a+3)) := by ac_rfl
            omega

theorem even_even_criterion_iff_affine (a k x y : Nat)
    (hx : x%2=0) (hy : y%2=0) (h6 : 6≤y)
    (hs : (x+y)%8≠0) :
    sectionPreimageCriterion a k x y ↔
      a=x+y-2 ∧ k=(y-2)/2 := by
  constructor
  · exact even_even_criterion_forces_affine a k x y hx hy h6 hs
  · rintro ⟨rfl,rfl⟩
    have ha0 : x+y-2≠0 := by omega
    have ha1 : x+y-2≠1 := by omega
    have hk0 : (y-2)/2≠0 := by omega
    have hlow : 2*((y-2)/2)≤x+y-2 := by omega
    simp [sectionPreimageCriterion,ha0,ha1,hk0,hlow]
    omega

/-- Full native-source classification, with no cutoff or synthetic parent. -/
theorem section_even_even_iff_affine (a k x y : Nat)
    (hx : x%2=0) (hy : y%2=0) (h6 : 6≤y)
    (hs : (x+y)%8≠0) :
    secNext (a,k)=some (x,y) ↔
      a=x+y-2 ∧ k=(y-2)/2 := by
  rw [complete_section_inverse a k x y (by omega)]
  exact even_even_criterion_iff_affine a k x y hx hy h6 hs

#print axioms section_even_even_iff_affine
end BB6.Agent46
