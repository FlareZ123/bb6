import FullSectionInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13SmallFan
open BB6.Agent46

/-- The short valuation window forbids the large exception branch a=1
    of the complete original-section inverse grammar. -/
private theorem pow_sixteen_mod_sixtyfour (n : Nat) (hn : 2 ≤ n) :
    (2^n*16)%64=0 := by
  have hd : 4 ∣ 2^n := by
    have h : (2:Nat)^2 ∣ 2^n := Nat.pow_dvd_pow 2 hn
    simpa only [show (2:Nat)^2=4 by decide] using h
  rcases hd with ⟨u,hu⟩
  apply Nat.mod_eq_zero_of_dvd
  refine ⟨u,?_⟩
  rw [hu]
  omega

/-- In the genuine complete source inverse relation, a large even-left,
    odd-right target with x+y+1 nonzero modulo 64 has only odd-source
    bounce parents of depth 0 or 2. No depth or search cutoff is assumed.
    This is a source-grammar classification; it does not assert that any
    such parent or target is reached by the blank orbit. -/
theorem even_odd_small_valuation_parent
    (a k x y : Nat)
    (hx : x%2=0) (hyodd : y%2=1) (hy : 5≤y)
    (hbig : 64≤x+y+1)
    (hn64 : (x+y+1)%64≠0)
    (hedge : secNext (a,k)=some (x,y)) :
    ∃ n : Nat, (n=0 ∨ n=2) ∧
      x+y+1=2^n*(2*(a-1)+8) ∧
      (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2 := by
  have hp := (complete_section_inverse a k x y hy).mp hedge
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageCriterion,ha0,hk0,hk1] at hp
        omega
      · simp only [sectionPreimageCriterion,if_pos ha0,
            if_neg hk0,if_neg hk1] at hp
        rcases hp with ⟨n,hpow,_⟩
        have heven : (x+y)%2=0 := by
          rw [hpow]
          simp [Nat.mul_mod]
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hp
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1] at hp
        · by_cases hk2 : k=2
          · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2] at hp
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at hp
              omega
            · simp only [sectionPreimageCriterion,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
              rcases hp with ⟨n,hpow,_⟩
              cases n with
              | zero =>
                simp at hpow
                omega
              | succ n =>
                cases n with
                | zero =>
                  simp at hpow
                  omega
                | succ n =>
                  have hmod : (x+y+1)%64=0 := by
                    rw [hpow]
                    exact pow_sixteen_mod_sixtyfour _ (by omega)
                  exact (hn64 hmod).elim
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hp
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
              if_neg hk0,if_pos hlow] at hp
          rcases hp with ⟨_,hyeven⟩
          omega
        · by_cases hae : a%2=0
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
                if_neg hk0,if_neg hlow,if_pos hae] at hp
            rcases hp with ⟨n,hpow,_⟩
            have heven : (x+y)%2=0 := by
              rw [hpow]
              simp [Nat.mul_mod]
            omega
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,
                if_neg hk0,if_neg hlow,if_neg hae] at hp
            rcases hp with ⟨n,hpow,hcost⟩
            have haodd : a%2=1 := by omega
            have hnEven : n%2=0 := by omega
            have hfac : 4 ∣ 2*(a-1)+8 := by
              have heven : (a-1)%2=0 := by omega
              obtain ⟨u,hu⟩ : ∃ u, a-1=2*u :=
                ⟨(a-1)/2,by omega⟩
              refine ⟨u+2,?_⟩
              rw [hu]
              omega
            have hnlt : n<4 := by
              by_cases hn4 : 4≤n
              · have hpow16 : 16 ∣ 2^n := by
                  have h : (2:Nat)^4 ∣ 2^n :=
                    Nat.pow_dvd_pow 2 hn4
                  simpa only [show (2:Nat)^4=16 by decide] using h
                rcases hpow16 with ⟨u,hu⟩
                rcases hfac with ⟨v,hv⟩
                have h64 : 64 ∣ x+y+1 := by
                  refine ⟨u*v,?_⟩
                  calc
                    x+y+1 = 2^n*(2*(a-1)+8) := hpow
                    _ = (16*u)*(4*v) := by rw [hu,hv]
                    _ = (16*4)*(u*v) := by ac_rfl
                    _ = 64*(u*v) := by decide
                exact hn64 (Nat.mod_eq_zero_of_dvd h64)
              · omega
            exact ⟨n,by omega,hpow,hcost⟩

#print axioms even_odd_small_valuation_parent
end BB6.Agent13SmallFan
