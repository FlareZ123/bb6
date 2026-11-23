import EvenOddSmallValuation
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13AllFan
open BB6.Agent46

/-- The full source inverse of any even-left / odd-right target of
    sufficiently large mass is an ordinary odd bounce whenever the
    mass-plus-one is not a pure power of two. This retains EVERY unbounded
    even bounce depth; it does not assume a finite valuation cutoff. -/
theorem even_odd_nonpower_parent
    (a k x y : Nat)
    (hx : x%2=0) (hyodd : y%2=1) (hy : 5≤y)
    (hbig : 64≤x+y+1)
    (hnonpower : ∀ t : Nat, x+y+1 ≠ 2^t)
    (hedge : secNext (a,k)=some (x,y)) :
    ∃ n : Nat, n%2=0 ∧ 3≤a ∧ a<2*k ∧
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
              have heq : x+y+1=2^(n+4) := by
                simpa only [Nat.pow_add, show (2:Nat)^4=16 by decide]
                  using hpow
              exact False.elim (hnonpower (n+4) heq)
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
            exact ⟨n,hnEven,by omega,by omega,hpow,hcost⟩

#print axioms even_odd_nonpower_parent
end BB6.Agent13AllFan
