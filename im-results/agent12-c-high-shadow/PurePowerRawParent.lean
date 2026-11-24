import PurePowerPhases
import FullSectionInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12PureFan
open BB6.Agent46

/-- Rewrite the already exact source criterion into a disjoint arithmetic
    fan suitable for pure-power targets. The guard removes the exceptional
    small outputs but retains every special zero/one source. -/
theorem raw_parent_iff (a k x y : Nat) (hy : 8≤y) :
    RawParent a k x y ↔ sectionPreimageCriterion a k x y := by
  constructor
  · intro h
    rcases h with h|h|h|h|h
    · obtain ⟨hpar,ha,hk⟩ := h
      have hreg : 2*k≤a := by omega
      simp [sectionPreimageCriterion,show a≠0 by omega,show a≠1 by omega,
        show k≠0 by omega,hreg]
      omega
    · obtain ⟨rfl,hk,n,hs,hw⟩ := h
      simp [sectionPreimageCriterion,show k≠0 by omega,show k≠1 by omega]
      exact ⟨n,hs,by omega⟩
    · obtain ⟨rfl,hk,n,hs,hw⟩ := h
      simp [sectionPreimageCriterion,show k≠0 by omega,show k≠1 by omega,
        show k≠2 by omega,show k≠3 by omega]
      exact ⟨n,hs,by omega⟩
    · obtain ⟨ha,hak,hpar,n,hs,hw⟩ := h
      simp [sectionPreimageCriterion,show a≠0 by omega,show a≠1 by omega,
        show k≠0 by omega,show ¬2*k≤a by omega,hpar]
      have hs' : 2^(n+1)*(a+2)=2^n*(2*(a-1)+6) := by
        rw [Nat.pow_succ,Nat.mul_assoc]
        congr 1
        omega
      exact ⟨n,hs.trans hs',by omega⟩
    · obtain ⟨ha,hak,hpar,n,hs,hw⟩ := h
      simp [sectionPreimageCriterion,show a≠0 by omega,show a≠1 by omega,
        show k≠0 by omega,show ¬2*k≤a by omega,show a%2≠0 by omega]
      have hs' : 2^(n+1)*(a+3)=2^n*(2*(a-1)+8) := by
        rw [Nat.pow_succ,Nat.mul_assoc]
        congr 1
        omega
      exact ⟨n,hs.trans hs',by omega⟩
  · intro h
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,hk0] at h
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,ha0,hk0,hk1] at h
          omega
        · simp [sectionPreimageCriterion,ha0,hk0,hk1] at h
          obtain ⟨n,hs,hw⟩ := h
          exact Or.inr (Or.inl ⟨ha0,by omega,n,hs,by omega⟩)
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
              · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at h
                obtain ⟨n,hs,hw⟩ := h
                exact Or.inr (Or.inr (Or.inl ⟨ha1,by omega,n,hs,by omega⟩))
      · by_cases hk0 : k=0
        · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
        · by_cases hreg : 2*k≤a
          · simp [sectionPreimageCriterion,ha0,ha1,hk0,hreg] at h
            exact Or.inl ⟨by omega,by omega,by omega⟩
          · by_cases hpar : a%2=0
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hreg,hpar] at h
              obtain ⟨n,hs,hw⟩ := h
              have hs' : 2^n*(2*(a-1)+6)=2^(n+1)*(a+2) := by
                rw [Nat.pow_succ,Nat.mul_assoc]
                congr 1
                omega
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,hpar,n,hs.trans hs',by omega⟩)))
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hreg,hpar] at h
              obtain ⟨n,hs,hw⟩ := h
              have hs' : 2^n*(2*(a-1)+8)=2^(n+1)*(a+3) := by
                rw [Nat.pow_succ,Nat.mul_assoc]
                congr 1
                omega
              exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,by omega,by omega,n,hs.trans hs',by omega⟩)))

end BB6.Agent12PureFan
