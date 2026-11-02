import FastSectionDef
import BounceHalting
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Exact complete arithmetic stopping criterion for every two-counter
    Machine C zero-high section, including all bounce depths. -/
theorem section_halts_iff_seed (a k : Nat) :
    secNext (a,k) = none ↔
      (a=0 ∧ k=0) ∨
      (a=1 ∧ 4≤k ∧ ∃ n, 2*k-3=haltSeed 4 n) ∨
      (2≤a ∧ 1≤k ∧ a<2*k ∧ a%2=1 ∧
       ∃ n, 2*k-a+3=haltSeed (a-1) n) := by
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · subst k
      simp [secNext, exactSection]
    · by_cases hk1 : k=1
      · subst k
        simp [secNext, exactSection]
      · have hc : 4≤2*k+1 := by omega
        have hodd := odd_bounce_nonhalt (2*k+1) 1 hc (by decide)
        simp [secNext,exactSection,hk0,hk1]
        intro hh
        exact hodd hh
  · by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · subst k
        simp [secNext, exactSection]
      · by_cases hk1 : k=1
        · subst k
          simp [secNext, exactSection]
        · by_cases hk2 : k=2
          · subst k
            simp [secNext, exactSection]
          · by_cases hk3 : k=3
            · subst k
              simp [secNext, exactSection]
            · have hc : 4≤2*k-3 := by omega
              have hh := bounce_halts_iff_seed 4 (2*k-3) hc
              have hsec : secNext (1,k) = (bounce 4 (2*k-3)).2 := by
                simp [secNext, exactSection, hk0,hk1,hk2,hk3]
              rw [hsec]
              simpa [show 4≤k by omega] using hh
    · by_cases hk0 : k=0
      · subst k
        simp [secNext, exactSection, ha0,ha1]
      · by_cases hreg : 2*k≤a
        · simp [secNext, exactSection, ha0,ha1,hk0,hreg]
          omega
        · have hc : 4≤2*k-a+3 := by omega
          have hh := bounce_halts_iff_seed (a-1) (2*k-a+3) hc
          have hp : (a-1)%2=0 ↔ a%2=1 := by omega
          have hA : 2≤a := by omega
          have hK : 1≤k := by omega
          have hR : a<2*k := by omega
          have hsec : secNext (a,k) = (bounce (a-1) (2*k-a+3)).2 := by
            simp [secNext,exactSection,ha0,ha1,hk0,hreg]
          rw [hsec,hh]
          simp [ha0,ha1,hA,hK,hR,hp]

#print axioms section_halts_iff_seed
end BB6.Agent15
