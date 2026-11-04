import Lean.Elab.Tactic.Omega
import A1100First
import A1101010111

namespace CryptidBoundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 3000
set_option linter.unusedSimpArgs false

/-- The first 33 source steps cannot expose a physically blank-left F section.
    The proof checks a finite uniform prefix, with arbitrary remaining stack. -/
theorem a1101010111_prefix_nonPhysical (m : Nat) (ys : List Bool)
    (t : Nat) (ht : t < 33) :
    ¬ Physical (run t (aBoundary m
      (true::true::false::true::false::true::false::true::true::true::ys))) := by
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 ∨ t = 26 ∨ t = 27 ∨ t = 28 ∨ t = 29 ∨ t = 30 ∨ t = 31 ∨ t = 32 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Physical, aBoundary, run, step, goR, goL, pairs]

/-- Exact first positive physical F/0 return at the new terminal, for all m. -/
theorem a1101010111_first_physical (m : Nat) (ys : List Bool)
    (t : Nat) (ht : t < 2*m+36) :
    ¬ Physical (run t (aBoundary m
      (true::true::false::true::false::true::false::true::true::true::ys))) := by
  by_cases hsmall : t < 33
  · exact a1101010111_prefix_nonPhysical m ys t hsmall
  · obtain ⟨u,hu⟩ : ∃ u, t = 33+u := ⟨t-33,by omega⟩
    rw [hu, run_add, a1101010111_start]
    intro hc
    exact sweepD_noF m
      (true::true::false::true::false::true::false::true::false::true::false::ys)
      u (by omega) hc.1

#print axioms a1101010111_prefix_nonPhysical
#print axioms a1101010111_first_physical
end CryptidBoundary
