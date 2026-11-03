import Lean.Elab.Tactic.Omega
import A1100First
import A110111

set_option maxHeartbeats 8000000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false

namespace CryptidBoundary

theorem a110111_prefix_nonPhysical (m : Nat) (ys : List Bool) (t : Nat)
    (ht : t < 27) :
    ¬ Physical (run t
      (aBoundary (m+3) (true::true::false::true::true::true::ys))) := by
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨
      t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 ∨
      t=12 ∨ t=13 ∨ t=14 ∨ t=15 ∨ t=16 ∨ t=17 ∨
      t=18 ∨ t=19 ∨ t=20 ∨ t=21 ∨ t=22 ∨ t=23 ∨
      t=24 ∨ t=25 ∨ t=26 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  all_goals simp [Physical, aBoundary, run, step, goR, goL, pairs]

theorem a110111_first_physical (m : Nat) (ys : List Bool) (t : Nat)
    (ht : t < 2*(m+3)+24) :
    ¬ Physical (run t (aBoundary (m+3)
      (true::true::false::true::true::true::ys))) := by
  by_cases hsmall : t < 27
  · exact a110111_prefix_nonPhysical m ys t hsmall
  · obtain ⟨u,hu⟩ : ∃ u, t=27+u := ⟨t-27,by omega⟩
    rw [hu,run_add,a110111_start]
    intro hc
    exact sweepD_noF m (List.replicate 8 true ++
       (false::true::false::true::false::ys)) u (by omega) hc.1

#print axioms a110111_prefix_nonPhysical
#print axioms a110111_first_physical
end CryptidBoundary
