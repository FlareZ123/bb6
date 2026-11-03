import Lean.Elab.Tactic.Omega
import A1100

set_option maxHeartbeats 8000000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false

namespace CryptidBoundary

/-- Physical F/0 return permits harmless zero padding on the finite left list. -/
def Physical (c : Cfg) : Prop :=
  c.st = 5 ∧ ∀ b, b ∈ c.l → b = false

theorem a1100_prefix_nonPhysical (m : Nat) (ys : List Bool) (t : Nat)
    (ht : t < 17) :
    ¬ Physical (run t
      (aBoundary (m+2) (true::true::false::false::ys))) := by
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨
      t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 ∨
      t=12 ∨ t=13 ∨ t=14 ∨ t=15 ∨ t=16 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  all_goals simp [Physical, aBoundary, run, step, goR, goL, pairs]

theorem sweepD_noF (m : Nat) (ys : List Bool) (t : Nat)
    (ht : t < 2*m+3) : (run t (sweepD m ys)).st ≠ 5 := by
  induction m generalizing ys t with
  | zero =>
    have hc : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hc with rfl | rfl | rfl
    all_goals simp [sweepD,run,step,goL,goR,pairs]
  | succ m ih =>
    by_cases hsmall : t < 2
    · have hc : t=0 ∨ t=1 := by omega
      rcases hc with rfl | rfl
      all_goals simp [sweepD,run,step,goL,goR,pairs]
    · obtain ⟨u,hu⟩ : ∃ u, t=2+u := ⟨t-2,by omega⟩
      rw [hu,run_add,sweepD_step]
      exact ih (true::true::ys) u (by omega)

theorem a1100_first_physical (m : Nat) (ys : List Bool) (t : Nat)
    (ht : t < 2*(m+2)+16) :
    ¬ Physical (run t (aBoundary (m+2) (true::true::false::false::ys))) := by
  by_cases hsmall : t < 17
  · exact a1100_prefix_nonPhysical m ys t hsmall
  · obtain ⟨u,hu⟩ : ∃ u, t=17+u := ⟨t-17,by omega⟩
    rw [hu,run_add,a1100_start]
    intro hc
    exact sweepD_noF m (true::true::false::(List.replicate 6 true ++ ys))
       u (by omega) hc.1

#print axioms a1100_prefix_nonPhysical
#print axioms sweepD_noF
#print axioms a1100_first_physical
end CryptidBoundary
