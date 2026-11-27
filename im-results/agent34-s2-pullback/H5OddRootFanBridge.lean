import H5ExactSpine
import QEvenH5OddAgent25Bridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34H5OddRootBridge
open BB6.Agent34H5Precision
open BB6.Agent34H5Exact
open BB6.Agent34H5OddBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The exact source high-stop target forces an encounter with Agent21's
    affinely parametrized odd/even E-state after the ten certified inverse
    steps, uniformly in all H5 odd parameters (not just a residue slice). -/
theorem h5_odd_root_forces_E (r w : Nat)
    (hr : BB6.Agent3.CReach (2*h5OddJ r+3) (h5OddK r w)) :
    BB6.Agent3.CReach (h5OddEax r w) (h5OddEay r w) := by
  have hj : J r=h5OddJ r+1 := by
    dsimp [J,h5OddJ]
    omega
  have hm : M r w=h5OddM r w := rfl
  have hk : h5OddK r w=49726+8388608*h5OddB r w := by
    rfl
  have hx : 2*J r+1=2*h5OddJ r+3 := by omega
  have hstop :
      (49726+8388608*h5OddB r w)+J r+3*M r w+4 =
      2^(2*M r w+2)*(J r+2) := by
    calc
      (49726+8388608*h5OddB r w)+J r+3*M r w+4
          = h5OddK r w+h5OddJ r+3*h5OddM r w+5 := by
            rw [hk,hj,hm]
            omega
      _ = 2^(2*h5OddM r w+2)*(h5OddJ r+3) :=
        h5OddK_gate r w
      _ = 2^(2*M r w+2)*(J r+2) := by
        rw [hm,hj]
        congr 1
        omega
  have hroot : BB6.Agent3.CReach (2*J r+1)
      (49726+8388608*h5OddB r w) := by
    rw [hx, ←hk]
    exact hr
  have hE := h5_stop_forces_E r w (h5OddB r w) hstop hroot
  simpa [h5OddEax,h5OddEay] using hE

/-- Exact original-source necessary alternatives for every full H5 odd
    high-stop root: either the direct E-parent, or a constrained odd-depth
    high E-parent. This stitches the source spine to the non-power lemma. -/
theorem h5_odd_root_parent_fan (r w : Nat)
    (hr : BB6.Agent3.CReach (2*h5OddJ r+3) (h5OddK r w)) :
      (∃ t, BB6.Agent8Section.run secNext t (some (5,1)) =
        some (h5OddEax r w + h5OddEay r w - 2,
             (h5OddEay r w - 2)/2)) ∨
      (∃ n a k t, n%2=1 ∧ a%2=1 ∧ 3≤a ∧ a<2*k ∧
        h5OddEax r w + h5OddEay r w + 1 = 2^(n+1)*(a+3) ∧
        2*k+a+7+3*n = h5OddEax r w + 2*h5OddEay r w ∧
        BB6.Agent8Section.run secNext t (some (5,1)) = some (a,k)) := by
  exact (h5Odd_parent_fan r w).mp (h5_odd_root_forces_E r w hr)

#print axioms h5_odd_root_forces_E
#print axioms h5_odd_root_parent_fan
end BB6.Agent34H5OddRootBridge
