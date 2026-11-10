import NeedleGrowth
import SpaceNeedleClosed
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleGrowth
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- Exact translation from the original pinned Space Needle high-level
    successor to a shifted-counter arithmetic edge. -/
theorem original_edge (d e : Nat)
    (h : highLevelNext (.N d) = some (.N e)) :
    NeedleGrowth.Edge (d+2) (e+2) := by
  rcases (highLevelNext_iff_oddTower d e).mp h with ⟨q,v,hd,he⟩
  refine ⟨q,v,?_,?_⟩
  · rw [hd]
    exact oddTower_factor q v
  · rw [he]
    omega

/-- Every successful genuine-source high-level step grows by at least
    the binary logarithm of its shifted input plus two. -/
theorem original_log_growth (d e : Nat)
    (h : highLevelNext (.N d) = some (.N e)) :
    d + Nat.log2 (d+2) + 2 ≤ e := by
  have hh := NeedleGrowth.edge_log_growth (original_edge d e h)
  omega

/-- Every unbounded successful source orbit has superlinear growth. This
    does not assert that the authentic blank-root orbit is infinite. -/
theorem original_orbit_superlinear (f : Nat → Nat)
    (h : ∀ n, highLevelNext (.N (f n)) = some (.N (f (n+1))))
    (M n : Nat) (hn : 2^(M+1) ≤ n) :
    (n/2)*(M+2) ≤ f n+2 := by
  have hi : NeedleGrowth.Orbit (fun i => f i+2) := by
    intro i
    exact original_edge (f i) (f (i+1)) (h i)
  exact NeedleGrowth.orbit_superlinear (fun i => f i+2) hi M n hn

#print axioms BB6.Agent20.SpaceNeedleGrowth.original_edge
#print axioms BB6.Agent20.SpaceNeedleGrowth.original_log_growth
#print axioms BB6.Agent20.SpaceNeedleGrowth.original_orbit_superlinear
end BB6.Agent20.SpaceNeedleGrowth
