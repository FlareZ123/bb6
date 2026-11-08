import CancellationTerminalConstructive
import CancellationMod5SourceEq
import NeedleTerminalAffineSource
import Lean.Elab.Tactic.Omega

/-! Pinned-original-source adapter for the constructive all-r cancellation
terminal feeders. The two arithmetic inverse obstructions remain in the
imported self-contained Lean modules. -/

namespace BB6.Agent20.CancellationOriginalBridge
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open CancellationGap CancellationConstructive
open CancellationTerminalConstructive

theorem feederK_positive (r : Nat) (hr : 1≤r) : 1≤feederK r := by
  have ha : 4≤valuationA r := by
    have hp := valuationA_linear r
    omega
  have hr2 : 2≤2*r := by omega
  have hmul : 2*valuationA r ≤ (2*r)*valuationA r :=
    Nat.mul_le_mul_right (valuationA r) hr2
  unfold feederK
  omega

/-- The constructed cancellation feeder is an authentic immediate
    predecessor of its terminal power in the original published accelerator.
    This does NOT say it is blank-reachable. -/
theorem original_all_r_terminal (r : Nat) (hr : 1≤r) :
    highLevelNext (.N (oddTower (feederQ r) (feederV r))) =
      some (.N (2^(feederK r)-2)) := by
  have hE : NeedleInverse.den (feederV r)*feederQ r+
      NeedleInverse.bias (feederV r)=2^(feederK r) := by
    change (2^(feederV r+1)+3)*feederQ r+
       3*2^(feederV r)+feederV r+3=2^(feederK r)
    exact (exact_terminal_feeder r hr).symm
  exact BB6.Agent20.SpaceNeedleTriple.authentic_affine_successor
    (feederQ r) (feederV r) (feederK r)
    (feederK_positive r hr) hE

#print axioms original_all_r_terminal
end BB6.Agent20.CancellationOriginalBridge
