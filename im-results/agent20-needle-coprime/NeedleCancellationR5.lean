import NeedleRootDecisionSource
import Lean.Elab.Tactic.Decide
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent20.SpaceNeedleR5

open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open NeedleInverse

/-- The fifth member of the exact cancellation terminal-feeder family. -/
def cancellationK5 : Nat := 295269
def cancellationV5 : Nat := 29526
def cancellationQ5 : Nat := candidateQ cancellationV5 cancellationK5
def cancellationFeeder5 : Nat := oddTower cancellationQ5 cancellationV5

/-- Exact terminal-feeder equation at r=5. -/
theorem cancellation_r5_equation :
    equation cancellationQ5 cancellationV5 cancellationK5 := by
  native_decide

/-- The complete generic inverse of the r=5 target is empty.  This checks
    every possible valuation 0 through log2(feeder+2), not a cutoff search. -/
theorem cancellation_r5_incoming_parents :
    NeedleGeneralInverse.parents (cancellationFeeder5+2) = [] := by
  native_decide

theorem cancellation_r5_feeder_gt_one : 1 < cancellationFeeder5 := by
  have hpow : 2 ≤ (2:Nat)^cancellationV5 := by
    change 2 ≤ (2:Nat)^29526
    rw [show (29526:Nat)=29525+1 by omega, Nat.pow_succ]
    have hp : 0 < (2:Nat)^29525 := Nat.pow_pos (by decide)
    omega
  have hq : 3 ≤ 2*cancellationQ5+3 := by omega
  have hprod :
      6 ≤ (2:Nat)^cancellationV5*(2*cancellationQ5+3) :=
    Nat.mul_le_mul hpow hq
  have hf := oddTower_factor cancellationQ5 cancellationV5
  rw [←hf] at hprod
  omega

/-- The exact root checker returns false immediately because there is no
    original-source predecessor of this target. -/
theorem cancellation_r5_root_check_false :
    NeedleRootDecisionCore.reverseCheck
      BB6.Agent20.SpaceNeedleRootDecision.finiteParents
      (cancellationFeeder5+1) cancellationFeeder5 = false := by
  simp [NeedleRootDecisionCore.reverseCheck,
    BB6.Agent20.SpaceNeedleRootDecision.finiteParents,
    cancellation_r5_incoming_parents,
    cancellation_r5_feeder_gt_one]

/-- The r=5 cancellation feeder is not on the authentic blank-start orbit. -/
theorem cancellation_r5_not_reachable :
    ¬ ReachN cancellationFeeder5 := by
  intro hreach
  have htrue :=
    (BB6.Agent20.SpaceNeedleRootDecision.exact_root_target
      cancellationFeeder5).mpr hreach
  rw [cancellation_r5_root_check_false] at htrue
  contradiction

#print axioms cancellation_r5_equation
#print axioms cancellation_r5_incoming_parents
#print axioms cancellation_r5_not_reachable

end BB6.Agent20.SpaceNeedleR5
