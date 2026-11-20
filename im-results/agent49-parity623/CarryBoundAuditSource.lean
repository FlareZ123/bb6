import Agent49ParitySource
import Lean.Elab.Tactic.Omega

/-!
# Source-checked counterexample to the narrowed #623 carry bound

This file imports the unmodified upstream #623 high-level definitions through
Agent49ParitySource. It proves the exact root transition and the integer
low-linear carry decomposition at that transition. The correction-only
quotient is in {-1,0,1}, but the total transducer carry is -2 because the
low R-x linear term already contributes a base quotient of -2.
-/

namespace BB6.Agent49CarryBoundAudit

open BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The exact source run reaches the disputed predecessor. -/
theorem root_run_38 :
    run 38 = some (.D 44634 124427) := by
  decide

/-- The exact source successor is the right-oriented state used in the audit. -/
theorem root_run_39 :
    run 39 = some (.D 79788 133932) := by
  rw [run, root_run_38]
  decide

def gap (a d : Nat) : Int :=
  (if a >= d then (a - d : Nat) else (d - a : Nat) : Nat) -
    3 * (min a d : Nat)

def gamma (a d : Nat) : Int :=
  if a >= d then
    if d % 2 = 1 then 18 else 10
  else
    if d % 2 = 1 then 2 else 4

/-- Agent 41's integer signed coordinate x=2g-gamma. -/
def signedX (a d : Nat) : Int := 2 * gap a d - gamma a d

/-- Agent 41's integer scale coordinate y=6 min(a,d). -/
def signedY (a d : Nat) : Int := 6 * (min a d : Nat)

theorem root38_signed_coordinates :
    signedX 44634 124427 = -108220 ∧
    signedY 44634 124427 = 267804 := by
  norm_num [signedX, signedY, gap, gamma]

theorem root39_signed_coordinates :
    signedX 79788 133932 = -370444 ∧
    signedY 79788 133932 = 478728 := by
  norm_num [signedX, signedY, gap, gamma]

/-- The exact R-branch affine correction C in x'=-4x-3y+C. -/
def correctionX : Int :=
  signedX 79788 133932 + 4 * signedX 44634 124427 +
    3 * signedY 44634 124427

/-- The exact R-branch affine correction F in y'=3x+3y+F. -/
def correctionY : Int :=
  signedY 79788 133932 - 3 * signedX 44634 124427 -
    3 * signedY 44634 124427

theorem exact_affine_corrections :
    correctionX = 88 ∧ correctionY = -24 := by
  norm_num [correctionX, correctionY, signedX, signedY, gap, gamma]

theorem low_residues :
    signedX 44634 124427 % 2187 = 1130 ∧
    signedX 44634 124427 % 729 = 401 ∧
    signedY 44634 124427 % 729 = 261 := by
  norm_num [signedX, signedY, gap, gamma]

/-- The uncorrected R-x contribution from input digits below k+1, k=6. -/
def lowLinearX : Int :=
  - (signedX 44634 124427 % 2187) -
    3 * (signedX 44634 124427 % 729) -
    3 * (signedY 44634 124427 % 729)

/-- The uncorrected R-y contribution from input digits below k+1, k=6. -/
def lowLinearY : Int :=
  3 * (signedX 44634 124427 % 729) +
    3 * (signedY 44634 124427 % 729)

theorem exact_low_linear_parts :
    lowLinearX = -3116 ∧ lowLinearY = 1986 := by
  norm_num [lowLinearX, lowLinearY, signedX, signedY, gap, gamma]

/-- The base quotient of the low R-x linear part is -2. -/
theorem base_linear_quotient :
    lowLinearX / 2187 = -2 := by
  norm_num [lowLinearX, signedX, signedY, gap, gamma]

/-- The extra quotient due to C alone is 0, satisfying the correction lemma. -/
theorem correction_only_quotient :
    (1258 + correctionX) / 2187 = 0 := by
  norm_num [correctionX, signedX, signedY, gap, gamma]

/-- The actual total R-x carry is base quotient plus correction quotient. -/
theorem total_Rx_carry :
    (lowLinearX + correctionX) / 2187 = -2 := by
  norm_num [lowLinearX, correctionX, signedX, signedY, gap, gamma]

/-- The actual total R-y carry is 0. -/
theorem total_Ry_carry :
    (lowLinearY + correctionY) / 2187 = 0 := by
  norm_num [lowLinearY, correctionY, signedX, signedY, gap, gamma]

/-- Exact decomposition: the correction quotient does not include the base carry. -/
theorem missing_base_carry_decomposition :
    (lowLinearX + correctionX) / 2187 =
      (-2 : Int) + (1258 + correctionX) / 2187 := by
  norm_num [lowLinearX, correctionX, signedX, signedY, gap, gamma]

#print axioms root_run_38
#print axioms root_run_39
#print axioms total_Rx_carry
#print axioms total_Ry_carry

end BB6.Agent49CarryBoundAudit
