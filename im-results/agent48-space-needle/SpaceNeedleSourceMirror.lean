import Lean
import Lean.Elab.Tactic.Omega

/- Exact high-level definitions copied from DeepMind Cryptids pinned
   ced8f9f44f67a167d5ecc03e687b048c67926371 lines 470-501.
   Independent of Mathlib for local kernel proof; original import still pending. -/
namespace BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

inductive HighLevelState where
  | N (d : Nat)
  deriving DecidableEq, Repr

def highLevelStart : HighLevelState := .N 1

def scanEven (d b : Nat) : Option HighLevelState :=
  if d % 2 = 0 then
    if d = 0 then none
    else scanEven (d / 2 - 1) (b + d / 2 + 2)
  else if d = 1 then
    some (.N (b + 4))
  else
    some (.N (b + 5 * (d / 2 - 1) + 9))
termination_by d
decreasing_by omega

def highLevelNext : HighLevelState → Option HighLevelState
  | .N d => scanEven d 0

end BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

def oddTower (q : Nat) : Nat → Nat
  | 0 => 2*q+1
  | k+1 => 2*(oddTower q k+1)

theorem scan_oddTower (q k b : Nat) :
    scanEven (oddTower q k) b =
      some (.N (b+oddTower q k+k+3*(q+1))) := by
  induction k generalizing b with
  | zero =>
      cases q with
      | zero => simp [oddTower,scanEven]
      | succ q => simp [oddTower,scanEven]; omega
  | succ k ih =>
      have he : 2*(oddTower q k+1) ≠ 0 := by omega
      have hx : (2*(oddTower q k+1))/2-1 = oddTower q k := by omega
      change scanEven (2*(oddTower q k+1)) b =
        some (.N (b+(2*(oddTower q k+1))+(k+1)+3*(q+1)))
      rw [scanEven]
      simp only [Nat.mul_mod_right, ite_true, if_neg he]
      rw [hx,ih]
      have hd : 2*(oddTower q k+1)/2 = oddTower q k+1 := by omega
      rw [hd]
      simp only [Option.some.injEq, HighLevelState.N.injEq]
      omega

theorem oddTower_factor (q k : Nat) :
    oddTower q k+2 = 2^k*(2*q+3) := by
  induction k with
  | zero => simp [oddTower]
  | succ k ih =>
      change 2*(oddTower q k+1)+2=2^(k+1)*(2*q+3)
      rw [Nat.pow_succ']
      rw [Nat.mul_assoc]
      omega

theorem original_step_on_oddTower (q v : Nat) :
    highLevelNext (.N (oddTower q v)) =
      some (.N (oddTower q v+v+3*(q+1))) := by
  change scanEven (oddTower q v) 0 = _
  simpa using scan_oddTower q v 0

end BB6.Agent48.SpaceNeedle
#print axioms BB6.Agent48.SpaceNeedle.scan_oddTower
#print axioms BB6.Agent48.SpaceNeedle.oddTower_factor
#print axioms BB6.Agent48.SpaceNeedle.original_step_on_oddTower
