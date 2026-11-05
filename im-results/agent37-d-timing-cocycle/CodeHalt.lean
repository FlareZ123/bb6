import Lean.Elab.Tactic.Omega
import ABridgeCode
import AHaltCylinder
import ReturnShift

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

namespace BB6.Agent37CodeHalt

open CryptidBoundary BB6.Agent35

/-- Original physical F/0 entry, with a general mixed A token word
    (10 or 111), followed by the earlier source-proved A halt cylinder. -/
def codeInput (k : Nat) (ws ys : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false :: (CryptidA.wordCode ws ++ (BB6.CryptidAHalt.haltWord ++ ys)))

/-- State-6 entry time in the original complete raw machine. -/
def codeTime (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32) + (CryptidA.wordCost (4*k+3) ws + 69)

def codePreTime (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32) + (CryptidA.wordCost (4*k+3) ws + 68)

/-- Every mixed token prefix admits the same independently certified terminal
    word. Arbitrary k, arbitrary token ordering and arbitrary suffix. -/
theorem full_code_halts (k : Nat) (ws ys : List Bool) :
    (run (codeTime k ws) (codeInput k ws ys)).st = 6 := by
  dsimp [codeTime, codeInput]
  rw [run_add, prefix_A]
  change (run (CryptidA.wordCost (4*k+3) ws + 69)
    (aBoundary (4*k+3)
      (CryptidA.wordCode ws ++ (BB6.CryptidAHalt.haltWord ++ ys)))).st = 6
  rw [run_add, a_code_return]
  simpa only [aBoundary] using
    BB6.CryptidAHalt.a_halt_69
      (false :: pairs (4*k+3+CryptidA.wordInc ws) ++ [true,true]) ys

/-- Exactly one transition before the terminal entry, the raw machine is
    physically in state F scanning 1 (the source's undefined transition). -/
theorem full_code_before_halt (k : Nat) (ws ys : List Bool) :
    (run (codePreTime k ws) (codeInput k ws ys)).st = 5 ∧
    (run (codePreTime k ws) (codeInput k ws ys)).h = true := by
  dsimp [codePreTime, codeInput]
  rw [run_add, prefix_A]
  change
    (run (CryptidA.wordCost (4*k+3) ws + 68)
      (aBoundary (4*k+3)
        (CryptidA.wordCode ws ++ (BB6.CryptidAHalt.haltWord ++ ys)))).st = 5 ∧
    (run (CryptidA.wordCost (4*k+3) ws + 68)
      (aBoundary (4*k+3)
        (CryptidA.wordCode ws ++ (BB6.CryptidAHalt.haltWord ++ ys)))).h = true
  rw [run_add, a_code_return]
  simpa only [aBoundary] using
    BB6.CryptidAHalt.a_before_halt
      (false :: pairs (4*k+3+CryptidA.wordInc ws) ++ [true,true]) ys

/-- Formula for the exact source-certified halt clock's quadratic shift.
    Each 111 token contributes 24 extra primitive steps per lifted k;
    10 tokens have no contribution to the derivative. -/
theorem codeTime_shift (k h : Nat) (ws : List Bool) :
    codeTime (k+h) ws =
      codeTime k ws +
        h*(24*k+12*h+41+24*BB6.CryptidBridge.tripleTokens ws) := by
  dsimp [codeTime]
  have hh := BB6.CryptidBridge.wordCost_shift4h (4*k+3) h ws
  have hm : 4*(k+h)+3 = (4*k+3)+4*h := by omega
  rw [hm, hh]
  have hquad : 12*(k+h)*(k+h) =
      12*k*k + 24*k*h + 12*h*h := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    have comm : h*k = k*h := Nat.mul_comm h k
    omega
  rw [hquad]
  have ha : 24*h*BB6.CryptidBridge.tripleTokens ws =
      h*(24*BB6.CryptidBridge.tripleTokens ws) := by ac_rfl
  have hb : 24*k*h = h*(24*k) := by ac_rfl
  have hc : 12*h*h = h*(12*h) := by ac_rfl
  rw [ha, hb, hc]
  simp only [Nat.mul_add]
  omega

#print axioms full_code_halts
#print axioms full_code_before_halt
#print axioms codeTime_shift

end BB6.Agent37CodeHalt
