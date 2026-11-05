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


/-- The original table's explicit state 6 is a frozen halt. -/
theorem terminal_step (c : Cfg) (hc : c.st = 6) : step c = c := by
  cases c with
  | mk l h r st =>
    change st = 6 at hc
    subst st
    cases h <;> rfl

theorem terminal_run (c : Cfg) (hc : c.st = 6) (n : Nat) :
    run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=n+1 by rfl, run_add n 1, ih]
    exact terminal_step c hc

/-- Any explicit F/1 predecessor excludes all preceding frozen halts. -/
theorem no_prior_halt {c : Cfg} {t : Nat}
    (h : (run t c).st = 5) (s : Nat) (hs : s ≤ t) :
    (run s c).st ≠ 6 := by
  intro h6
  have hr : run t c = run (t-s) (run s c) := by
    calc
      run t c = run (s+(t-s)) c := by congr 1; omega
      _ = run (t-s) (run s c) := by rw [run_add]
  rw [hr, terminal_run _ h6 (t-s)] at h
  omega

/-- Source-authenticated *first halting time* for arbitrary finite mixed
    10/111 codewords. This does not separately exclude earlier F/0 returns. -/
theorem full_code_exact_first_halt (k : Nat) (ws ys : List Bool)
    (t : Nat) (ht : t < codeTime k ws) :
    (run t (codeInput k ws ys)).st ≠ 6 := by
  have htime : codeTime k ws = codePreTime k ws + 1 := by
    dsimp [codeTime, codePreTime]
    omega
  have hsmall : t ≤ codePreTime k ws := by omega
  exact no_prior_halt (full_code_before_halt k ws ys).1 t hsmall

#print axioms terminal_step
#print axioms terminal_run
#print axioms no_prior_halt
#print axioms full_code_exact_first_halt
#print axioms full_code_halts
#print axioms full_code_before_halt
#print axioms codeTime_shift

end BB6.Agent37CodeHalt
