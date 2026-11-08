import PositiveSafe
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429ZeroRegularSafe
open BB429OddExcursion BB429SourceE1Return
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4CZeroSafe

private theorem pairs01_succ_append (n : Nat) :
    pairs01 n ++ [false,true] = pairs01 (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change false :: true :: (pairs01 n ++ [false,true]) =
        false :: true :: pairs01 (n+1)
      rw [ih]

/-- One B/0,C/1 pair executes no C/0 instruction. -/
theorem b01_pair_safe (left suffix : List Bool) :
    runSafe 2 (z 1 left false (true :: true :: suffix)) =
      some (z 1 (false :: true :: left) true suffix) := by rfl

/-- Arbitrarily long B/0,C/1 scan traverses no C/0. -/
theorem b01_shift_safe (v : Nat) (left suffix : List Bool) :
    runSafe (2*(v+1))
      (z 1 left false (true :: (pairs01 v ++ (true :: suffix)))) =
      some (z 1 (pairs01 (v+1) ++ left) true suffix) := by
  induction v generalizing left suffix with
  | zero =>
      simpa [pairs01] using (b01_pair_safe left suffix)
  | succ v ih =>
      have hpair :
          runSafe 2
            (z 1 left false (true :: (pairs01 (v+1) ++ (true :: suffix)))) =
            some (z 1 (false :: true :: left) false
              (true :: (pairs01 v ++ (true :: suffix)))) := by rfl
      rw [show 2*(v+2) = 2+2*(v+1) by omega,runSafe_add,hpair]
      simp only [Option.bind_some]
      rw [ih (false :: true :: left) suffix]
      have hleft : pairs01 (v+1) ++ (false :: true :: left) =
          pairs01 (v+2) ++ left := by
        calc
          pairs01 (v+1) ++ (false :: true :: left) =
            (pairs01 (v+1) ++ [false,true]) ++ left := by
              simp [List.append_assoc]
          _ = pairs01 (v+2) ++ left := by rw [pairs01_succ_append]
      rw [hleft]

/-- First twenty primitive instructions of zero-u Junc avoid C/0. -/
theorem junc0_prep20_safe (v w : Nat) :
    runSafe 20 (junc 0 v w) =
      some (z 1 (ones 5) false
        (true :: (pairs01 (v+2) ++ ones w ++ [false,true]))) := by rfl

/-- Zero-u Junc's full B/0,C/1 sweep is C/0-free whenever w>=1. -/
theorem junc0_to_B_safe (v w : Nat) (hw : 1 ≤ w) :
    runSafe (2*v+26) (junc 0 v w) =
      some (z 1 (pairs01 (v+3) ++ ones 5) true
        (ones (w-1) ++ [false,true])) := by
  have hones : ones w = true :: ones (w-1) := by
    cases w with
    | zero => omega
    | succ w => rfl
  rw [show 2*v+26 = 20 + 2*(v+3) by omega,runSafe_add,junc0_prep20_safe]
  simp only [Option.bind_some]
  have hshift := b01_shift_safe (v+2) (ones 5) (ones (w-1) ++ [false,true])
  have hinput :
      z 1 (ones 5) false (true :: (pairs01 (v+2) ++ ones w ++ [false,true])) =
      z 1 (ones 5) false
        (true :: (pairs01 (v+2) ++ (true :: (ones (w-1) ++ [false,true])))) := by
    simp [hones, List.append_assoc]
  rw [← hinput] at hshift
  exact hshift

/-- An entire zero-u regular Junc return, for every w>=3,
    executes no C/0 instruction at any primitive step. -/
theorem junc0_regular_safe (v w : Nat) (hw : 3 ≤ w) :
    runSafe (2*v+27) (junc 0 v w) =
      some (junc (v+3) 0 (w-3)) := by
  have hB := junc0_to_B_safe v w (by omega)
  rw [show 2*v+27 = (2*v+26)+1 by omega,runSafe_add,hB]
  simp only [Option.bind_some]
  have hones : ones (w-1) = true :: true :: ones (w-3) := by
    cases w with
    | zero => omega
    | succ w => cases w with
      | zero => omega
      | succ w => cases w with
        | zero => omega
        | succ w => rfl
  rw [hones]
  rfl

/-- Every executed prefix of the regular zero-u branch has a defined
    source run and avoids the state-C/current-zero halting gateway. -/
theorem junc0_regular_no_czero (v w t : Nat) (hw : 3 ≤ w)
    (ht : t < 2*v+27) :
    ∃ p, run t (junc 0 v w) = some p ∧
      (p.state == 2 && !p.current) = false := by
  exact runSafe_no_czero_prefix (2*v+27) t
    (junc 0 v w) (junc (v+3) 0 (w-3))
    (junc0_regular_safe v w hw) ht

#print axioms junc0_prep20_safe
#print axioms junc0_to_B_safe
#print axioms junc0_regular_safe
#print axioms junc0_regular_no_czero

end BB429ZeroRegularSafe
