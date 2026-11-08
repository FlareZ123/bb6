import ZeroRegularSafe
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429ZeroTwoGate
open BB429OddExcursion BB429SourceE1Return
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4CZeroSafe BB429ZeroRegularSafe

/-- Nine guarded primitive steps from the w=2 B/1 boundary reach C/0
    with the entire right half-tape blank, for any untouched left tail. -/
theorem b1_w2_to_czero9 (tail : List Bool) :
    runSafe 9 (z 1 (false :: true :: tail) true [true,false,true]) =
      some (z 2 (([true,false] ++ ones 5) ++ tail) false []) := by rfl

/-- For every v, the first C/0 encounter of junc 0 v 2
    occurs at exactly 2v+35 original source steps. Its whole right
    tape is blank, and the guarded interpreter certifies that no
    earlier processed step was C/0. -/
theorem junc0_w2_first_czero (v : Nat) :
    runSafe (2*v+35) (junc 0 v 2) =
      some (z 2 (([true,false] ++ ones 5) ++ (pairs01 (v+2) ++ ones 5))
        false []) := by
  have hb := junc0_to_B_safe v 2 (by omega)
  rw [show 2*v+35 = (2*v+26)+9 by omega,runSafe_add,hb]
  simp only [Option.bind_some]
  have hi : pairs01 (v+3) ++ ones 5 =
      false :: true :: (pairs01 (v+2) ++ ones 5) := by rfl
  rw [hi]
  exact b1_w2_to_czero9 (pairs01 (v+2) ++ ones 5)

/-- Original, unguarded source prefix exists at every step through the
    first w=2 C/0, with earlier C/0 visits impossible. -/
theorem junc0_w2_no_earlier_czero (v t : Nat) (ht : t < 2*v+35) :
    ∃ p, run t (junc 0 v 2) = some p ∧
      (p.state == 2 && !p.current) = false := by
  exact runSafe_no_czero_prefix (2*v+35) t
    (junc 0 v 2)
    (z 2 (([true,false] ++ ones 5) ++ (pairs01 (v+2) ++ ones 5))
      false []) (junc0_w2_first_czero v) ht

/-- The first w=2 gate is harmless because the right neighbor is blank;
    the same certificate proves the source run reaches this exact gate. -/
theorem junc0_w2_first_czero_blank_right (v : Nat) :
    run (2*v+35) (junc 0 v 2) =
      some (z 2 (([true,false] ++ ones 5) ++ (pairs01 (v+2) ++ ones 5))
        false []) := by
  exact runSafe_to_run (2*v+35) (junc 0 v 2)
    (z 2 (([true,false] ++ ones 5) ++ (pairs01 (v+2) ++ ones 5))
      false []) (junc0_w2_first_czero v)

#print axioms b1_w2_to_czero9
#print axioms junc0_w2_first_czero
#print axioms junc0_w2_no_earlier_czero
#print axioms junc0_w2_first_czero_blank_right

end BB429ZeroTwoGate
