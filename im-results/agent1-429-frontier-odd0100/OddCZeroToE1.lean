import CZeroEvenReturn
import Lean.Elab.Tactic.Omega

namespace BB429OddCZeroToE1
open BB429OddExcursion BB429CZeroEvenReturn

private theorem odd_c3 (m : Nat) (tail : List Bool) :
  run 3 (z 2 (true :: ones (2*m) ++ (false :: tail)) false []) =
    some (z 0 (ones (2*m) ++ (false :: tail)) true [false,true]) := by rfl

private theorem a3_to_e1 (tail r : List Bool) :
  run 3 (z 0 (false :: tail) true r) =
    some (z 4 tail true (true :: r)) := by rfl

/-- Uniform odd-prefix left parsing for a C/0 right frontier.
    The first zero after the 2m+1 ones suffices, and the deeper left tape
    survives without examination through the exact E/1 entry. -/
theorem odd_C0_to_E1 (m : Nat) (tail : List Bool) :
  run (2*m+6) (z 2 (ones (2*m+1) ++ (false :: tail)) false []) =
    some (z 4 tail true (true :: tens m ++ [false,true])) := by
  have hs : ones (2*m+1) ++ (false :: tail) =
      true :: ones (2*m) ++ (false :: tail) := by
    change List.replicate (2*m+1) true ++ (false :: tail) =
      true :: List.replicate (2*m) true ++ (false :: tail)
    rw [List.replicate_succ]
  rw [show 2*m+6=3+(2*m+3) by omega,run_add,hs,odd_c3]
  simp only [Option.bind_some]
  rw [run_add,af_pairs]
  simp only [Option.bind_some]
  exact a3_to_e1 tail (tens m ++ [false,true])

#print axioms odd_C0_to_E1
end BB429OddCZeroToE1
