import CZeroContext
import Lean.Elab.Tactic.Omega

namespace BB429CZeroContextToE1
open BB429OddExcursion BB429CZeroEvenReturn BB429CZeroContext

/-- The C/0 to E/1 entry leaves the entire unknown farther-left tape
    unchanged beyond the identified 10 prefix. -/
theorem C0_to_E1_6_context (n : Nat) (tail : List Bool) :
    run 6 (z 2 (true::false::(ones n ++ tail)) false []) =
      some (z 4 (ones n ++ tail) true [true,false,true]) := by rfl

/-- An E/1 sweep copies any finite block of marked cells to the right
    and preserves arbitrary tape beyond that block. -/
theorem E1_ones_sweep_context (n : Nat) (tail suffix : List Bool) :
    run n (z 4 (ones n ++ tail) true suffix) =
      some (z 4 tail true (ones n ++ suffix)) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
      have hfirst : run 1 (z 4 (ones (n+1) ++ tail) true suffix) =
          some (z 4 (ones n ++ tail) true (true::suffix)) := by rfl
      have hwords : ones n ++ (true::suffix) = ones (n+1) ++ suffix := by
        simp [ones,List.replicate_succ',List.append_assoc]
      rw [show n+1=1+n by omega,run_add,
        show 1+n=n+1 by omega,hfirst]
      simp only [Option.bind_some]
      rw [ih (true::suffix),hwords]

/-- A fresh C/0 with left 10 1^(2k+4) L reaches E/1 at the unknown
    left context after exactly 2k+10 real machine instructions. -/
theorem C0_to_E1_context (k : Nat) (tail : List Bool) :
    run (2*k+10) (z 2 (true::false::(ones (2*k+4) ++ tail)) false []) =
      some (z 4 tail true (ones (2*k+4) ++ [true,false,true])) := by
  rw [show 2*k+10=6+(2*k+4) by omega,
    run_add,C0_to_E1_6_context]
  simp only [Option.bind_some]
  exact E1_ones_sweep_context (2*k+4) tail [true,false,true]

/-- Exact 6k+21-step bridge from any even C/0 context to the E/1
    boundary at which the remaining arbitrary tape finally matters. -/
theorem even_C0_to_E1_context (k : Nat) (tail : List Bool) :
    run (6*k+21) (z 2 (ones (2*k+2) ++ (false::tail)) false []) =
      some (z 4 tail true (ones (2*k+4) ++ [true,false,true])) := by
  rw [show 6*k+21=(4*k+11)+(2*k+10) by omega,
    run_add,even_C0_context]
  simp only [Option.bind_some]
  exact C0_to_E1_context k tail

#print axioms C0_to_E1_6_context
#print axioms E1_ones_sweep_context
#print axioms C0_to_E1_context
#print axioms even_C0_to_E1_context
end BB429CZeroContextToE1
