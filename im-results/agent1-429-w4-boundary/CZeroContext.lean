import CZeroEvenReturn
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 4096
set_option maxHeartbeats 10000000

namespace BB429CZeroContext
open BB429OddExcursion BB429CZeroEvenReturn

private theorem even_left (k : Nat) (tail : List Bool) :
    ones (2*k+2) ++ (false::tail) =
      true :: (ones (2*k+1) ++ (false::tail)) := by
  simp only [ones]
  rw [show 2*k+2 = (2*k+1)+1 by omega, List.replicate_succ]
  rfl

private theorem even_A_pair_input (k : Nat) (tail : List Bool) :
    ones (2*k+1) ++ (false::tail) =
      ones (2*k) ++ (true::false::tail) := by
  simp only [ones]
  rw [show 2*k+1 = (2*k)+1 by omega, List.replicate_succ']
  simp [List.append_assoc]

/-- The even E/0 return depends on the first zero to the left,
    independently of the tape beyond that zero. -/
theorem even_E0_context (k : Nat) (tail : List Bool) :
    run (4*k+7)
      (z 4 (ones (2*k+2) ++ (false::tail)) false [true]) =
    some (z 2 (ones (2*k+4) ++ tail) true []) := by
  have h1 : run 1 (z 4 (ones (2*k+2) ++ (false::tail)) false [true]) =
      some (z 0 (ones (2*k+1) ++ (false::tail)) true [false,true]) := by
    rw [even_left]; rfl
  have h2 : run (2*k)
      (z 0 (ones (2*k+1) ++ (false::tail)) true [false,true]) =
      some (z 0 (true::false::tail) true (tens k ++ [false,true])) := by
    rw [even_A_pair_input]
    simpa only [ones] using (af_pairs k (true::false::tail) [false,true])
  have h3 : run 2 (z 0 (true::false::tail) true
        (tens k ++ [false,true])) =
      some (z 0 tail false (tens (k+1) ++ [false,true])) := by
    simp only [tens]
    rfl
  have h4 := a_right_pairs_exact (k+1) tail [false,true]
  have h5 : run 2 (z 0 (ones (2*(k+1)) ++ tail) false [false,true]) =
      some (z 2 (ones (2*k+4) ++ tail) true []) := by
    have hw : ones (2*k+4) = true::true::ones (2*(k+1)) := by
      simp only [ones]
      rw [show 2*k+4 = 2+(2*(k+1)) by omega,
        ← List.replicate_append_replicate]
      rfl
    rw [hw]
    rfl
  have ht : 4*k+7 = 1+(2*k+(2+(2*(k+1)+2))) := by omega
  rw [ht,run_add,h1]
  simp only [Option.bind_some]
  rw [run_add,h2]
  simp only [Option.bind_some]
  rw [run_add,h3]
  simp only [Option.bind_some]
  rw [run_add,h4]
  simp only [Option.bind_some]
  exact h5

/-- Contextual transfer: arbitrary deeper left tape survives unchanged,
    and the next C/0 is exactly three cells farther right. -/
theorem even_C0_context (k : Nat) (tail : List Bool) :
    run (4*k+11) (z 2 (ones (2*k+2) ++ (false::tail)) false []) =
      some (z 2 (true::false::(ones (2*k+4) ++ tail)) false []) := by
  have h1 : run 2 (z 2 (ones (2*k+2) ++ (false::tail)) false []) =
      some (z 4 (ones (2*k+2) ++ (false::tail)) false [true]) := by rfl
  have h3 : run 2 (z 2 (ones (2*k+4) ++ tail) true []) =
      some (z 2 (true::false::(ones (2*k+4) ++ tail)) false []) := by rfl
  rw [show 4*k+11 = 2+((4*k+7)+2) by omega,
    run_add,h1]
  simp only [Option.bind_some]
  rw [run_add,even_E0_context]
  simp only [Option.bind_some]
  exact h3

/-- The nine-step turn reads precisely three blank cells beyond the
    preceding marked block. The rest of the left stack is untouched. -/
private theorem nine_context (tail right : List Bool) :
    run 9 (z 0 (false::false::false::tail) true (true::right)) =
      some (z 0 ([true,false,true,true] ++ tail) true right) := by rfl

private theorem four_context (tail right : List Bool) :
    run 4 (z 0 ([true,false,true,true] ++ tail) true right) =
      some (z 0 ([true,true,true,true] ++ tail) false right) := by rfl

private theorem odd_left (k : Nat) (tail : List Bool) :
    ones (2*k+3) ++ (false::false::false::tail) =
      true :: (ones (2*(k+1)) ++ (false::false::false::tail)) := by
  simp only [ones]
  rw [show 2*k+3 = 1+2*(k+1) by omega,
    ← List.replicate_append_replicate]
  rfl

/-- Three zeros beyond an odd marked block force a C/01 entry,
    even with arbitrary farther-left marked tape. -/
theorem odd_C0_context_fatal (k : Nat) (tail : List Bool) :
    ∃ left, run (4*k+20)
      (z 2 (ones (2*k+3) ++ (false::false::false::tail)) false []) =
        some (z 2 left false [true]) := by
  have h1 : run 2 (z 2 (ones (2*k+3) ++ (false::false::false::tail)) false []) =
      some (z 4 (ones (2*k+3) ++ (false::false::false::tail)) false [true]) := by rfl
  have h2 : run 1 (z 4 (ones (2*k+3) ++ (false::false::false::tail)) false [true]) =
      some (z 0 (ones (2*(k+1)) ++ (false::false::false::tail)) true [false,true]) := by
    rw [odd_left]; rfl
  have h3 : run (2*(k+1))
      (z 0 (ones (2*(k+1)) ++ (false::false::false::tail)) true [false,true]) =
      some (z 0 (false::false::false::tail) true (tens (k+1) ++ [false,true])) := by
    simpa only [ones] using (af_pairs (k+1) (false::false::false::tail) [false,true])
  have h9 : run 9 (z 0 (false::false::false::tail) true (tens (k+1) ++ [false,true])) =
      some (z 0 ([true,false,true,true] ++ tail) true
        (false::tens k ++ [false,true])) := by
    simpa [tens, List.cons_append, List.append_assoc] using
      (nine_context tail (false::tens k ++ [false,true]))
  have h4 : run 4 (z 0 ([true,false,true,true] ++ tail) true
        (false::tens k ++ [false,true])) =
      some (z 0 ([true,true,true,true] ++ tail) false
        (false::tens k ++ [false,true])) := four_context _ _
  have hA : run 1 (z 0 ([true,true,true,true] ++ tail) false
        (false::tens k ++ [false,true])) =
      some (z 1 (true::[true,true,true,true] ++ tail) false
        (tens k ++ [false,true])) := by rfl
  obtain ⟨l,hB⟩ := b_right_pairs k (true::[true,true,true,true] ++ tail) [false,true]
  have hC : run 1 (z 1 l false [false,true]) =
      some (z 2 (true::l) false [true]) := by rfl
  refine ⟨true::l,?_⟩
  have ht : 4*k+20 = 2+(1+(2*(k+1)+(9+(4+(1+(2*k+1)))))) := by omega
  rw [ht,run_add,h1]
  simp only [Option.bind_some]
  rw [run_add,h2]
  simp only [Option.bind_some]
  rw [run_add,h3]
  simp only [Option.bind_some]
  rw [run_add,h9]
  simp only [Option.bind_some]
  rw [run_add,h4]
  simp only [Option.bind_some]
  rw [run_add,hA]
  simp only [Option.bind_some]
  rw [run_add,hB]
  simp only [Option.bind_some]
  exact hC

theorem odd_C0_context_halts (k : Nat) (tail : List Bool) :
    run (4*k+22)
      (z 2 (ones (2*k+3) ++ (false::false::false::tail)) false []) = none := by
  obtain ⟨left,h⟩ := odd_C0_context_fatal k tail
  rw [show 4*k+22=(4*k+20)+2 by omega,run_add,h]
  rfl

#print axioms even_C0_context
#print axioms odd_C0_context_halts
end BB429CZeroContext
