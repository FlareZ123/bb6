import BB429OddExcursion
import Lean.Elab.Tactic.Omega

namespace BB429CZeroEvenReturn
open BB429OddExcursion

abbrev ones (n : Nat) : List Bool := List.replicate n true

/-- Unlike the prior existential right-pair scan, the left stack after every
    two-bit pair is given explicitly. -/
theorem a_right_pairs_exact (j : Nat) (l r : List Bool) :
    run (2*j) (z 0 l false (tens j ++ r)) =
      some (z 0 (ones (2*j) ++ l) false r) := by
  induction j generalizing l with
  | zero => simp [run, tens, ones]
  | succ j ih =>
      have hfirst : run 2 (z 0 l false (tens (j+1) ++ r)) =
          some (z 0 (true::true::l) false (tens j ++ r)) := by
        simpa [tens] using (a_right_two l (tens j ++ r))
      have hwords : ones (2*(j+1)) ++ l =
          ones (2*j) ++ (true::true::l) := by
        change List.replicate (2*(j+1)) true ++ l =
          List.replicate (2*j) true ++ (true::true::l)
        rw [show 2*(j+1) = 2*j+2 by omega,
          ← List.replicate_append_replicate]
        rfl
      rw [show 2*(j+1) = 2+2*j by omega, run_add, hfirst]
      simp only [Option.bind_some]
      rw [ih (true::true::l)]
      rw [hwords]

/-- Entire even prepared E/0 passage, now with the exact final left stack.
    Existing even_prepared_crosses supplied only an existential left stack. -/
theorem even_E0_crosses_exact (k : Nat) :
    run (4*k+7) (prepared (2*k+2)) =
      some (z 2 (ones (2*k+4)) true []) := by
  have hs : prepared (2*k+2) =
      z 4 (true::(ones (2*k) ++ [true])) false [true] := by
    change z 4 (List.replicate (2*k+2) true) false [true] = _
    rw [show 2*k+2 = (2*k+1)+1 by omega, List.replicate_succ]
    rw [show 2*k+1 = 2*k+1 by omega, List.replicate_succ']
  have h1 : run 1 (prepared (2*k+2)) =
      some (z 0 (ones (2*k) ++ [true]) true [false,true]) := by
    rw [hs]
    exact e_first _ _
  have h2 := af_pairs k [true] [false,true]
  have hlow := apair_low (tens k ++ [false,true])
  have hR := a_right_pairs_exact (k+1) [] [false,true]
  have hR' : run (2*(k+1))
      (z 0 [] false (true::false::(tens k ++ [false,true]))) =
      some (z 0 (ones (2*(k+1))) false [false,true]) := by
    simpa [tens] using hR
  have htail : run 2 (z 0 (ones (2*(k+1))) false [false,true]) =
      some (z 2 (ones (2*k+4)) true []) := by
    have ht := a_even_end (ones (2*(k+1)))
    have hwords : true::true::ones (2*(k+1)) = ones (2*k+4) := by
      change true::true::List.replicate (2*(k+1)) true =
        List.replicate (2*k+4) true
      rw [show 2*k+4 = (2*(k+1))+2 by omega,
        ← List.replicate_append_replicate]
      rfl
    simpa only [hwords] using ht
  have ht : 4*k+7 = 1+(2*k+(2+(2*(k+1)+2))) := by omega
  rw [ht,run_add,h1]
  simp only [Option.bind_some]
  rw [run_add,h2]
  simp only [Option.bind_some]
  rw [run_add,hlow]
  simp only [Option.bind_some]
  rw [run_add,hR']
  simp only [Option.bind_some]
  exact htail

/-- A fresh-right C/0 with an even full left block has a second C/0
    exactly three tape positions to its right after 4k+11 instructions.
    The complete right suffix stays blank. -/
theorem C0_even_to_C0 (k : Nat) :
    run (4*k+11) (z 2 (ones (2*k+2)) false []) =
      some (z 2 (true::false::ones (2*k+4)) false []) := by
  have hfirst : run 2 (z 2 (ones (2*k+2)) false []) =
      some (prepared (2*k+2)) := by rfl
  have hlast : run 2 (z 2 (ones (2*k+4)) true []) =
      some (z 2 (true::false::ones (2*k+4)) false []) := by rfl
  have ht : 4*k+11 = 2+((4*k+7)+2) := by omega
  rw [ht,run_add,hfirst]
  simp only [Option.bind_some]
  rw [run_add,even_E0_crosses_exact]
  simp only [Option.bind_some]
  exact hlast

#print axioms a_right_pairs_exact
#print axioms even_E0_crosses_exact
#print axioms C0_even_to_C0
end BB429CZeroEvenReturn
