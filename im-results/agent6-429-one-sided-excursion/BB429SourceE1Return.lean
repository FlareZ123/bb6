import BB429OddExcursion
import Lean.Elab.Tactic.Omega

namespace BB429SourceE1Return
open BB429OddExcursion

/-- A block of n ones. -/
def ones (n : Nat) : List Bool := List.replicate n true

/-- The nearest-first left-tape word (01)^n. -/
def pairs01 : Nat → List Bool
 | 0 => []
 | n+1 => false :: true :: pairs01 n

/-- The source S_E(b,m,k) head-relative configuration, with its arbitrary
    right suffix. The current E/1 cell is separate from both stacks. -/
def sourceScanE (b : Nat) (suffix : List Bool) : Zipper :=
  z 4 (pairs01 b ++ ones 5) true suffix

/-- Configuration immediately after the E/1 instruction has written one
    and moved left. The original current cell is now the first right cell. -/
def e1After : Nat → List Bool → Zipper
 | 0, suffix => z 4 (ones 4) true (true :: suffix)
 | n+1, suffix => z 4 (true :: (pairs01 n ++ ones 5)) false (true :: suffix)

/-- Exact number of further steps to return to the cell written by E/1. -/
def crossTime : Nat → Nat
 | 0 => 41
 | 1 => 15
 | n+2 => crossTime n + 14

/-- The left stack when the original E/1-written cell is revisited. -/
def finalLeft : Nat → List Bool
 | 0 => true :: false :: true :: false :: true :: ones 5
 | 1 => ones 8
 | n+2 => ones 4 ++ finalLeft n

def leftBlock : List Bool := [true,false,true,false]
def rightBlock : List Bool := [true,true,false,true]

/-- Six raw instructions consume two nearest 01 pairs and append 1101 to
    the right of the marked boundary. -/
theorem six_step_macro (tail suffix : List Bool) :
  run 6 (z 4 (leftBlock ++ tail) false (true :: suffix)) =
    some (z 4 tail false (true :: rightBlock ++ suffix)) := by
  rfl

/-- Eight raw instructions consume the appended 1101 and prepend four ones
    to the left stack, preserving every later right-hand cell. -/
theorem eight_step_macro (left suffix : List Bool) :
  run 8 (z 2 left true (rightBlock ++ suffix)) =
    some (z 2 (ones 4 ++ left) true suffix) := by
  rfl

theorem nat_two_step_induction {P : Nat → Prop} (h0 : P 0) (h1 : P 1)
    (hs : ∀ n, P n → P (n+2)) : ∀ n, P n := by
  have hp : ∀ n, P n ∧ P (n+1) := by
    intro n
    induction n with
    | zero => exact ⟨h0,h1⟩
    | succ n ih => exact ⟨ih.2, hs n ih.1⟩
  intro n
  exact (hp n).1

/-- Main exact one-sided return theorem. It is uniform in the untouched
    right suffix, so it applies to all source S_E right-hand parameters. -/
theorem e1_cross (b : Nat) (suffix : List Bool) :
  run (crossTime b) (e1After b suffix) =
    some (z 2 (finalLeft b) true suffix) := by
  have hAll : ∀ n, ∀ suffix, run (crossTime n) (e1After n suffix) =
      some (z 2 (finalLeft n) true suffix) := by
    apply nat_two_step_induction
    · intro suffix
      rfl
    · intro suffix
      rfl
    · intro n ih suffix
      have h6 : run 6 (e1After (n+2) suffix) =
          some (e1After n (rightBlock ++ suffix)) := by
        cases n with
        | zero => rfl
        | succ n =>
          change run 6 (z 4 (leftBlock ++ (true :: (pairs01 n ++ ones 5))) false (true :: suffix)) =
            some (z 4 (true :: (pairs01 n ++ ones 5)) false (true :: rightBlock ++ suffix))
          exact six_step_macro (true :: (pairs01 n ++ ones 5)) suffix
      have hi := ih (rightBlock ++ suffix)
      have h8 : run 8 (z 2 (finalLeft n) true (rightBlock ++ suffix)) =
          some (z 2 (ones 4 ++ finalLeft n) true suffix) := by
        exact eight_step_macro (finalLeft n) suffix
      have htime : crossTime (n+2) = 6 + (crossTime n + 8) := by
        simp [crossTime]
        omega
      rw [htime, run_add, h6]
      simp only [Option.bind_some]
      rw [run_add, hi]
      simp only [Option.bind_some]
      simpa [finalLeft, List.append_assoc] using h8
  exact hAll b suffix

/-- The E/1 instruction in the original #429 table. -/
theorem source_E1_row : action 4 true = some (4,true,false) := rfl

/-- At the return, C/1 writes zero and moves right, overwriting the E/1 mark. -/
theorem returned_C1_overwrites : action 2 true = some (1,false,true) := rfl

/-- The first raw step from the source S_E configuration is precisely E/1. -/
theorem sourceScanE_e1_step (b : Nat) (suffix : List Bool) :
  one (sourceScanE b suffix) = some (e1After b suffix) := by
  cases b <;> rfl

/-- Starting at the source S_E configuration, the E/1 step is followed by
    a return to the very cell it wrote. At that return the machine is C/1;
    its next instruction writes zero on that cell. -/
theorem sourceScanE_e1_revisit (b : Nat) (suffix : List Bool) :
  run (crossTime b + 1) (sourceScanE b suffix) =
    some (z 2 (finalLeft b) true suffix) := by
  have h1 : run 1 (sourceScanE b suffix) = some (e1After b suffix) := by
    simp [run, sourceScanE_e1_step]
  rw [show crossTime b + 1 = 1 + crossTime b by omega, run_add, h1]
  simp only [Option.bind_some]
  exact e1_cross b suffix

theorem ones_add (m n : Nat) : ones (m+n) = ones m ++ ones n := by
  simp [ones]

theorem crossTime_even (k : Nat) : crossTime (2*k) = 14*k+41 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : 2*(k+1) = 2*k+2 := by omega
    rw [h, crossTime, ih]
    omega

theorem crossTime_odd (k : Nat) : crossTime (2*k+1) = 14*k+15 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : 2*(k+1)+1 = (2*k+1)+2 := by omega
    rw [h, crossTime, ih]
    omega

theorem finalLeft_even (k : Nat) :
  finalLeft (2*k) = ones (4*k+1) ++ [false,true,false,true] ++ ones 5 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : 2*(k+1) = 2*k+2 := by omega
    rw [h, finalLeft, ih]
    rw [show 4*(k+1)+1 = 4+(4*k+1) by omega]
    rw [ones_add 4 (4*k+1)]
    rfl

theorem finalLeft_odd (k : Nat) : finalLeft (2*k+1) = ones (4*k+8) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : 2*(k+1)+1 = (2*k+1)+2 := by omega
    rw [h, finalLeft, ih]
    rw [show 4*(k+1)+8 = 4+(4*k+8) by omega]
    rw [ones_add 4 (4*k+8)]

#print axioms e1_cross
#print axioms sourceScanE_e1_revisit
#print axioms crossTime_even
#print axioms crossTime_odd
#print axioms finalLeft_even
#print axioms finalLeft_odd

end BB429SourceE1Return
