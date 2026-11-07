import BB429SourceE1Delta
import Lean.Elab.Tactic.Omega

namespace BB429E1ShiftDelta
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta

/-- A prefix of the original-source `shift_E_11` sweep. The source E/1
    instruction writes one and moves left at every step, so after exactly
    `j` steps the head is `j` cells left of its starting position. -/
theorem e1_left_prefix (n j : Nat) (tail suffix : List Bool) :
    j ≤ n →
    runWithDelta j (z 4 (ones n ++ tail) true (ones 6 ++ suffix)) =
      some (z 4 (ones (n-j) ++ tail) true (ones (j+6) ++ suffix), -(j : Int)) := by
  induction j generalizing n tail suffix with
  | zero =>
      intro _
      simp [runWithDelta, ones]
  | succ j ih =>
      intro hj
      have hn : 0 < n := by omega
      have hrep : ones n = true :: ones (n-1) := by
        cases n with
        | zero => omega
        | succ n =>
          simp only [ones, Nat.succ_sub_one]
          rw [List.replicate_succ]
      have h1 :
          runWithDelta 1 (z 4 (ones n ++ tail) true (ones 6 ++ suffix)) =
            some (z 4 (ones (n-1) ++ tail) true (ones 7 ++ suffix), -1) := by
        rw [hrep]
        rfl
      rw [show j+1 = 1+j by omega, runWithDelta_add, h1]
      simp only [Option.bind_some]
      have hright : ones 7 ++ suffix = ones 6 ++ (ones 1 ++ suffix) := by
        rw [show 7 = 6+1 by omega, ones_add 6 1]
        simp [List.append_assoc]
      rw [hright]
      have hih := ih (n-1) tail (ones 1 ++ suffix) (by omega)
      rw [hih]
      simp only [Option.map_some]
      have hleft : n-1-j = n-(1+j) := by omega
      have hright' : ones (j+6) ++ (ones 1 ++ suffix) =
          ones (1+j+6) ++ suffix := by
        have heq : 1+j+6 = (j+6)+1 := by omega
        rw [heq, ones_add (j+6) 1]
        simp [List.append_assoc]
      have hdelta : (-1 : Int) + (-(j : Int)) =
          -((1+j : Nat) : Int) := by omega
      rw [hleft, hright', hdelta]

/-- Exact displacement of the pinned Cryptids helper `shift_E_11`:
    its `(11)^k` left prefix is consumed by `2*k` E/1 instructions,
    and becomes a `(11)^k` block immediately to the right of the original
    seven-one suffix. The head displacement is exactly `-2*k`. -/
theorem shift_E11_total (k : Nat) (tail suffix : List Bool) :
    runWithDelta (2*k) (z 4 (ones (2*k) ++ tail) true (ones 6 ++ suffix)) =
      some (z 4 tail true (ones (2*k+6) ++ suffix), -((2*k : Nat) : Int)) := by
  have h := e1_left_prefix (2*k) (2*k) tail suffix (by omega)
  simpa [ones] using h

/-- Every nonempty prefix of `shift_E_11` is strictly left of its start.
    This is the one-sided head condition needed by a last-writer argument;
    this theorem concerns the macro only, not the later unbounded suffix. -/
theorem shift_E11_prefix_strict (k j : Nat) (tail suffix : List Bool)
    (hj : 0 < j) (hbound : j ≤ 2*k) :
    ∃ c : Zipper,
      runWithDelta j (z 4 (ones (2*k) ++ tail) true (ones 6 ++ suffix)) =
        some (c, -(j : Int)) ∧ -(j : Int) < 0 := by
  refine ⟨z 4 (ones (2*k-j) ++ tail) true (ones (j+6) ++ suffix), ?_, ?_⟩
  · exact e1_left_prefix (2*k) j tail suffix hbound
  · omega

/-- The macro's terminal configuration remains in E/1 at the left endpoint;
    a later proof must determine whether the rest of the authentic J path
    ever crosses any of the swept cells again. -/
theorem shift_E11_terminal_is_E1 (k : Nat) (tail suffix : List Bool) :
    runWithDelta (2*k) (z 4 (ones (2*k) ++ tail) true (ones 6 ++ suffix)) =
      some (z 4 tail true (ones (2*k+6) ++ suffix), -((2*k : Nat) : Int)) ∧
    (z 4 tail true (ones (2*k+6) ++ suffix)).state = 4 ∧
    (z 4 tail true (ones (2*k+6) ++ suffix)).current = true := by
  exact ⟨shift_E11_total k tail suffix, rfl, rfl⟩

#print axioms e1_left_prefix
#print axioms shift_E11_total
#print axioms shift_E11_prefix_strict
#print axioms shift_E11_terminal_is_E1

end BB429E1ShiftDelta
