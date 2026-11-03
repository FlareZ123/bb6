import Lean.Elab.Tactic.Omega

namespace BB6.Agent31Language

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def pairs : Nat → List Bool
  | 0 => []
  | n + 1 => false :: true :: pairs n

/-- A direct recognizer for the syntactic language (01)^r 1^b. -/
def regular : List Bool → Bool
  | false :: true :: ys => regular ys
  | true :: ys => ys.all id
  | [] => true
  | _ => false

private theorem all_ones (n : Nat) : (List.replicate n true).all id = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate, List.all] using ih

private theorem regular_ones (n : Nat) :
    regular (List.replicate n true) = true := by
  cases n with
  | zero => rfl
  | succ n => simpa [regular, List.replicate] using all_ones n

private theorem regular_pairs_ones (r b : Nat) :
    regular (pairs r ++ List.replicate b true) = true := by
  induction r with
  | zero => simpa [pairs] using regular_ones b
  | succ r ih => simpa [pairs, regular] using ih

private theorem irregular_escaped (h : Nat) :
    regular (pairs 2 ++ [false] ++ List.replicate (2*h+3) true ++
      [false] ++ List.replicate 6 true) = false := by
  have rep : List.replicate (2*h+3) true =
      [true,true,true] ++ List.replicate (2*h) true := by
    calc
      _ = List.replicate (3+2*h) true := by rw [Nat.add_comm (2*h) 3]
      _ = List.replicate 3 true ++ List.replicate (2*h) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [rep]
  simp [pairs, regular, List.all_append]

/-- The output after two source-derived raw returns lies outside all
    right-suffix words of the standard (01)^r 1^b regular language. -/
theorem second_escape_not_regular (h r b : Nat) :
    pairs 2 ++ [false] ++ List.replicate (2*h+3) true ++
      [false] ++ List.replicate 6 true ≠
      pairs r ++ List.replicate b true := by
  intro heq
  have h1 := irregular_escaped h
  rw [heq, regular_pairs_ones] at h1
  contradiction

#print axioms second_escape_not_regular


private theorem fourth_a_irregular (h : Nat) :
    regular (pairs 3 ++ [false] ++ List.replicate (2*h) true ++
      [false] ++ List.replicate 6 true) = false := by
  cases h with
  | zero => simp [pairs, regular]
  | succ h =>
    have rep : List.replicate (2*(h+1)) true =
        [true,true] ++ List.replicate (2*h) true := by
      have eqn : 2*(h+1) = 2+(2*h) := by omega
      rw [eqn]
      exact (List.replicate_append_replicate).symm
    rw [rep]
    simp [pairs, regular, List.all_append]

private theorem fourth_b_irregular (h : Nat) :
    regular ([false] ++ List.replicate (2*h+3) true ++
      [false] ++ List.replicate 6 true) = false := by
  have rep : List.replicate (2*h+3) true =
      [true,true,true] ++ List.replicate (2*h) true := by
    have eqn : 2*h+3 = 3+2*h := by omega
    rw [eqn]
    exact (List.replicate_append_replicate).symm
  rw [rep]
  simp [regular, List.all_append]

/-- The first fourth-checkpoint obstruction family is outside L at all sizes. -/
theorem fourth_escape_A_not_regular (h r b : Nat) :
    pairs 3 ++ [false] ++ List.replicate (2*h) true ++
      [false] ++ List.replicate 6 true ≠
      pairs r ++ List.replicate b true := by
  intro heq
  have hz := fourth_a_irregular h
  rw [heq, regular_pairs_ones] at hz
  contradiction

/-- The second fourth-checkpoint obstruction family is outside L at all sizes. -/
theorem fourth_escape_B_not_regular (h r b : Nat) :
    [false] ++ List.replicate (2*h+3) true ++
      [false] ++ List.replicate 6 true ≠
      pairs r ++ List.replicate b true := by
  intro heq
  have hz := fourth_b_irregular h
  rw [heq, regular_pairs_ones] at hz
  contradiction

#print axioms fourth_escape_A_not_regular
#print axioms fourth_escape_B_not_regular

end BB6.Agent31Language
