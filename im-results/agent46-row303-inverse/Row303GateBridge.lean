import Row303GateOriginal

namespace BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF

theorem preGate_iff_regex (L : List Nat) :
    preGate L ↔
      (∃ tail, L = 3 :: 0 :: tail) ∨
      (∃ n tail, L = 1 :: (List.replicate n 0 ++ 2 :: 0 :: tail)) := by
  cases L with
  | nil => simp [preGate]
  | cons a Lt =>
    rcases a with _ | _ | _ | a
    · simp [preGate]
    · simpa [preGate] using core_iff_regex Lt
    · simp [preGate]
    · cases a with
      | zero =>
          cases Lt with
          | nil => simp [preGate]
          | cons b Bs =>
              cases b with
              | zero => simp [preGate]
              | succ b => simp [preGate]
      | succ a => simp [preGate]

/-- Exact all-input, all-right-stack characterization of one-return gate
    predecessors in the pinned original six-state machine accelerator. -/
theorem exact_next_gate_predecessors (L R : List Nat) :
    (∃ L' R', next (.E L R) = some (.E (0 :: L') R')) ↔
      (∃ tail, L = 3 :: 0 :: tail) ∨
      (∃ n tail, L = 1 :: (List.replicate n 0 ++ 2 :: 0 :: tail)) := by
  exact (next_gate_iff L R).trans (preGate_iff_regex L)

#print axioms exact_next_gate_predecessors
end BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF
