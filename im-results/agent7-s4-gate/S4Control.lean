module

public import BusyBeaver.BB6.Accelerations.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

@[expose] public section

namespace BB6.Agent7S4Control

open BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF
open BusyBeaver.Stack

/-- Three unconditional exact source-transitions in the S4 4-phase orbit,
    valid for every finite tail without any reachability assumptions. -/
theorem one_to_zero (tail : List Nat) :
    highLevelNext (.C 1 (3 :: 5 :: tail)) =
      some (.C 0 (4 :: 7 :: tail)) := by
  rfl

theorem zero_to_two (tail : List Nat) :
    highLevelNext (.C 0 (4 :: 7 :: tail)) =
      some (.C 2 (4 :: 7 :: tail)) := by
  rfl

theorem two_to_three (tail : List Nat) :
    highLevelNext (.C 2 (4 :: 7 :: tail)) =
      some (.C 3 (5 :: 7 :: tail)) := by
  rfl

/-- Exact three-step return from the restricted one-phase S4 section. -/
theorem three_safe_phases (tail : List Nat) :
    highLevelNext (.C 1 (3 :: 5 :: tail)) =
      some (.C 0 (4 :: 7 :: tail)) ∧
    highLevelNext (.C 0 (4 :: 7 :: tail)) =
      some (.C 2 (4 :: 7 :: tail)) ∧
    highLevelNext (.C 2 (4 :: 7 :: tail)) =
      some (.C 3 (5 :: 7 :: tail)) :=
  ⟨one_to_zero tail, zero_to_two tail, two_to_three tail⟩


/-- The 6-prefix source epoch is universally safe and performs an exact
    one-head carry on the remaining stack. -/
theorem normalized_six (tail : List Nat) :
    highLevelNext (.C 3 (5 :: 7 :: 6 :: tail)) =
      some (.C 1 (3 :: 5 :: 8 :: bumpHeadBy 6 tail)) := by
  cases tail with
  | nil => rfl
  | cons b rest => rfl

/-- The 8-prefix source epoch is universally safe and performs a distinct
    one-head carry. -/
theorem normalized_eight (tail : List Nat) :
    highLevelNext (.C 3 (5 :: 7 :: 8 :: tail)) =
      some (.C 1 (3 :: 5 :: 9 :: bumpHeadBy 7 tail)) := by
  cases tail with
  | nil => rfl
  | cons b rest => rfl

#print axioms BB6.Agent7S4Control.normalized_six
#print axioms BB6.Agent7S4Control.normalized_eight

#print axioms BB6.Agent7S4Control.three_safe_phases

end BB6.Agent7S4Control
