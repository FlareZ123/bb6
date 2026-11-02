import Std

namespace Agent9FirstPassage

inductive Digit where
  | zero | four | six
  deriving DecidableEq, Repr

open Digit

def delta : Digit → Int
  | zero => -1
  | four => 4
  | six => 6

def displacement : List Digit → Int
  | [] => 0
  | d :: ds => delta d + displacement ds

theorem displacement_count (ds : List Digit) :
    displacement ds = - (ds.length : Int) + 5 * (ds.count four : Int) + 7 * (ds.count six : Int) := by
  induction ds with
  | nil => simp [displacement]
  | cons d ds ih =>
    cases d <;> simp [displacement, delta, ih] <;> omega

theorem first_passage_length (h : Nat) (ds : List Digit)
    (hit : (h : Int) + 1 + displacement ds = 0) :
    ds.length = h + 1 + 5 * ds.count four + 7 * ds.count six := by
  have hx := displacement_count ds
  omega

#print axioms Agent9FirstPassage.displacement_count
#print axioms Agent9FirstPassage.first_passage_length
end Agent9FirstPassage

namespace Agent9FirstPassage
private def denom : Nat := 1000000000
private def lower : Nat := 334894995
private def upper : Nat := 334894996

theorem root_lower_integer_sign :
    denom ^ 7 + lower ^ 5 * denom ^ 2 + lower ^ 7 >
      3 * lower * denom ^ 6 := by
  decide

theorem root_upper_integer_sign :
    denom ^ 7 + upper ^ 5 * denom ^ 2 + upper ^ 7 <
      3 * upper * denom ^ 6 := by
  decide

#print axioms Agent9FirstPassage.root_lower_integer_sign
#print axioms Agent9FirstPassage.root_upper_integer_sign
end Agent9FirstPassage
