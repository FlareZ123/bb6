import Raw10Encoded
import Q02700Consumer

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13Raw10Q2700Encoded

open BB6.Agent49BoxComplement
open BB6.Agent49Raw10Encoded
open BB6.Agent5Q0HeldBlock

/-- Encode an ordinary transition using the raw10 convention:
    1 + 4*nextState + 2*writeBit + rightBit. -/
def moveCode (m : BB6BlockFAR.Move) : Nat :=
  1 + 4 * m.next.val + (if m.write then 2 else 0) +
    (if m.right then 1 else 0)

/-- The source-semantic q2700 table encoded in the raw10 Fin-25 format.
    Zero denotes the unique unconstrained D0 slot. -/
def q2700Row : List Nat :=
  q2700Entries.map fun e =>
    match e with
    | none => 0
    | some m => moveCode m

theorem q2700Row_exact :
    q2700Row = [8, 13, 11, 4, 19, 3, 0, 6, 20, 22, 24, 9] := by
  decide

def q2700Cube : Cube Slot Value := cubeOf q2700Row

/-- The new one-hole cylinder is a subcylinder of the raw10 parent
    (A0=1RB, B0=1LC). -/
theorem q2700Cube_within_raw10_parent :
    ∀ s v, (s, v) ∈ q2700Cube → v ∈ parentBox s := by
  decide

/-- Two finite cubes intersect exactly when every shared slot agrees. -/
def cubesCompatible (a b : Cube Slot Value) : Bool :=
  a.all fun p =>
    b.all fun q =>
      if p.1 == q.1 then p.2 == q.2 else true

/-- q2700 is disjoint from every one of the 66 existing encoded cylinders
    (65 side witnesses plus the q2800 held leaf). -/
theorem q2700_disjoint_from_66_rows :
    (rows.map cubeOf).all (fun c => !(cubesCompatible c q2700Cube)) = true := by
  decide

def boxesWithQ2700 : List (Box Slot Value) :=
  subtractMany slots boxes [q2700Cube]

/-- Kernel-checked exact subtraction: the new residual is precisely the old
    66-cylinder residual with the q2700 cylinder removed. -/
theorem q2700_remainder_exact (m : Slot → Value) :
    (∃ b ∈ boxesWithQ2700, Fits b m) ↔
      (∃ b ∈ boxes, Fits b m) ∧ ¬ Matches q2700Cube m := by
  simpa [boxesWithQ2700] using
    (subtractMany_exact slots boxes [q2700Cube] m)

/-- VM diagnostics only: these finite cardinalities/masses are not presented
    as kernel-decided cardinality theorems. -/
def q2700RemainderMass : Nat :=
  (boxesWithQ2700.map boxMass).sum

#eval (boxesWithQ2700.length, q2700RemainderMass)
#eval (25^10 - (boxes.map boxMass).sum,
       25^10 - q2700RemainderMass,
       (boxes.map boxMass).sum - q2700RemainderMass)

#print axioms q2700Row_exact
#print axioms q2700Cube_within_raw10_parent
#print axioms q2700_disjoint_from_66_rows
#print axioms q2700_remainder_exact

end BB6.Agent13Raw10Q2700Encoded
