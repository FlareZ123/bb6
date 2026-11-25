import Raw10BoxCore
import Raw10Encoded

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Raw10BoxFar

open BB6Coverage
open BB6.Agent49Box
open BB6.Agent49BoxBridge
open BB6.Agent49BoxEncoded
open BB6.Agent50RootFrontier

/-- Source slot order is A0,A1,...,F0,F1, encoded by 2*state+symbol. -/
def slotIndex (s : Slot) : Fin 12 :=
  ⟨2 * s.1.val + (if s.2 then 1 else 0), by have h := s.1.isLt; omega⟩

/-- The standard 1..24 move code used by Raw10Encoded and BlockFAR. -/
def encodeMove (mv : BB6Coverage.Move) : Nat :=
  1 + 4 * mv.next.val + 2 * (if mv.write then 1 else 0) +
    (if mv.right then 1 else 0)

def encodePartial (p : PartialMachine) : List Nat :=
  BB6.Agent49BoxBridge.slots.map fun s =>
    match p s with
    | none => 0
    | some none => 0
    | some (some mv) => encodeMove mv

/-- Decode the Fin 25 transition code, with 0 representing a halt value.
    The source raw10 tables have no assigned halts, so encoded zero entries
    are exactly their unassigned/wildcard slots. -/
def decodeCode (n : Fin 25) : Transition :=
  if n.val = 0 then none
  else
    let j := n.val - 1
    some ⟨decide ((j / 2) % 2 = 1), decide (j % 2 = 1),
      ⟨j / 4, by have hn := n.isLt; omega⟩⟩

/-- A pointwise, order-sensitive equality of a source box and an encoded box. -/
def BoxMatches (source : Box Slot Transition)
    (encoded : Box (Fin 12) (Fin 25)) : Prop :=
  ∀ s, source s = (encoded (slotIndex s)).map decodeCode

/-- The literal 66 rows are exactly the 65 filtered source side witnesses
    followed by the authentic q_i(2800,100) held table. -/
theorem encoded_rows_are_source_rows :
    rows = (sideTables ++ [held]).map encodePartial := by
  decide

theorem source_remainder_count : raw10Remainder.length = 34 := by
  decide

theorem encoded_remainder_count : boxes.length = 34 := by
  decide

/-- Every encoded residual box, at its original index, is exactly the
    corresponding source-defined BoxComplement residual. This closes the
    source-identity gap between the Python search and Raw10BoxCore. -/
theorem encoded_boxes_match_source :
    ∀ i : Fin 34,
      BoxMatches (raw10Remainder[i.val]!) (boxes[i.val]!) := by
  decide

#print axioms encoded_rows_are_source_rows
#print axioms source_remainder_count
#print axioms encoded_remainder_count
#print axioms encoded_boxes_match_source

end BB6.Agent17Raw10BoxFar
