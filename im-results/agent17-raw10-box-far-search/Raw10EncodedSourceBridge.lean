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
  ⟨2 * s.1.val + (if s.2 then 1 else 0), by
    have hq : s.1.val < 6 := s.1.isLt
    have hb : (if s.2 then 1 else 0) ≤ 1 := by
      cases s.2 <;> simp
    omega⟩

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

/-- A Boolean, finite pointwise equality test for a source and encoded box. -/
def boxMatches (source : Box Slot Transition)
    (encoded : Box (Fin 12) (Fin 25)) : Bool :=
  BB6.Agent49BoxBridge.slots.all fun s =>
    decide (source s = (encoded (slotIndex s)).map decodeCode)

theorem boxMatches_sound (source : Box Slot Transition)
    (encoded : Box (Fin 12) (Fin 25))
    (h : boxMatches source encoded = true) :
    ∀ s, source s = (encoded (slotIndex s)).map decodeCode := by
  intro s
  exact of_decide_eq_true
    (List.all_eq_true.mp h s (BB6.Agent49BoxBridge.slots_complete s))

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
    corresponding source-defined BoxComplement residual. -/
theorem encoded_boxes_match_source :
    (List.finRange 34).all (fun i =>
      boxMatches (raw10Remainder[i.val]!) (boxes[i.val]!)) = true := by
  decide

theorem exact_box_at_index (i : Fin 34) :
    ∀ s, raw10Remainder[i.val]! s =
      (boxes[i.val]! (slotIndex s)).map decodeCode := by
  apply boxMatches_sound
  exact List.all_eq_true.mp encoded_boxes_match_source i (List.mem_finRange i)

#print axioms encoded_rows_are_source_rows
#print axioms source_remainder_count
#print axioms encoded_remainder_count
#print axioms boxMatches_sound
#print axioms encoded_boxes_match_source
#print axioms exact_box_at_index

end BB6.Agent17Raw10BoxFar
