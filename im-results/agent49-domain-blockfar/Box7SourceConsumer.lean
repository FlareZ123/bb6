import Box7Weighted
import Raw10BoxBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49Box7
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent49BoxBridge

/-- Compare finite pointwise membership, independently of domain ordering. -/
def sourceMatch (b : BB6.Agent49Box.Box Slot Transition) : Bool :=
  slots.all fun s => choices.all fun t =>
    decide ((t ∈ b s) ↔ (t ∈ baseBox s))

theorem sourceMatch_sound (b : BB6.Agent49Box.Box Slot Transition)
    (h : sourceMatch b=true) (m : Machine) (hm : BB6.Agent49Box.Fits b m) :
    BB6.Agent49BoxOneHalt.Fits baseBox m := by
  intro s
  have hs := List.all_eq_true.mp h s (slots_complete s)
  have ht := List.all_eq_true.mp hs (m s) (choices_complete (m s))
  exact (of_decide_eq_true ht).mp (hm s)

theorem source_has_box7 : raw10Remainder.any sourceMatch=true := by decide +kernel

/-- At least one exact source residual rectangle is closed at the common
weighted target. This witness can be removed from the residual obligation. -/
theorem raw10_box7_closed (B : Nat) (hB : 41≤B) :
    ∃ b ∈ raw10Remainder, sourceMatch b=true ∧
      ∀ m, BB6.Agent49Box.Fits b m → WeightedBound B m := by
  obtain ⟨b,hb,hmatch⟩ := List.any_eq_true.mp source_has_box7
  exact ⟨b,hb,hmatch,fun m hm => box7_weighted B hB m (sourceMatch_sound b hmatch m hm)⟩

/-- Consume the checked subset without assuming any of the remaining boxes
are closed. -/
theorem residual_without_box7 (B : Nat) (hB : 41≤B)
    (hrest : ∀ b ∈ raw10Remainder, sourceMatch b=false →
      ∀ m, BB6.Agent49Box.Fits b m → WeightedBound B m) :
    ∀ b ∈ raw10Remainder, ∀ m, BB6.Agent49Box.Fits b m → WeightedBound B m := by
  intro b hb m hm
  cases h : sourceMatch b with
  | false => exact hrest b hb h m hm
  | true => exact box7_weighted B hB m (sourceMatch_sound b h m hm)

#print axioms raw10_box7_closed
#print axioms residual_without_box7
end BB6.Agent49Box7
