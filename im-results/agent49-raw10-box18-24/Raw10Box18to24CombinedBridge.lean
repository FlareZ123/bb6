import Box18to24Source
import HeldBlockRaw10Combined
import WeightedFirstOneCover
import WeightedTNFQueueOrbit
import TNFPilot

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Box18to24CombinedBridge

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49Box
open BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109
open BB6.Agent17Raw10CombinedConsumer

abbrev Parent := BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC
abbrev CombinedRemainder :=
  BB6.Agent17Raw10CombinedConsumer.raw10RemainderWithCycleAndHalt
abbrev EncodedBox := BB6.Agent49Box.Box (Fin 12) (Fin 25)

/-- Extensional equality check for encoded 12-slot product boxes. -/
def sameBox (b1 b2 : EncodedBox) : Bool :=
  (List.finRange 12).all (fun s => decide (b1 s = b2 s))

theorem sameBox_eq {b1 b2 : EncodedBox} (h : sameBox b1 b2 = true) :
    b1 = b2 := by
  funext s
  have hall : ∀ i ∈ List.finRange 12, decide (b1 i = b2 i) = true :=
    List.all_eq_true.mp h
  have hs : decide (b1 s = b2 s) = true := hall s (by simp)
  exact of_decide_eq_true hs

/-- A box in the expanded 41-box remainder is one of the seven old
    source-certified rectangles exactly when this finite check succeeds. -/
def closedMatchCombined (r : EncodedBox) : Bool :=
  (BB6.Agent49Box18to24.closedRows).any
    (fun a => sameBox r (BB6.Agent49Box18to24.rect a))

theorem closedMatchCombined_exists {r : EncodedBox}
    (h : closedMatchCombined r = true) :
    ∃ a ∈ BB6.Agent49Box18to24.closedRows,
      sameBox r (BB6.Agent49Box18to24.rect a) = true := by
  change (BB6.Agent49Box18to24.closedRows).any
    (fun a => sameBox r (BB6.Agent49Box18to24.rect a)) = true at h
  exact List.any_eq_true.mp h

/-- Each of the seven original source-certified rectangles survives
    unchanged in the expanded remainder after the cycle and halt cylinders. -/
theorem rects_in_combined_remainder :
    ∀ a ∈ BB6.Agent49Box18to24.closedRows,
      ∃ r ∈ CombinedRemainder,
        sameBox r (BB6.Agent49Box18to24.rect a) = true := by
  intro a ha
  have hcases : a = 19 ∨ a = 18 ∨ a = 17 ∨ a = 8 ∨
      a = 6 ∨ a = 3 ∨ a = 2 := by
    simpa [BB6.Agent49Box18to24.closedRows] using ha
  rcases hcases with h | h | h | h | h | h | h
  all_goals
    subst a
    exact List.any_eq_true.mp (by decide)

/-- The seven closed rectangles are seven distinct members of the 41-box
    expanded remainder; the explicit complement therefore has 34 boxes. -/
theorem closed_match_count :
    (CombinedRemainder.filter closedMatchCombined).length = 7 := by
  decide

theorem open_remainder_count :
    (CombinedRemainder.filter (fun r => !closedMatchCombined r)).length = 34 := by
  decide

/-- Source-accepted parent Cover using the held BlockFAR leaf, Agent50's
    cycle and halt cylinders, and the seven 598-bound rectangles. Only the
    remaining 34 expanded-remainder boxes are left as explicit obligations. -/
theorem raw10_cover_with_cycle_halt_boxes18to24 (B : Nat)
    (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ CombinedRemainder,
      closedMatchCombined r = false →
        ∀ m : BB6Coverage.Machine,
          BB6.Agent49Box.Fits r m →
            BB6.Agent13BlankDelay.WeightedBound B m) :
    BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B) Parent := by
  apply BB6.Agent13HeldBlockRaw10Combined.raw10_cover_with_cycle_and_halt B hB
  intro r hr m hm
  cases hmatch : closedMatchCombined r with
  | true =>
      obtain ⟨a, ha, heq⟩ := closedMatchCombined_exists hmatch
      have hbox : r = BB6.Agent49Box18to24.rect a := sameBox_eq heq
      have hm' : BB6.Agent49Box.Fits (BB6.Agent49Box18to24.rect a) m := by
        simpa [hbox] using hm
      have h598 := BB6.Agent49Box18to24.rectBound a ha m hm'
      intro k d hk hd
      exact Nat.le_trans (h598 k d hk hd) (by omega)
  | false =>
      exact hOpen r hr hmatch m hm

/-- Root-level exactness consumer. The canonical roster's soundness and
    exact parent membership are explicit inputs; every other roster entry
    and the 34-box expanded complement remain explicit obligations. -/
theorem exact_from_raw10_boxes18to24_combined (B : Nat)
    (hB : 7014 ≤ B)
    (roster : List (List BB6Coverage.Move × BB6Coverage.PartialMachine))
    (hroot : ∀ m : BB6Coverage.Machine,
      BB6Coverage.compatible BB6.Agent50TNFPilot.root m →
        BB6.Agent13BlankDelay.WeightedBound 7014 m ∨
        ∃ e ∈ roster, BB6.Agent13BlankDelay.TNFQuotientCompatible e.2 m)
    (hParent : ∃ e ∈ roster, e.2 = Parent)
    (hOpen : ∀ r ∈ CombinedRemainder,
      closedMatchCombined r = false →
        ∀ m : BB6Coverage.Machine,
          BB6.Agent49Box.Fits r m →
            BB6.Agent13BlankDelay.WeightedBound B m)
    (hOther : ∀ e ∈ roster, e.2 ≠ Parent →
      BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  obtain ⟨eParent, heParent, hParentEq⟩ := hParent
  have hParentCover :
      BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B) eParent.2 := by
    rw [hParentEq]
    exact raw10_cover_with_cycle_halt_boxes18to24 B hB hOpen
  have hLeaves : ∀ e ∈ roster,
      BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B) e.2 := by
    intro e he
    by_cases h : e.2 = Parent
    · have heq : e.2 = eParent.2 := h.trans hParentEq.symm
      rw [heq]
      exact hParentCover
    · exact hOther e he h
  have hRootCover :
      BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B)
        BB6.CoverageAdapter.firstOneCylinder := by
    refine BB6Coverage.Cover.leaf _ ?_
    intro m hm
    have hmr : BB6Coverage.compatible BB6.Agent50TNFPilot.root m := by
      simpa [BB6.Agent50TNFPilot.root] using hm
    rcases hroot m hmr with hb | ⟨entry, he, e, he0, hc⟩
    · intro k d hk hd
      exact Nat.le_trans (hb k d hk hd) hB
    · have hz := BB6.Agent13BlankDelay.firstOne_terminal _
        BB6.Agent13BlankDelay.firstOneCylinder_root_action m hm
      exact BB6.Agent13BlankDelay.weighted_rename_back B e m he0 hz
        ((hLeaves entry he).sound _ hc)
  exact BB6.Agent13BlankDelay.exact_from_weighted_first_one B (by omega)
    hRootCover champ

#print axioms sameBox_eq
#print axioms rects_in_combined_remainder
#print axioms closed_match_count
#print axioms open_remainder_count
#print axioms raw10_cover_with_cycle_halt_boxes18to24
#print axioms exact_from_raw10_boxes18to24_combined

end BB6.Agent49Box18to24CombinedBridge
