import Raw117Roster
import CanonicalFrontier

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent8Raw117CanonicalCut
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier BB6.Agent8Raw117
open BB6.Agent8Raw117Roster

/-- Ingest the exact-table cut into any source-rooted quotient roster. -/
noncomputable def cut (roster : List (List Move × PartialMachine)) :=
  roster.filter fun e => !(covered e.2)

theorem cut_sound {C : Nat} (hC : 1291 ≤ C)
    {roster : List (List Move × PartialMachine)}
    (hs : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound C m ∨ ∃ e ∈ cut roster, TNFQuotientCompatible e.2 m := by
  rcases hs m hm with hb | ⟨entry, he, hq⟩
  · exact Or.inl hb
  · cases hc : covered entry.2 with
    | true =>
        have heq : entry.2 = p117 :=
          BB6.Agent31ThreeHole.tableOK_sound _ _ hc
        have hf : entry.2 initialSlot = some (some ⟨true,true,1⟩) := by
          rw [heq]
          exact p117_root
        have hb := quotientSafe hf (covered_sound entry.2 hc) m hq
        exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) hC)
    | false =>
        exact Or.inr ⟨entry, List.mem_filter.mpr ⟨he, by simp [hc]⟩, hq⟩

theorem canonical_cut_count : (cut canonicalRemainingRoster).length = 95 := by
  decide

theorem canonical_cut_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 1291 m ∨
      ∃ e ∈ cut canonicalRemainingRoster, TNFQuotientCompatible e.2 m := by
  apply cut_sound (by decide) _ m hm
  intro m' hm'
  rcases canonicalRemaining_sound m' hm' with h | h
  · exact Or.inl (fun k d hk hd => Nat.le_trans (h k d hk hd) (by decide))
  · exact Or.inr h

theorem cover_at_target (B : Nat) (hB : 1291 ≤ B)
    (hLeaves : ∀ e ∈ cut canonicalRemainingRoster, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder :=
  cover_of_quotient_roster hB canonical_cut_sound hLeaves

#print axioms cut_sound
#print axioms canonical_cut_count
#print axioms canonical_cut_sound
#print axioms cover_at_target

end BB6.Agent8Raw117CanonicalCut
