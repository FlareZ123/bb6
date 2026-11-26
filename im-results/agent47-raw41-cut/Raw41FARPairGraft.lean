import Raw41CanonicalCut
import Raw41LB1RBClosed
import Raw41RB0RCClosed

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

def removeFARPair (xs : List (List Move × PartialMachine)) :=
  xs.filter fun e => !(sameTable e.2 Raw41LB1RB_p || sameTable e.2 Raw41RB0RC_p)

theorem removeFARPair_sound (B : Nat) (hB : 173 ≤ B) (m : Machine)
    (xs : List (List Move × PartialMachine))
    (h : WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ removeFARPair xs, TNFQuotientCompatible e.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h1 : sameTable e.2 Raw41LB1RB_p = true
    · exact Or.inl (fun k d hk hd => Nat.le_trans (Raw41LB1RB_bound m ((sameTable_sound h1) ▸ hq) k d hk hd) (by omega))
    · by_cases h2 : sameTable e.2 Raw41RB0RC_p = true
      · exact Or.inl (fun k d hk hd => Nat.le_trans (Raw41RB0RC_bound m ((sameTable_sound h2) ▸ hq) k d hk hd) hB)
      · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [h1,h2]⟩,hq⟩

def localFARPair := removeFARPair canonicalRemaining

theorem lb1rb_unique : (canonicalRemaining.filter fun e => sameTable e.2 Raw41LB1RB_p).length = 1 := by decide +kernel
theorem rb0rc_unique : (canonicalRemaining.filter fun e => sameTable e.2 Raw41RB0RC_p).length = 1 := by decide +kernel
theorem localFARPair_count : localFARPair.length = 151 := by decide +kernel
theorem localFARPair_sound : ∀ m, TNFQuotientCompatible parent m → WeightedBound 173 m ∨ ∃ e ∈ localFARPair, TNFQuotientCompatible e.2 m := by
  intro m hm
  apply removeFARPair_sound 173 (by decide)
  rcases canonical_sound m hm with hb | h
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr h

noncomputable def globalFARPair := removeFARPair roster
theorem globalFARPair_count : globalFARPair.length = 227 := by decide +kernel
theorem globalFARPair_sound : ∀ m, compatible root m → WeightedBound 7014 m ∨ ∃ e ∈ globalFARPair, TNFQuotientCompatible e.2 m := by
  intro m hm
  exact removeFARPair_sound 7014 (by decide) m roster (roster_sound m hm)

theorem exact_at_target_farPair (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ globalFARPair, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB globalFARPair_sound hLeaves champ

#print axioms removeFARPair_sound
#print axioms lb1rb_unique
#print axioms rb0rc_unique
#print axioms localFARPair_count
#print axioms localFARPair_sound
#print axioms globalFARPair_count
#print axioms globalFARPair_sound
#print axioms exact_at_target_farPair
end BB6.Agent47Raw41
