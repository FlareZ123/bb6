import Canonical64Raw120Integrated
import Raw57ParentBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw57Canonical64

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31StableParentBatch
open BB6.Agent47CanonicalFrontier

/-- The exact six-hole Raw57 parent (E1=0LA) that remains after the
    fourteen already-covered A1 choices and five immediate cycles. -/
abbrev raw57 : PartialMachine := BB6.Agent1Raw57Parent.parent

/-- Remove this exact parent from the source-accepted Canonical64 roster.
    The count theorem below is the critical crosswalk check. -/
noncomputable def roster63 :=
  removeParents [raw57] BB6.Agent3Canonical64Raw120.roster64

theorem raw57_root :
    raw57 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

/-- Raw57 is expected to be exactly one of the 64 retained representatives.
    This is a finite exact-table check, not a string/name match. -/
theorem raw57_member_count :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 raw57)).length = 1 := by
  decide

theorem roster63_count : roster63.length = 63 := by
  decide

/-- Conditional 64-to-63 graft. The only new mathematical premise is the
    source-accepted Cover of the exact Raw57 parent; all other roster
    representatives are retained unchanged. -/
theorem sound63 (B : Nat) (hB : 6766859 ≤ B)
    (h57 : Cover (WeightedBound B) raw57) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster63, TNFQuotientCompatible e.2 m := by
  have hroot : ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ BB6.Agent3Canonical64Raw120.roster64,
          TNFQuotientCompatible e.2 m := by
    intro m hm
    rcases BB6.Agent3Canonical64Raw120.sound64_integrated m hm with hb | hr
    · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) hB)
    · exact Or.inr hr
  have hstart : ∀ p ∈ [raw57],
      p initialSlot = some (some ⟨true,true,1⟩) := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact raw57_root
  have hparents : ∀ p ∈ [raw57],
      Cover (WeightedBound B) p := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact h57
  exact removeParents_sound (B := B) (root := root)
    (parents := [raw57])
    (roster := BB6.Agent3Canonical64Raw120.roster64)
    hroot hstart hparents

/-- If the Raw57 parent and the 63 retained representatives all have
    target-B Covers, the existing attained-score witness gives ExactBB6 B. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (h57 : Cover (WeightedBound B) raw57)
    (hLeaves : ∀ e ∈ roster63, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) (Nat.le_refl B)
    (sound63 B hB h57) hLeaves champ

#print axioms raw57_root
#print axioms raw57_member_count
#print axioms roster63_count
#print axioms sound63
#print axioms exact_at_target

end BB6.Agent1Raw57Canonical64
