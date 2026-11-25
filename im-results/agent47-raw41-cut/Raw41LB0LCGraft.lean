import Raw41LC0RAGraft
import Raw41LB0LCClosed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

/-- Uniform filtering of a certified quotient family retains all other obligations. -/
theorem filter_sound {xs : List (List Move × PartialMachine)} {B : Nat}
    (p : PartialMachine)
    (hs : ∀ m, compatible root m → WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m)
    (hp : ∀ m, TNFQuotientCompatible p m → WeightedBound B m) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ xs.filter (fun e => !(sameTable e.2 p)), TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases hs m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · cases h : sameTable e.2 p with
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [h]⟩,hq⟩
    | true =>
      have eq : e.2 = p := sameTable_sound h
      exact Or.inl (hp m (eq ▸ hq))

noncomputable def afterLB0LC := afterLC0RA.filter fun e => !(sameTable e.2 Raw41LB0LC_p)

theorem lb0lc_unique : (afterLC0RA.filter fun e => sameTable e.2 Raw41LB0LC_p).length = 1 := by decide +kernel
theorem afterLB0LC_count : afterLB0LC.length = 227 := by decide +kernel

theorem afterLB0LC_sound : ∀ m, compatible root m → WeightedBound 7014 m ∨ ∃ e ∈ afterLB0LC, TNFQuotientCompatible e.2 m :=
  filter_sound _ afterLC0RA_sound (fun m hm k d hk hd => Nat.le_trans (Raw41LB0LC_bound m hm k d hk hd) (by decide))

noncomputable def afterThree := afterLB0LC.filter fun e => !(sameTable e.2 lc0lbParent)

theorem lc0lb_unique_after_two : (afterLB0LC.filter fun e => sameTable e.2 lc0lbParent).length = 1 := by decide +kernel
theorem afterThree_count : afterThree.length = 226 := by decide +kernel

theorem afterThree_sound (hLC0LB : ∀ m, TNFQuotientCompatible lc0lbParent m → WeightedBound 229 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨ ∃ e ∈ afterThree, TNFQuotientCompatible e.2 m :=
  filter_sound _ afterLB0LC_sound (fun m hm k d hk hd => Nat.le_trans (hLC0LB m hm k d hk hd) (by decide))

theorem exact_at_target_after_LB0LC (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ afterLB0LC, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB afterLB0LC_sound hLeaves champ

#print axioms filter_sound
#print axioms lb0lc_unique
#print axioms afterLB0LC_count
#print axioms afterLB0LC_sound
#print axioms lc0lb_unique_after_two
#print axioms afterThree_count
#print axioms afterThree_sound
#print axioms exact_at_target_after_LB0LC
end BB6.Agent47Raw41
