import Raw39Canonical40Conditional

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
General fixed-score quotient transport. The accepted Canonical40 predecessor
is already sound at weighted floor 6766859. It is ALSO sound at any larger
threshold. Therefore a parent can be removed from a fixed-score exactness
proof using Cover at the CHAMPION threshold, not necessarily at 6766859.
This weakens the missing Raw39/1LE hypothesis without assuming its proof.
-/

namespace BB6.Agent11Raw39Canonical40LooseThreshold

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic
open BB6.Agent11Raw39Canonical40Conditional

/-- The accepted Canonical40 source frontier is sound at *every* B above
its original weighted floor, without inspecting or changing any retained
representative. This lemma is independent of Raw39. -/
theorem sound40_at (B : Nat) (hFloor : 6766859 ≤ B) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ BB6.Agent11Raw39Canonical40Conditional.baseRoster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent31Canonical40Extra57.sound_integrated m hm with hsmall | hrest
  · exact Or.inl (fun k d hk hd =>
      Nat.le_trans (hsmall k d hk hd) hFloor)
  · exact Or.inr hrest

/-- Any batch of independently certified parent Covers can be removed at ANY
target B ≥ 6766859; parent bounds need NOT fit the original local cutoff.
This applies to every current Canonical40 target, not only Raw39. -/
theorem remove_many_at (B : Nat) (hFloor : 6766859 ≤ B)
    {parents : List PartialMachine}
    (hRoots : ∀ p ∈ parents,
      p initialSlot = some (some ⟨true,true,1⟩))
    (hParents : ∀ p ∈ parents, Cover (WeightedBound B) p) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ removeParents parents BB6.Agent11Raw39Canonical40Conditional.baseRoster,
          TNFQuotientCompatible e.2 m :=
  removeParents_sound (sound40_at B hFloor) hRoots hParents

theorem parents_cover_at (B : Nat)
    (hp : Cover (WeightedBound B) p39) :
    ∀ p ∈ removedParents, Cover (WeightedBound B) p := by
  intro p hmem
  have he : p = p39 := by simpa [removedParents] using hmem
  subst p
  exact hp

/-- The existing 6,766,859 soundness cut can be widened to any larger B. -/
theorem sound_at (B : Nat) (hFloor : 6766859 ≤ B)
    (hp : Cover (WeightedBound B) p39) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster39, TNFQuotientCompatible e.2 m := by
  exact remove_many_at B hFloor parents_root (parents_cover_at B hp)

/-- Discharging a single parent at the target global score suffices; the
older local 6,766,859 floor is not mathematically necessary. -/
theorem exact_at_target (B : Nat) (hFloor : 6766859 ≤ B)
    (hSix : 6 ≤ B)
    (hp : Cover (WeightedBound B) p39)
    (hLeaves : ∀ e ∈ roster39, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
       BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster hSix (Nat.le_refl B)
    (sound_at B hFloor hp) hLeaves champ

theorem exact_at_champion
    (hp : Cover (WeightedBound (proposedTM63Moves + 7)) p39)
    (hLeaves : ∀ e ∈ roster39,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (by omega) hp hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms sound40_at
#print axioms remove_many_at
#print axioms parents_cover_at
#print axioms sound_at
#print axioms exact_at_target
#print axioms exact_at_champion

end BB6.Agent11Raw39Canonical40LooseThreshold
