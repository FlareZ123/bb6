import Raw39Canonical40LooseThreshold

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
A *direct, two-parent* Canonical40→38 conditional quotient that does not
require either independent Canonical39 branch to be consumed first.

The existing accepted polymorphic "remove_many_at" theorem transports the
Canonical40 soundness bound to any B ≥ 6766859. Two literal, distinct
Canonical40 representatives (Raw39 and Raw47) are then deleted together,
conditional only on their respective target-score Covers.

Both local whole-parent Covers have independently been source accepted,
but their separate proof-object families are NOT imported here. Hence this
module is a source-level target for an eventual original-source two-parent
global kernel link, not a claim of a completed BB(6) upper bound.
-/

namespace BB6.Agent11Raw39Raw47Batch38

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p39 : PartialMachine := BB6.Agent11Raw39Canonical40Membership.p
abbrev p47 : PartialMachine := BB6.Agent11Raw39Canonical40Membership.p47
noncomputable abbrev baseRoster := BB6.Agent11Raw39Canonical40Conditional.baseRoster
abbrev removedParents : List PartialMachine := [p39,p47]
noncomputable def roster38 := removeParents removedParents baseRoster

theorem parents_distinct : sameTable p39 p47 = false :=
  BB6.Agent11Raw39Canonical40Membership.distinct_from_raw47

theorem parent39_present :
    (baseRoster.filter (fun e => sameTable e.2 p39)).length = 1 :=
  BB6.Agent11Raw39Canonical40Membership.parent_present

theorem parent47_present :
    (baseRoster.filter (fun e => sameTable e.2 p47)).length = 1 := by decide

theorem parent_roots :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · decide
  · decide

theorem parent_covers (B : Nat)
    (h39 : Cover (WeightedBound B) p39)
    (h47 : Cover (WeightedBound B) p47) :
    ∀ p ∈ removedParents, Cover (WeightedBound B) p := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact h39
  · exact h47

theorem count38 : roster38.length = 38 := by decide

theorem raw39_removed :
    (roster38.filter (fun e => sameTable e.2 p39)).length = 0 := by decide

theorem raw47_removed :
    (roster38.filter (fun e => sameTable e.2 p47)).length = 0 := by decide

/-- Exactly the two named parent Covers are required to pass from the
accepted 40-roster quotient to 38 survivors at ANY final target score above
the established Canonical40 floor. -/
theorem sound38_at (B : Nat) (hFloor : 6766859 ≤ B)
    (h39 : Cover (WeightedBound B) p39)
    (h47 : Cover (WeightedBound B) p47) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m := by
  exact BB6.Agent11Raw39Canonical40LooseThreshold.remove_many_at
    B hFloor parent_roots (parent_covers B h39 h47)

/-- The remaining 38 Covers, plus the independent locally proved
Raw39/Raw47 parent Covers, imply exactness at the published champion score.
This is deliberately conditional, not a proof of all 38 remaining Covers. -/
theorem exact38_at_champion
    (h39 : Cover (WeightedBound (proposedTM63Moves + 7)) p39)
    (h47 : Cover (WeightedBound (proposedTM63Moves + 7)) p47)
    (hLeaves : ∀ e ∈ roster38,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega) (Nat.le_refl _)
    (sound38_at (proposedTM63Moves + 7)
      BB6.Agent38ChampionThreshold.champion_score_ge_6766859 h39 h47)
    hLeaves BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parents_distinct
#print axioms parent39_present
#print axioms parent47_present
#print axioms parent_roots
#print axioms count38
#print axioms raw39_removed
#print axioms raw47_removed
#print axioms sound38_at
#print axioms exact38_at_champion

end BB6.Agent11Raw39Raw47Batch38
