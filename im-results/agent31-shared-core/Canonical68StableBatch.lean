import CanonicalTwoParentRosterOnly
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31StableParentBatch
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- Delete precisely the entries matching one of the supplied physical tables.
This combinator requires no parent-specific proof modules. -/
def removeParents (parents : List PartialMachine) (roster : List Entry) : List Entry :=
  roster.filter (fun e => !(parents.any (fun p => sameTable e.2 p)))

/-- Consume independently certified parent cylinders in one quotient-preserving
operation. All entries not matching a selected parent are retained. -/
theorem removeParents_sound {B : Nat} {root : PartialMachine}
    {parents : List PartialMachine} {roster : List Entry}
    (hroot : ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (hstart : ∀ p ∈ parents, p initialSlot = some (some ⟨true,true,1⟩))
    (hparents : ∀ p ∈ parents, Cover (WeightedBound B) p) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ removeParents parents roster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases hroot m hm with hb | ⟨e,he,perm,hfix,hcomp⟩
  · exact Or.inl hb
  · by_cases hmatch : parents.any (fun p => sameTable e.2 p) = true
    · obtain ⟨p,hp,ht⟩ := List.any_eq_true.mp hmatch
      have hc : compatible p (renameTable perm m) := sameTable_sound ht ▸ hcomp
      have hz := firstOne_terminal p (hstart p hp) _ hc
      exact Or.inl (weighted_rename_back B perm m hfix
        ((zeroNext_none_rename_iff perm m hfix).mp hz) ((hparents p hp).sound _ hc))
    · exact Or.inr ⟨e, List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,
        perm,hfix,hcomp⟩

/-- An existing local proof can be weakened to any larger score bound. -/
theorem liftCover {B C : Nat} {p : PartialMachine}
    (hCB : C ≤ B) (h : Cover (WeightedBound C) p) : Cover (WeightedBound B) p :=
  Cover.leaf p (fun m hm k d hk hd => Nat.le_trans (h.sound m hm k d hk hd) hCB)

/-- All eight tables are derived from the stable path, not imported from the
generated proof data of any of the parents. -/
abbrev e1Base : PartialMachine := (pathEnd root 2 (path.take 4)).1
abbrev p60 : PartialMachine := refine e1Base (4,true) (some ⟨true,true,0⟩)
abbrev p109 : PartialMachine := refine e1Base (4,true) (some ⟨true,true,1⟩)
abbrev p110 : PartialMachine := refine e1Base (4,true) (some ⟨false,false,2⟩)
abbrev p111 : PartialMachine := refine e1Base (4,true) (some ⟨false,true,2⟩)
abbrev p117 : PartialMachine := refine e1Base (4,true) (some ⟨true,true,3⟩)
abbrev p121 : PartialMachine := refine e1Base (4,true) (some ⟨true,true,4⟩)
abbrev p123 : PartialMachine := refine e1Base (4,true) (some ⟨false,true,5⟩)
abbrev p125 : PartialMachine := refine e1Base (4,true) (some ⟨true,true,5⟩)
def parents : List PartialMachine := [p60,p109,p110,p111,p117,p121,p123,p125]
noncomputable def baseRoster := BB6.Agent47CanonicalTwoParent.roster76
noncomputable def roster68 := removeParents parents baseRoster

theorem parent_roots : ∀ p ∈ parents, p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [parents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem count68 : roster68.length = 68 := by decide

theorem sound68 {B : Nat} (hB : 7014 ≤ B)
    (hParents : ∀ p ∈ parents, Cover (WeightedBound B) p) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ roster68, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := parents) (roster := baseRoster) ?_ parent_roots hParents
  intro m hm
  rcases BB6.Agent31CanonicalTwoParentRosterOnly.roster76_sound m hm with hb | hr
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) hB)
  · exact Or.inr hr

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hParents : ∀ p ∈ parents, Cover (WeightedBound B) p)
    (hLeaves : ∀ e ∈ roster68, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) (Nat.le_refl B)
    (sound68 hB hParents) hLeaves champ

#print axioms removeParents_sound
#print axioms liftCover
#print axioms parent_roots
#print axioms count68
#print axioms sound68
#print axioms exact_at_target
end BB6.Agent31StableParentBatch
