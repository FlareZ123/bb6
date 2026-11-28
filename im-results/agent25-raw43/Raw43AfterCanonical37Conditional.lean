import Raw47AfterRaw112Integrated

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Conditional Raw43 successor of the source-accepted Raw112-first / Raw47
Canonical37 lineage.  Raw43's complete seven-hole parent Cover is deliberately
an explicit premise: this module proves the exact current-roster geometry and
the 37 -> 36 quotient step without pretending the still-running parent assembly
is already accepted.
-/

namespace BB6.Agent25Raw43AfterCanonical37Conditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

/-- Raw43 parent: 1RB---_1RC---_0RD---_1LD0RB_------_------. -/
def p43 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,true,1⟩)
  | _,_ => none

noncomputable abbrev baseRoster :=
  BB6.Agent17Raw47AfterRaw112Integrated.roster37
abbrev removedParents : List PartialMachine := [p43]

theorem parent_count37 :
    (baseRoster.filter (fun e => sameTable e.2 p43)).length = 1 := by decide

theorem parent_root :
    p43 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p43 := by simpa [removedParents] using hp
  subst p
  exact parent_root

theorem parents_cover
    (h : Cover (WeightedBound 6766859) p43) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p43 := by simpa [removedParents] using hp
  subst p
  exact h

noncomputable def roster36 := removeParents removedParents baseRoster

theorem count36 : roster36.length = 36 := by decide

theorem removed_parent_absent :
    (roster36.filter (fun e => sameTable e.2 p43)).length = 0 := by decide

theorem conditional_sound
    (hp : Cover (WeightedBound 6766859) p43) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent17Raw47AfterRaw112Integrated.sound_integrated
    parents_root (parents_cover hp)

theorem conditional_exact_at_champion
    (hp : Cover (WeightedBound 6766859) p43)
    (hLeaves : ∀ e ∈ roster36,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound hp) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parent_count37
#print axioms count36
#print axioms removed_parent_absent
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent25Raw43AfterCanonical37Conditional
