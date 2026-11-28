import Raw39Canonical39Successor

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Exact cumulative successor skeleton for Raw47 on the accepted Raw39 Canonical39
lineage.  This theorem deliberately takes the Raw47 Cover as an explicit
premise: it settles the roster/membership side of the 39 -> 38 decrement
without claiming that the independently accepted Raw47 proof object has yet
been transported into this source environment.
-/

namespace BB6.Agent3Raw47Canonical39Conditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

def p47 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨false, true, 2⟩)
  | _, _ => none

noncomputable abbrev baseRoster :=
  BB6.Agent11Raw39Canonical39Successor.roster39
abbrev removedParents : List PartialMachine := [p47]

theorem parent_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p47)).length = 1 := by decide

theorem parent_root :
    p47 initialSlot = some (some ⟨true, true, 1⟩) := by decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  have he : p = p47 := by simpa [removedParents] using hp
  subst p
  exact parent_root

theorem parents_cover (hp : Cover (WeightedBound 6766859) p47) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hmem
  have he : p = p47 := by simpa [removedParents] using hmem
  subst p
  exact hp

noncomputable def roster38 := removeParents removedParents baseRoster

theorem count38 : roster38.length = 38 := by decide

theorem raw47_removed :
    (roster38.filter (fun e => sameTable e.2 p47)).length = 0 := by decide

theorem conditional_sound (hp : Cover (WeightedBound 6766859) p47) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m :=
by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent11Raw39Canonical39Successor.sound_integrated
    parents_root (parents_cover hp)

theorem conditional_exact_at_champion
    (hp : Cover (WeightedBound 6766859) p47)
    (hLeaves : ∀ e ∈ roster38,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound hp) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parent_count39
#print axioms count38
#print axioms raw47_removed
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent3Raw47Canonical39Conditional
