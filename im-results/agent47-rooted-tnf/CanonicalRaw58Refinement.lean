import CanonicalRaw114Accepted

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47CanonicalRaw58
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent8TNFPath
open BB6.Agent31FourHoleRoster BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- The exact canonical raw58 residual, a sibling of p107 and p114. -/
abbrev p58 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,0⟩)
abbrev child (mv : Move) : PartialMachine := refine p58 (0,true) (some mv)

def remaining5 : List Move :=
  [⟨false,false,4⟩, ⟨false,false,5⟩, ⟨false,true,5⟩,
   ⟨true,false,4⟩, ⟨true,false,5⟩]
abbrev rf : Move := ⟨false,true,5⟩
def remaining4 : List Move := remaining5.filter fun mv => decide (mv ≠ rf)
def replacement : List Entry := remaining4.map fun mv => ([mv], child mv)

noncomputable def partialRoster :=
  graftRoster p58 replacement BB6.Agent47CanonicalRaw114Accepted.roster
noncomputable def closedRoster :=
  graftRoster p58 [] BB6.Agent47CanonicalRaw114Accepted.roster

theorem parent_count :
    (BB6.Agent47CanonicalRaw114Accepted.roster.filter fun e => sameTable e.2 p58).length = 1 := by
  decide

theorem replacement_count : replacement.length = 4 := by decide

theorem partial_count : partialRoster.length = 80 := by decide

theorem closed_count : closedRoster.length = 76 := by decide

/-- Consume the accepted local 374-bound partition and 1346-bound RF child
    while retaining every other child. Their source theorems are explicit
    premises so this consumer needs only the canonical77 proof core. -/
theorem partial_sound
    (hcut : ∀ m, compatible p58 m → WeightedBound 374 m ∨
      ∃ mv ∈ remaining5, compatible (child mv) m)
    (hRF : ∀ m, compatible (child rf) m → WeightedBound 1346 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ partialRoster, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := p58) (replacement := replacement)
    (roster := BB6.Agent47CanonicalRaw114Accepted.roster)
    (by decide) BB6.Agent47CanonicalRaw114Accepted.sound
  intro m hm
  rcases hcut m hm with hb | ⟨mv, hr, hc⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases he : mv = rf
    · subst mv
      exact Or.inl (fun k d hk hd => Nat.le_trans (hRF m hc k d hk hd) (by decide))
    · have hr' : mv ∈ remaining4 := List.mem_filter.mpr ⟨hr, by simp [he]⟩
      exact Or.inr ⟨([mv], child mv), List.mem_map.mpr ⟨mv, hr', rfl⟩, hc⟩

/-- The fully closed alternative consumes a complete Raw58 parent bound. -/
theorem closed_sound
    (h58 : ∀ m, compatible p58 m → WeightedBound 7014 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ closedRoster, TNFQuotientCompatible e.2 m :=
  graftRoster_sound (by decide) BB6.Agent47CanonicalRaw114Accepted.sound
    (fun m hm => Or.inl (h58 m hm))

theorem exact_partial_at_target (B : Nat) (hB : 7014 ≤ B)
    (hcut : ∀ m, compatible p58 m → WeightedBound 374 m ∨
      ∃ mv ∈ remaining5, compatible (child mv) m)
    (hRF : ∀ m, compatible (child rf) m → WeightedBound 1346 m)
    (hLeaves : ∀ e ∈ partialRoster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) : BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (partial_sound hcut hRF) hLeaves champ

theorem exact_closed_at_target (B : Nat) (hB : 7014 ≤ B)
    (h58 : ∀ m, compatible p58 m → WeightedBound 7014 m)
    (hLeaves : ∀ e ∈ closedRoster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) : BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (closed_sound h58) hLeaves champ

#print axioms parent_count
#print axioms replacement_count
#print axioms partial_count
#print axioms closed_count
#print axioms partial_sound
#print axioms closed_sound
#print axioms exact_partial_at_target
#print axioms exact_closed_at_target
end BB6.Agent47CanonicalRaw58
