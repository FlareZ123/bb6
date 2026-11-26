import Canonical64Raw139NormalizedCrosswalk
import Raw139E0ZeroRBCover
import Raw139E0ZeroRDCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Canonical64Raw139E0ParentCrosswalk

open BB6Coverage
open BB6ChampionArithmetic
open BB6.Agent6Raw139Normalized
open BB6.Agent31FourHoleRoster
open BB6.Agent3Canonical64Raw120
open BB6.Agent6ChampionResidual
open BB6.Agent38ChampionThreshold
open BB6.Agent14Canonical64Raw139Crosswalk
open BB6.Agent48Raw139E0ZeroRB
open BB6.Agent48Raw139E0ZeroRD

/-- The normalized E0=0RB table is exactly the parent certified by Agent48. -/
theorem e0RBTable_eq_certifiedParent :
    e0RBTable = BB6.Agent48Raw139E0ZeroRB.parent := by
  exact sameTable_sound (by decide)

/-- The source-accepted E0=0RB Cover at its candidate bound. -/
theorem e0RB_cover_at_1217 :
    Cover (WeightedBound 1217) e0RBTable := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  have hm' : compatible BB6.Agent48Raw139E0ZeroRB.parent m := by
    simpa [e0RBTable_eq_certifiedParent] using hm
  exact BB6.Agent48Raw139E0ZeroRB.all_completions_weighted m hm' k d hk hd

/-- Lift E0=0RB to every larger weighted bound. -/
theorem e0RB_cover_at_bound {B : Nat} (hB : 1217 ≤ B) :
    Cover (WeightedBound B) e0RBTable := by
  cases e0RB_cover_at_1217 with
  | leaf _ hbound =>
      refine Cover.leaf _ ?_
      intro m hm k d hk hd
      exact Nat.le_trans (hbound m hm k d hk hd) hB

/-- The normalized E0=0RD table is exactly the parent certified by Agent48. -/
theorem e0RDTable_eq_certifiedParent :
    e0RDTable = BB6.Agent48Raw139E0ZeroRD.parent := by
  exact sameTable_sound (by decide)

/-- The source-accepted E0=0RD Cover at its candidate bound. -/
theorem e0RD_cover_at_806 :
    Cover (WeightedBound 806) e0RDTable := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  have hm' : compatible BB6.Agent48Raw139E0ZeroRD.parent m := by
    simpa [e0RDTable_eq_certifiedParent] using hm
  exact BB6.Agent48Raw139E0ZeroRD.all_completions_weighted m hm' k d hk hd

/-- Lift E0=0RD to every larger weighted bound. -/
theorem e0RD_cover_at_bound {B : Nat} (hB : 806 ≤ B) :
    Cover (WeightedBound B) e0RDTable := by
  cases e0RD_cover_at_806 with
  | leaf _ hbound =>
      refine Cover.leaf _ ?_
      intro m hm k d hk hd
      exact Nat.le_trans (hbound m hm k d hk hd) hB

/-- Supply the accepted E0=0RE, E0=0RB and E0=0RD parent Covers for their
    unique normalized rows, leaving only 63 normalized residual Covers. -/
theorem normalizedTables_cover_with_E0RE0RB0RD {B : Nat}
    (hB : 1217 ≤ B)
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0RE0RB0RD,
      Cover (WeightedBound B) p) :
    ∀ p ∈ normalizedTables, Cover (WeightedBound B) p := by
  intro p hp
  by_cases heRE : sameTable p e0RETable = true
  · have hpEq : p = e0RETable := sameTable_sound heRE
    rw [hpEq]
    exact e0RE_cover_at_bound (Nat.le_trans (by decide : 852 ≤ 1217) hB)
  · by_cases heRB : sameTable p e0RBTable = true
    · have hpEq : p = e0RBTable := sameTable_sound heRB
      rw [hpEq]
      exact e0RB_cover_at_bound hB
    · by_cases heRD : sameTable p e0RDTable = true
      · have hpEq : p = e0RDTable := sameTable_sound heRD
        rw [hpEq]
        exact e0RD_cover_at_bound (Nat.le_trans (by decide : 806 ≤ 1217) hB)
      · exact hNorm p (List.mem_filter.mpr
          ⟨hp, by simp [normalizedTablesWithoutE0RE0RB0RD, heRE, heRB, heRD]⟩)

/-- Canonical64 exactness with three source-accepted E0 parent Covers:
    63 other Canonical64 Covers, 63 remaining normalized Raw139 Covers,
    and only the explicit active complement outside the normalized crosswalk. -/
theorem exact_at_target_with_63_normalized_and_complement
    (hOther : ∀ e ∈ roster64,
      e.2 ≠ championResidual →
        Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0RE0RB0RD,
      Cover (WeightedBound (proposedTM63Moves + 7)) p)
    (hRest : ∀ e ∈ activeUncoveredByNormalized,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    ExactBB6 (proposedTM63Moves + 7) := by
  have hB : 1217 ≤ proposedTM63Moves + 7 := by
    have hScore := champion_score_ge_6766859
    omega
  exact exact_at_target_with_normalized_and_complement hOther
    (normalizedTables_cover_with_E0RE0RB0RD hB hNorm) hRest

#print axioms e0RBTable_eq_certifiedParent
#print axioms e0RB_cover_at_1217
#print axioms e0RB_cover_at_bound
#print axioms e0RDTable_eq_certifiedParent
#print axioms e0RD_cover_at_806
#print axioms e0RD_cover_at_bound
#print axioms normalizedTables_cover_with_E0RE0RB0RD
#print axioms exact_at_target_with_63_normalized_and_complement

end BB6.Agent14Canonical64Raw139E0ParentCrosswalk
