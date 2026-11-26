import Canonical64Raw120Integrated
import Raw139NormalizedAcceptedCovers
import Raw139NormalizedE0ParentRows
import Raw139E0ZeroRAIntegrated
import Raw139E0ZeroRECover
import Raw139E0ZeroRBCover
import Raw139E0ZeroRDCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Canonical64Raw139NormalizedDirect

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6ChampionArithmetic
open BB6.Agent6Raw139Normalized
open BB6.Agent3Raw139E0ZeroRAIntegrated
open BB6.Agent14Raw139NormalizedE0ParentRows
open BB6.Agent14Raw139NormalizedAccepted
open BB6.Agent31FourHoleRoster
open BB6.Agent31FourHoleFrontier
open BB6.Agent3Canonical64Raw120
open BB6.Agent6ChampionResidual
open BB6.Agent38ChampionThreshold

/-- Monotonicity of the weighted completion bound. -/
theorem cover_mono {A B : Nat} (hAB : A ≤ B) {p : PartialMachine}
    (h : Cover (WeightedBound A) p) : Cover (WeightedBound B) p := by
  cases h with
  | leaf _ hbound =>
      refine Cover.leaf _ ?_
      intro m hm k d hk hd
      exact Nat.le_trans (hbound m hm k d hk hd) hAB

/-- The E0=0RA row is already source-accepted at 321,796. -/
theorem e0RA_cover_at_champion :
    Cover (WeightedBound championScore) (leaf dischargedRow) := by
  have hScore : 321796 ≤ championScore := by
    have h := champion_score_ge_6766859
    omega
  exact cover_mono hScore discharged_cover

/-- Exact table identity for the accepted E0=0RE parent. -/
theorem e0RETable_eq_certifiedParent :
    e0RETable = BB6.Agent48Raw139E0ZeroRE.parent := by
  exact sameTable_sound (by decide)

/-- Exact table identity for the source-accepted E0=0RB parent. -/
theorem e0RBTable_eq_certifiedParent :
    e0RBTable = BB6.Agent48Raw139E0ZeroRB.parent := by
  exact sameTable_sound (by decide)

/-- Exact table identity for the E0=0RD parent under source audit. -/
theorem e0RDTable_eq_certifiedParent :
    e0RDTable = BB6.Agent48Raw139E0ZeroRD.parent := by
  exact sameTable_sound (by decide)

/-- Lift the source-accepted E0=0RE Cover to the champion score. -/
theorem e0RE_cover_at_champion :
    Cover (WeightedBound championScore) e0RETable := by
  have hSmall : Cover (WeightedBound 852) e0RETable := by
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    have hm' : compatible BB6.Agent48Raw139E0ZeroRE.parent m := by
      simpa [e0RETable_eq_certifiedParent] using hm
    exact BB6.Agent48Raw139E0ZeroRE.all_completions_weighted m hm' k d hk hd
  have hScore : 852 ≤ championScore := by
    have h := champion_score_ge_6766859
    omega
  exact cover_mono hScore hSmall

/-- Lift the E0=0RB Cover to the champion score. -/
theorem e0RB_cover_at_champion :
    Cover (WeightedBound championScore) e0RBTable := by
  have hSmall : Cover (WeightedBound 1217) e0RBTable := by
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    have hm' : compatible BB6.Agent48Raw139E0ZeroRB.parent m := by
      simpa [e0RBTable_eq_certifiedParent] using hm
    exact BB6.Agent48Raw139E0ZeroRB.all_completions_weighted m hm' k d hk hd
  have hScore : 1217 ≤ championScore := by
    have h := champion_score_ge_6766859
    omega
  exact cover_mono hScore hSmall

/-- Lift the E0=0RD Cover to the champion score. -/
theorem e0RD_cover_at_champion :
    Cover (WeightedBound championScore) e0RDTable := by
  have hSmall : Cover (WeightedBound 806) e0RDTable := by
    refine Cover.leaf _ ?_
    intro m hm k d hk hd
    have hm' : compatible BB6.Agent48Raw139E0ZeroRD.parent m := by
      simpa [e0RDTable_eq_certifiedParent] using hm
    exact BB6.Agent48Raw139E0ZeroRD.all_completions_weighted m hm' k d hk hd
  have hScore : 806 ≤ championScore := by
    have h := champion_score_ge_6766859
    omega
  exact cover_mono hScore hSmall

/-- Supply the E0=0RE and E0=0RB Covers and, once accepted, E0=0RD for their unique
    normalized rows, leaving exactly the 63 rows in the finite membership proof. -/
theorem normalizedTables_cover_from_63
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0RE0RB0RD,
      Cover (WeightedBound championScore) p) :
    ∀ p ∈ normalizedTables, Cover (WeightedBound championScore) p := by
  intro p hp
  by_cases hRE : sameTable p e0RETable = true
  · have hpEq : p = e0RETable := sameTable_sound hRE
    rw [hpEq]
    exact e0RE_cover_at_champion
  · by_cases hRB : sameTable p e0RBTable = true
    · have hpEq : p = e0RBTable := sameTable_sound hRB
      rw [hpEq]
      exact e0RB_cover_at_champion
    · by_cases hRD : sameTable p e0RDTable = true
      · have hpEq : p = e0RDTable := sameTable_sound hRD
        rw [hpEq]
        exact e0RD_cover_at_champion
      · exact hNorm p (List.mem_filter.mpr
          ⟨hp, by simp [normalizedTablesWithoutE0RE0RB0RD, hRE, hRB, hRD]⟩)

/-- Reinsert the already accepted E0=0RA Cover, obtaining Covers for all 67
    original normalized residual tables from the 63 remaining hypotheses. -/
theorem remainingTables_cover_from_63
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0RE0RB0RD,
      Cover (WeightedBound championScore) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound championScore) p := by
  intro p hp
  change p ∈ remainingRows.map leaf at hp
  rcases List.mem_map.mp hp with ⟨r, hr, rfl⟩
  by_cases hRA : r = dischargedRow
  · subst r
    exact e0RA_cover_at_champion
  · have hpAfter : leaf r ∈ normalizedTables := by
      apply List.mem_map.mpr
      exact ⟨r, List.mem_filter.mpr ⟨hr, by simp [dischargedRow, hRA]⟩, rfl⟩
    exact normalizedTables_cover_from_63 hNorm (leaf r) hpAfter

/-- The normalized Raw139 parent is now reduced to exactly 63 residual-table
    Covers: all 43 accepted siblings, rowRC/rowRE continuations, p7, and the
    four E0 parent Covers have been consumed. -/
theorem raw139_championResidual_cover_from_63
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0RE0RB0RD,
      Cover (WeightedBound championScore) p) :
    Cover (WeightedBound championScore) championResidual := by
  have hp0 : Cover (WeightedBound championScore) p0 :=
    BB6.Agent14Raw139NormalizedAccepted.raw139_cover_after_accepted
      (remainingTables_cover_from_63 hNorm)
  have hEq : p0 = championResidual :=
    sameTable_sound
      BB6.Agent14Raw139NormalizedAccepted.p0_eq_championResidual
  rw [hEq] at hp0
  exact hp0

/-- Direct Canonical64 exactness interface: only the other 63 roster Covers
    and the 63 remaining normalized Raw139 Covers are left as hypotheses.
    Unlike the active-list crosswalk, this route needs no separate active
    complement because the normalized p0 theorem consumes its full frontier. -/
theorem exact_at_target_with_63_normalized
    (hOther : ∀ e ∈ roster64,
      e.2 ≠ championResidual →
        Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0RE0RB0RD,
      Cover (WeightedBound championScore) p) :
    ExactBB6 (proposedTM63Moves + 7) := by
  have hRaw : Cover (WeightedBound (proposedTM63Moves + 7)) championResidual := by
    simpa [championScore] using raw139_championResidual_cover_from_63 hNorm
  exact BB6.Agent3Canonical64Raw120.exact_at_target
    (proposedTM63Moves + 7)
    champion_score_ge_6766859
    (fun e he => by
      by_cases hs : sameTable e.2 championResidual = true
      · have hEq : e.2 = championResidual := sameTable_sound hs
        rw [hEq]
        exact hRaw
      · have hne : e.2 ≠ championResidual := by
          intro hEq
          have hself : sameTable championResidual championResidual = true := by decide
          exact hs (by simpa [hEq] using hself)
        exact hOther e he hne)
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms e0RA_cover_at_champion
#print axioms e0RETable_eq_certifiedParent
#print axioms e0RBTable_eq_certifiedParent
#print axioms e0RDTable_eq_certifiedParent
#print axioms e0RE_cover_at_champion
#print axioms e0RB_cover_at_champion
#print axioms e0RD_cover_at_champion
#print axioms normalizedTables_cover_from_63
#print axioms remainingTables_cover_from_63
#print axioms raw139_championResidual_cover_from_63
#print axioms exact_at_target_with_63_normalized

end BB6.Agent14Canonical64Raw139NormalizedDirect
