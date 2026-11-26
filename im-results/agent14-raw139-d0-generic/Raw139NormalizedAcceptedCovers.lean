import Raw139Normalized
import ChampionResidualSourceSiblingIntegrationExtended

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedAccepted

open BB6Coverage
open BB6.Agent6Raw139Normalized
open BB6.Agent31FourHoleRoster
open BB6.Agent31FourHoleFrontier
open BB6.Agent6F0.Integration

/-- Exact source-parent membership for the 43 already proved sibling cylinders:
    13 D0/F1 source siblings, the 12-parent C1 batch, 11 F0 siblings, the
    remaining D0=0RF sibling, and six further F1 source siblings. -/
def acceptedCoverHit (p : PartialMachine) : Bool :=
  BB6.Agent6ChampionRaw139SiblingExtended.isAdditionalSourceAcceptedSibling p ||
  BB6.Agent48Raw139C1Batch.parents.any
    (fun q => BB6.Agent31FourHoleRoster.sameTable p q) ||
  BB6.Agent41F0Extended.closedF0 p ||
  BB6.Agent41F0Extended.parentZeroRA p ||
  BB6.Agent31FourHoleRoster.sameTable p BB6.Agent14Raw139D0ZeroRF.parent ||
  BB6.Agent31FourHoleRoster.sameTable p BB6.Agent41F1ZeroLF.parent ||
  BB6.Agent31FourHoleRoster.sameTable p BB6.Agent41F1ZeroRC.parent ||
  BB6.Agent31FourHoleRoster.sameTable p BB6.Agent48F1ZeroRF.parent ||
  BB6.Agent31FourHoleRoster.sameTable p BB6.Agent48F1ZeroRD.ctr ||
  BB6.Agent31FourHoleRoster.sameTable p BB6.Agent48F1OneLA.parent ||
  BB6.Agent31FourHoleRoster.sameTable p BB6.Agent48F1OneLF.parent

/-- A finite exact-table audit: every one of the 43 normalized accepted addresses
    matches at least one of the existing source-parent families above. -/
#eval acceptedRows.filter (fun r => !acceptedCoverHit (child r.1 r.2))

theorem acceptedRowsCovered :
    ∀ r ∈ acceptedRows, acceptedCoverHit (child r.1 r.2) = true := by
  decide

theorem acceptedRowCover (r : Fin 7 × Move) (hr : r ∈ acceptedRows) :
    Cover (WeightedBound championScore) (child r.1 r.2) := by
  have h := acceptedRowsCovered r hr
  simp [acceptedCoverHit] at h
  rcases h with hSource | hC1 | hF0 | hZeroRA | hD0ZeroRF |
      hF1ZeroLF | hF1ZeroRC | hF1ZeroRF | hF1ZeroRD | hF1OneLA | hF1OneLF
  · simpa [championScore] using
      (BB6.Agent6ChampionRaw139SiblingExtended.additionalSourceAcceptedSiblingCover
        (child r.1 r.2) hSource)
  · rcases List.any_eq_true.mp hC1 with ⟨p, hp, hSame⟩
    have hEq : child r.1 r.2 = p := sameTable_sound hSame
    rw [hEq]
    exact BB6.Agent48Raw139C1Batch.cover_at championScore (by omega) p hp
  · exact BB6.Agent41F0Extended.cover_closed championScore
      champion_score_ge_49394 _ hF0
  · have hEq : child r.1 r.2 = BB6.Agent6F0.parent ⟨false, true, 0⟩ :=
      sameTable_sound hZeroRA
    rw [hEq]
    exact BB6.Agent48RA.cover_zeroRA championScore (by omega)
  · have hEq : child r.1 r.2 = BB6.Agent14Raw139D0ZeroRF.parent :=
      sameTable_sound hD0ZeroRF
    rw [hEq]
    exact BB6.Agent6ChampionRaw139SiblingExtended.cover_zeroRF
  · have hEq : child r.1 r.2 = BB6.Agent41F1ZeroLF.parent :=
      sameTable_sound hF1ZeroLF
    rw [hEq]
    exact BB6.Agent48F1ZeroLFIntegration.cover_zeroLF championScore (by omega)
  · have hEq : child r.1 r.2 = BB6.Agent41F1ZeroRC.parent :=
      sameTable_sound hF1ZeroRC
    rw [hEq]
    exact BB6.Agent6F1ZeroRCIntegration.cover_zeroRC championScore (by omega)
  · have hEq : child r.1 r.2 = BB6.Agent48F1ZeroRF.parent :=
      sameTable_sound hF1ZeroRF
    rw [hEq]
    exact BB6.Agent48F1RFIntegration.cover_zeroRF championScore (by omega)
  · have hEq : child r.1 r.2 = BB6.Agent48F1ZeroRD.ctr :=
      sameTable_sound hF1ZeroRD
    rw [hEq]
    exact BB6.Agent48F1Integration.cover_zeroRD championScore
  · have hEq : child r.1 r.2 = BB6.Agent48F1OneLA.parent :=
      sameTable_sound hF1OneLA
    rw [hEq]
    exact BB6.Agent6F1OneLAIntegration.cover_oneLA championScore (by omega)
  · have hEq : child r.1 r.2 = BB6.Agent48F1OneLF.parent :=
      sameTable_sound hF1OneLF
    rw [hEq]
    exact BB6.Agent48F1Integration.cover_oneLF championScore (by omega)

theorem acceptedRowsCover :
    ∀ r ∈ acceptedRows,
      Cover (WeightedBound championScore) (child r.1 r.2) := by
  intro r hr
  exact acceptedRowCover r hr

/-- The two exceptional depth-six continuations are the exact 0RD hard children
    already handled by Agent48Remaining.  The equalities are checked against the
    literal normalized tables, not inferred from matching addresses. -/
theorem rowRC_lift
    (h : Cover (WeightedBound championScore) (leaf rowRC)) :
    Cover (WeightedBound championScore) (child rowRC.1 rowRC.2) := by
  have hEq :
      sameTable (leaf rowRC)
        (BB6.Agent6F0.AFirst.childA ⟨false, true, 2⟩ ⟨false, true, 3⟩) = true := by
    decide
  rw [sameTable_sound hEq] at h
  exact BB6.Agent48Remaining.cover_zeroRC_of_RD championScore (by omega) h

theorem rowRE_lift
    (h : Cover (WeightedBound championScore) (leaf rowRE)) :
    Cover (WeightedBound championScore) (child rowRE.1 rowRE.2) := by
  have hEq :
      sameTable (leaf rowRE)
        (BB6.Agent6F0.child ⟨true, true, 4⟩ ⟨false, true, 3⟩) = true := by
    decide
  rw [sameTable_sound hEq] at h
  exact BB6.Agent48Remaining.cover_oneRE_of_RD championScore (by omega) h

/-- The terminal champion branch is already source-certified by the accepted
    weighted TNF parent certificate; this is transported to the normalized p7
    table by exact equality. -/
theorem p7_cover : Cover (WeightedBound championScore) p7 := by
  have hChampionP7 :
      Cover (WeightedBound championScore) BB6.Agent6ChampionResidual.championP7 := by
    simpa [championScore] using
      (BB6.Agent31ChampionParentIntegration.cover_of_frontier_leaves
        (RootedFrontier.closed
          BB6.Agent6ChampionResidual.championP7Path
          BB6.Agent31ChampionParentIntegration.parent_certificate_on_championP7)
        (by
          intro e he
          simp [residuals] at he))
  have hEq :
      sameTable p7 BB6.Agent6ChampionResidual.championP7 = true := by
    decide
  rw [sameTable_sound hEq]
  exact hChampionP7

/-- The normalized p0 cylinder is now reduced to exactly the 67 tables in
    remainingTables.  All 43 accepted siblings, both continuation implications,
    and the terminal p7 Cover have been consumed with exact table transports. -/
theorem raw139_cover_after_accepted
    (hLeaves : ∀ p ∈ remainingTables,
      Cover (WeightedBound championScore) p) :
    Cover (WeightedBound championScore) p0 :=
  raw139_cover championScore (by omega) acceptedRowsCover hLeaves
    rowRC_lift rowRE_lift p7_cover

#print axioms acceptedRowsCovered
#print axioms acceptedRowCover
#print axioms acceptedRowsCover
#print axioms rowRC_lift
#print axioms rowRE_lift
#print axioms p7_cover
#print axioms raw139_cover_after_accepted

end BB6.Agent14Raw139NormalizedAccepted
