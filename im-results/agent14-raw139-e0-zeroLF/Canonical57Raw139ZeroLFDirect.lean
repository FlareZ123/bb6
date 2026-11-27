import Raw124Canonical58Membership
import Canonical64Raw139NormalizedDirect
import E0ZeroLFDischarge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Canonical57Raw139ZeroLFDirect

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6ChampionArithmetic
open BB6.Agent6Raw139Normalized
open BB6.Agent6ChampionResidual
open BB6.Agent14Raw139NormalizedE0ParentRows
open BB6.Agent14Canonical64Raw139NormalizedDirect
open BB6.Agent38ChampionThreshold

/-- The normalized E0=0LF row closed by the source-audited ZeroLF parent proof. -/
def e0LFTable : PartialMachine := leaf (2, ⟨false, false, 5⟩)

/-- ZeroLF occurs exactly once among the 63 normalized Raw139 rows left after
    the accepted E0=0RA/0RE/0RB/0RD parent cuts. -/
theorem e0LF_occurs_once :
    (normalizedTablesWithoutE0RE0RB0RD.filter
      (fun p => sameTable p e0LFTable)).length = 1 := by
  decide

/-- The normalized Raw139 frontier after also consuming E0=0LF. -/
def normalizedTablesWithoutE0Parents : List PartialMachine :=
  normalizedTablesWithoutE0RE0RB0RD.filter
    (fun p => !(sameTable p e0LFTable))

theorem normalizedTablesWithoutE0Parents_count :
    normalizedTablesWithoutE0Parents.length = 62 := by
  decide

/-- Exact table identity between the normalized row and the independently
    source-audited E0=0LF parent theorem. -/
theorem e0LFTable_eq_certifiedParent :
    e0LFTable = BB6.Agent14E0LFParent.parent := by
  exact sameTable_sound (by decide)

/-- Lift the 19,007 ZeroLF parent Cover to the exact champion score. -/
theorem e0LF_cover_at_champion :
    Cover (WeightedBound championScore) e0LFTable := by
  have hSmall : Cover (WeightedBound 19007) e0LFTable := by
    rw [e0LFTable_eq_certifiedParent]
    exact BB6.Agent14E0LFParent.weighted
  have hScore : 19007 ≤ championScore := by
    have h := champion_score_ge_6766859
    omega
  exact cover_mono hScore hSmall

/-- Reinsert the accepted ZeroLF row, recovering all 63 rows required by the
    previously checked Raw139 normalized consumer. -/
theorem normalized63_cover_from_62
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0Parents,
      Cover (WeightedBound championScore) p) :
    ∀ p ∈ normalizedTablesWithoutE0RE0RB0RD,
      Cover (WeightedBound championScore) p := by
  intro p hp
  by_cases hLF : sameTable p e0LFTable = true
  · have hpEq : p = e0LFTable := sameTable_sound hLF
    rw [hpEq]
    exact e0LF_cover_at_champion
  · exact hNorm p (List.mem_filter.mpr
      ⟨hp, by simp [normalizedTablesWithoutE0Parents, hLF]⟩)

/-- The full Raw139 canonical representative is bounded at the champion score
    from exactly 62 remaining normalized Raw139 Covers. -/
theorem raw139_championResidual_cover_from_62
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0Parents,
      Cover (WeightedBound championScore) p) :
    Cover (WeightedBound championScore) championResidual :=
  raw139_championResidual_cover_from_63 (normalized63_cover_from_62 hNorm)

/-- Use the currently source-accepted Canonical57 roster, obtained by removing
    Raw124 from the accepted Canonical58 roster. -/
abbrev roster57 := BB6.Agent2Raw124Canonical58Membership.roster57

theorem championResidual_count57 :
    (roster57.filter
      (fun e => sameTable e.2 championResidual)).length = 1 := by
  decide

noncomputable def roster57WithoutChampion :
    List (Nat × PartialMachine) :=
  roster57.filter (fun e => !(sameTable e.2 championResidual))

theorem roster57WithoutChampion_count :
    roster57WithoutChampion.length = 56 := by
  decide

/-- Current global conditional interface with Raw139 expanded through the new
    ZeroLF cut: 56 other Canonical57 Covers plus 62 normalized Raw139 Covers
    imply exactness at the already-attained champion score. -/
theorem exact_at_champion_with_62_normalized
    (hOther : ∀ e ∈ roster57WithoutChampion,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0Parents,
      Cover (WeightedBound championScore) p) :
    ExactBB6 (proposedTM63Moves + 7) := by
  have hRaw : Cover (WeightedBound (proposedTM63Moves + 7)) championResidual := by
    simpa [championScore] using raw139_championResidual_cover_from_62 hNorm
  exact BB6.Agent2Raw124Canonical58Membership.exact_at_champion_score
    (fun e he => by
      by_cases hs : sameTable e.2 championResidual = true
      · have hEq : e.2 = championResidual := sameTable_sound hs
        rw [hEq]
        exact hRaw
      · exact hOther e (List.mem_filter.mpr
          ⟨he, by simp [roster57WithoutChampion, hs]⟩))

#print axioms e0LF_occurs_once
#print axioms normalizedTablesWithoutE0Parents_count
#print axioms e0LFTable_eq_certifiedParent
#print axioms e0LF_cover_at_champion
#print axioms normalized63_cover_from_62
#print axioms raw139_championResidual_cover_from_62
#print axioms championResidual_count57
#print axioms roster57WithoutChampion_count
#print axioms exact_at_champion_with_62_normalized

end BB6.Agent14Canonical57Raw139ZeroLFDirect
