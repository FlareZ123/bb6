import Raw124Canonical58Membership
import Raw139NormalizedZeroLF62Local

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Canonical57Raw139ZeroLFDirect

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6ChampionArithmetic
open BB6.Agent31FourHoleRoster
open BB6.Agent6Raw139Normalized
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent14Raw139NormalizedZeroLF62Local

/-- The current source-accepted 57-entry quotient roster. -/
abbrev roster57 := BB6.Agent2Raw124Canonical58Membership.roster57

/-- The normalized Raw139 root itself occurs exactly once in Canonical57. -/
theorem p0_count57 :
    (roster57.filter (fun e => sameTable e.2 p0)).length = 1 := by
  decide

/-- The 56 canonical representatives other than Raw139. -/
noncomputable def roster57WithoutRaw139 : List (Nat × PartialMachine) :=
  roster57.filter (fun e => !(sameTable e.2 p0))

theorem roster57WithoutRaw139_count :
    roster57WithoutRaw139.length = 56 := by
  decide

/-- Thin current-roster consumer for the roster-independent Raw139 theorem:
    56 other Canonical57 Covers plus 62 normalized Raw139 Covers imply exact
    BB(6) at the already attained champion score. -/
theorem exact_at_champion_with_62_normalized
    (hOther : ∀ e ∈ roster57WithoutRaw139,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0Parents,
      Cover (WeightedBound localScore) p) :
    ExactBB6 (proposedTM63Moves + 7) := by
  have hRaw : Cover (WeightedBound localScore) p0 :=
    raw139_p0_cover_from_62 hNorm
  exact BB6.Agent2Raw124Canonical58Membership.exact_at_champion_score
    (fun e he => by
      by_cases hs : sameTable e.2 p0 = true
      · have hEq : e.2 = p0 := sameTable_sound hs
        rw [hEq]
        simpa [localScore] using hRaw
      · exact hOther e (List.mem_filter.mpr
          ⟨he, by simp [roster57WithoutRaw139, hs]⟩))

#print axioms p0_count57
#print axioms roster57WithoutRaw139_count
#print axioms exact_at_champion_with_62_normalized

end BB6.Agent14Canonical57Raw139ZeroLFDirect
