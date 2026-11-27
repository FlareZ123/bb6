import Canonical58Raw113Graft
import Raw139NormalizedAcceptedE0Six61Local

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Canonical58Raw139AcceptedE0SixDirect

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6ChampionArithmetic
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedAcceptedE0Six61Local

/-- The strongest accepted global quotient roster in the current board lineage. -/
abbrev roster58 := BB6.Agent31Canonical58Raw113Graft.roster58

/-- The normalized Raw139 root occurs exactly once in the accepted Canonical58
    complement. -/
theorem p0_count58 :
    (roster58.filter (fun e => sameTable e.2 p0)).length = 1 := by
  decide

/-- The 57 accepted Canonical58 representatives other than Raw139. -/
noncomputable def roster58WithoutRaw139 : List (Nat × PartialMachine) :=
  roster58.filter (fun e => !(sameTable e.2 p0))

theorem roster58WithoutRaw139_count :
    roster58WithoutRaw139.length = 57 := by
  decide

/-- Current accepted-roster conditional exactness theorem with Raw139 expanded
    through all six source-accepted normalized E0 parents: 57 other global
    Covers plus 61 normalized Raw139 Covers imply exactness at the attained
    champion score. -/
theorem exact_at_champion_with_61_normalized
    (hOther : ∀ e ∈ roster58WithoutRaw139,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hNorm : ∀ p ∈ normalizedAfterAcceptedE0Six,
      Cover (WeightedBound localScore) p) :
    ExactBB6 (proposedTM63Moves + 7) := by
  have hRaw : Cover (WeightedBound localScore) p0 :=
    raw139_p0_cover_from_61_accepted hNorm
  exact BB6.Agent31Canonical58Raw113Graft.exact_at_champion_score
    (fun e he => by
      by_cases hs : sameTable e.2 p0 = true
      · have hEq : e.2 = p0 := sameTable_sound hs
        rw [hEq]
        simpa [localScore] using hRaw
      · exact hOther e (List.mem_filter.mpr
          ⟨he, by simp [roster58WithoutRaw139, hs]⟩))

#print axioms p0_count58
#print axioms roster58WithoutRaw139_count
#print axioms exact_at_champion_with_61_normalized

end BB6.Agent14Canonical58Raw139AcceptedE0SixDirect
