import Raw124Canonical58Membership
import Raw139NormalizedAcceptedE0Six61Local

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Canonical57Raw139AcceptedE0SixDirect

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6ChampionArithmetic
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedAcceptedE0Six61Local

abbrev roster57 := BB6.Agent2Raw124Canonical58Membership.roster57

theorem p0_count57 :
    (roster57.filter (fun e => sameTable e.2 p0)).length = 1 := by
  decide

noncomputable def roster57WithoutRaw139 : List (Nat × PartialMachine) :=
  roster57.filter (fun e => !(sameTable e.2 p0))

theorem roster57WithoutRaw139_count :
    roster57WithoutRaw139.length = 56 := by
  decide

/-- Current-roster conditional exactness theorem after consuming all six
    source-accepted normalized E0 parents inside Raw139. -/
theorem exact_at_champion_with_61_normalized
    (hOther : ∀ e ∈ roster57WithoutRaw139,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hNorm : ∀ p ∈ normalizedAfterAcceptedE0Six,
      Cover (WeightedBound localScore) p) :
    ExactBB6 (proposedTM63Moves + 7) := by
  have hRaw : Cover (WeightedBound localScore) p0 :=
    raw139_p0_cover_from_61_accepted hNorm
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
#print axioms exact_at_champion_with_61_normalized

end BB6.Agent14Canonical57Raw139AcceptedE0SixDirect
