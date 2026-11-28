import Raw139NormalizedCertified18Finite
import Raw139NormalizedAcceptedCovers

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedCertified18Champion

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedCertified18Finite
open BB6.Agent14Raw139NormalizedAccepted
open BB6.Agent31FourHoleRoster

/-- At the exact champion cutoff, the accepted Raw139 spine adapter consumes
    all 43 sibling Covers, both continuation bridges and terminal p7.  The
    only remaining local hypotheses are Covers for the eighteen independently
    source-accepted normalized parent cylinders plus their exact 49-row
    complement. -/
theorem raw139_p0_at_champion_from_49_certified
    (h18 : ∀ q ∈ sourceAcceptedEighteen,
      Cover (WeightedBound championScore) q)
    (h49 : ∀ p ∈ normalizedAfterSourceAcceptedEighteen,
      Cover (WeightedBound championScore) p) :
    Cover (WeightedBound championScore) p0 :=
  raw139_cover_after_accepted
    (remainingTables_cover_from_49_certified championScore h18 h49)

/-- If the pending ZeroLF whole-parent theorem is accepted, the same accepted
    spine adapter leaves exactly nineteen parent Covers and 48 complementary
    normalized rows. -/
theorem raw139_p0_at_champion_from_48_prospective
    (h19 : ∀ q ∈ prospectiveNineteen,
      Cover (WeightedBound championScore) q)
    (h48 : ∀ p ∈ normalizedAfterProspectiveNineteen,
      Cover (WeightedBound championScore) p) :
    Cover (WeightedBound championScore) p0 :=
  raw139_cover_after_accepted
    (remainingTables_cover_from_48_prospective championScore h19 h48)

#print axioms raw139_p0_at_champion_from_49_certified
#print axioms raw139_p0_at_champion_from_48_prospective

end BB6.Agent14Raw139NormalizedCertified18Champion
