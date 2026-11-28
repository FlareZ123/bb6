import Raw139NormalizedPostTwelve48
import Raw139NormalizedE0OneRFConditional

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedCertified18Finite

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedE0OneRFConditional
open BB6.Agent14Raw139NormalizedPostTwelve53
open BB6.Agent14Raw139NormalizedPostTwelve52
open BB6.Agent14Raw139NormalizedPostTwelve51
open BB6.Agent14Raw139NormalizedPostTwelve50
open BB6.Agent14Raw139NormalizedPostTwelve49
open BB6.Agent14Raw139NormalizedPostTwelve48

/-- Eighteen exact normalized Raw139 cylinders whose whole-parent Covers
    have independent original-source acceptance.  ZeroLF is deliberately
    excluded: its parent recovery is still pending. -/
def sourceAcceptedEighteen : List PartialMachine :=
  acceptedElevenCertified ++ sourceAcceptedExtraTwo ++
    [e0OneLF, c1ZeroLA, c1ZeroLC, e0OneLA, e0ZeroLC]

theorem sourceAcceptedEighteen_count :
    sourceAcceptedEighteen.length = 18 := by
  decide

theorem sourceAcceptedEighteen_each_once :
    ∀ q ∈ sourceAcceptedEighteen,
      (remainingTables.filter (fun p => sameTable p q)).length = 1 := by
  decide

def normalizedAfterSourceAcceptedEighteen : List PartialMachine :=
  remainingTables.filter
    (fun p => !(matchesAny p sourceAcceptedEighteen))

theorem normalizedAfterSourceAcceptedEighteen_count :
    normalizedAfterSourceAcceptedEighteen.length = 49 := by
  decide

/-- The nineteenth row is the exact E0=0LF/ZeroLF cylinder.  Keeping it
    separate makes the accepted 49-row frontier and the prospective 48-row
    frontier impossible to confuse. -/
def prospectiveNineteen : List PartialMachine :=
  e0ZeroLF :: sourceAcceptedEighteen

theorem zeroLF_not_sourceAcceptedEighteen :
    matchesAny e0ZeroLF sourceAcceptedEighteen = false := by
  decide

theorem prospectiveNineteen_count :
    prospectiveNineteen.length = 19 := by
  decide

theorem prospectiveNineteen_each_once :
    ∀ q ∈ prospectiveNineteen,
      (remainingTables.filter (fun p => sameTable p q)).length = 1 := by
  decide

def normalizedAfterProspectiveNineteen : List PartialMachine :=
  remainingTables.filter
    (fun p => !(matchesAny p prospectiveNineteen))

theorem normalizedAfterProspectiveNineteen_count :
    normalizedAfterProspectiveNineteen.length = 48 := by
  decide

/-- Exact generic reinsertion for the source-accepted frontier.  This theorem
    does not assume ZeroLF. -/
theorem remainingTables_cover_from_49_certified (B : Nat)
    (h18 : ∀ q ∈ sourceAcceptedEighteen,
      Cover (WeightedBound B) q)
    (h49 : ∀ p ∈ normalizedAfterSourceAcceptedEighteen,
      Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p :=
  remainingTables_cover_from_filter B sourceAcceptedEighteen h18
    (by simpa [normalizedAfterSourceAcceptedEighteen] using h49)

/-- Prospective exact reinsertion if the pending ZeroLF parent is accepted. -/
theorem remainingTables_cover_from_48_prospective (B : Nat)
    (h19 : ∀ q ∈ prospectiveNineteen,
      Cover (WeightedBound B) q)
    (h48 : ∀ p ∈ normalizedAfterProspectiveNineteen,
      Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p :=
  remainingTables_cover_from_filter B prospectiveNineteen h19
    (by simpa [normalizedAfterProspectiveNineteen] using h48)

#print axioms sourceAcceptedEighteen_count
#print axioms sourceAcceptedEighteen_each_once
#print axioms normalizedAfterSourceAcceptedEighteen_count
#print axioms zeroLF_not_sourceAcceptedEighteen
#print axioms prospectiveNineteen_count
#print axioms prospectiveNineteen_each_once
#print axioms normalizedAfterProspectiveNineteen_count
#print axioms remainingTables_cover_from_49_certified
#print axioms remainingTables_cover_from_48_prospective

end BB6.Agent14Raw139NormalizedCertified18Finite
