import Raw139NormalizedE0TenAcceptedFinite

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite

open BB6Coverage
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0TenAcceptedFinite

/-- The eleventh *already* source-certified normalized E0 family is 0RC
    (ordinary code 9), closed by Agent6 in run 45935140791 at bound 1673363.
    It is not the still-pending 0LF/code20 family. -/
def e0ZeroRC : PartialMachine := leaf (2, ⟨false, true, 2⟩)

/-- Eleven independently source-accepted exact six-hole E0 parent cylinders. -/
def acceptedElevenCertified : List PartialMachine :=
  e0ZeroRC :: acceptedE0Ten

/-- Twelve possible source-accepted E0 cylinders once the outstanding
    ZeroLF all-completion parent audit is compiled and discharged. -/
def acceptedTwelveProspective : List PartialMachine :=
  e0ZeroLF :: acceptedElevenCertified

theorem zeroRC_in_normalized_once :
    (remainingTables.filter (fun p => sameTable p e0ZeroRC)).length = 1 := by
  decide

theorem zeroRC_disjoint_ten :
    matchesAny e0ZeroRC acceptedE0Ten = false := by
  decide

theorem acceptedEleven_each_once :
    ∀ q ∈ acceptedElevenCertified,
      (remainingTables.filter (fun p => sameTable p q)).length = 1 := by
  decide

def normalizedAfterElevenCertified : List PartialMachine :=
  remainingTables.filter (fun p => !(matchesAny p acceptedElevenCertified))

theorem normalizedAfterElevenCertified_count :
    normalizedAfterElevenCertified.length = 56 := by
  decide

def normalizedAfterTwelveProspective : List PartialMachine :=
  remainingTables.filter (fun p => !(matchesAny p acceptedTwelveProspective))

theorem normalizedAfterTwelveProspective_count :
    normalizedAfterTwelveProspective.length = 55 := by
  decide

#print axioms zeroRC_in_normalized_once
#print axioms zeroRC_disjoint_ten
#print axioms acceptedEleven_each_once
#print axioms normalizedAfterElevenCertified_count
#print axioms normalizedAfterTwelveProspective_count

end BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
