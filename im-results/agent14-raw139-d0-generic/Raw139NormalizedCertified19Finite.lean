import Raw139NormalizedCertified18Finite

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedCertified19Finite

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedCertified18Finite

/-- C1=0RA is now independently source-certified:
    run 46125877467, theorem BB6.Agent14Raw139C1ZeroRA.weighted,
    native weighted bound 14,876,970. -/
def c1ZeroRA : PartialMachine := leaf (4, ⟨false, true, 0⟩)

theorem c1ZeroRA_occurs_once :
    (remainingTables.filter (fun p => sameTable p c1ZeroRA)).length = 1 := by
  decide

def sourceAcceptedNineteen : List PartialMachine :=
  c1ZeroRA :: sourceAcceptedEighteen

theorem sourceAcceptedNineteen_count :
    sourceAcceptedNineteen.length = 19 := by
  decide

theorem sourceAcceptedNineteen_each_once :
    ∀ q ∈ sourceAcceptedNineteen,
      (remainingTables.filter (fun p => sameTable p q)).length = 1 := by
  decide

def normalizedAfterSourceAcceptedNineteen : List PartialMachine :=
  remainingTables.filter
    (fun p => !(matchesAny p sourceAcceptedNineteen))

theorem normalizedAfterSourceAcceptedNineteen_count :
    normalizedAfterSourceAcceptedNineteen.length = 48 := by
  decide

/-- ZeroLF remains the one pending parent in the next prospective cut. -/
def prospectiveTwenty : List PartialMachine :=
  e0ZeroLF :: sourceAcceptedNineteen

theorem zeroLF_not_sourceAcceptedNineteen :
    matchesAny e0ZeroLF sourceAcceptedNineteen = false := by
  decide

theorem prospectiveTwenty_count :
    prospectiveTwenty.length = 20 := by
  decide

def normalizedAfterProspectiveTwenty : List PartialMachine :=
  remainingTables.filter
    (fun p => !(matchesAny p prospectiveTwenty))

theorem normalizedAfterProspectiveTwenty_count :
    normalizedAfterProspectiveTwenty.length = 47 := by
  decide

theorem remainingTables_cover_from_48_certified (B : Nat)
    (h19 : ∀ q ∈ sourceAcceptedNineteen,
      Cover (WeightedBound B) q)
    (h48 : ∀ p ∈ normalizedAfterSourceAcceptedNineteen,
      Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p :=
  remainingTables_cover_from_filter B sourceAcceptedNineteen h19
    (by simpa [normalizedAfterSourceAcceptedNineteen] using h48)

theorem remainingTables_cover_from_47_prospective (B : Nat)
    (h20 : ∀ q ∈ prospectiveTwenty,
      Cover (WeightedBound B) q)
    (h47 : ∀ p ∈ normalizedAfterProspectiveTwenty,
      Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p :=
  remainingTables_cover_from_filter B prospectiveTwenty h20
    (by simpa [normalizedAfterProspectiveTwenty] using h47)

#print axioms c1ZeroRA_occurs_once
#print axioms sourceAcceptedNineteen_count
#print axioms sourceAcceptedNineteen_each_once
#print axioms normalizedAfterSourceAcceptedNineteen_count
#print axioms zeroLF_not_sourceAcceptedNineteen
#print axioms prospectiveTwenty_count
#print axioms normalizedAfterProspectiveTwenty_count
#print axioms remainingTables_cover_from_48_certified
#print axioms remainingTables_cover_from_47_prospective

end BB6.Agent14Raw139NormalizedCertified19Finite
