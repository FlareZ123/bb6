import Raw139NormalizedE0CutsFinite

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0OneRFFinite

open BB6Coverage
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite

/-- OneRF's ordinary transition code is 23, the accepted six-hole
    normalized Raw139 E0 parent (not a complement or a renamed machine). -/
def e0OneRF : PartialMachine := leaf (2, ⟨true, true, 5⟩)

/-- Six source-accepted E0 classes plus the separately source-accepted OneRF. -/
def acceptedSixPlusOneRF : List PartialMachine :=
  e0OneRF :: acceptedE0Six

/-- The eighth ordinary E0 class becomes usable only after ZeroLF discharge. -/
def acceptedEight : List PartialMachine :=
  e0ZeroLF :: acceptedSixPlusOneRF

theorem oneRF_occurs_once :
    (remainingTables.filter (fun p => sameTable p e0OneRF)).length = 1 := by
  decide

theorem oneRF_not_in_six :
    matchesAny e0OneRF acceptedE0Six = false := by
  decide

theorem oneRF_not_in_seven :
    matchesAny e0OneRF acceptedE0Seven = false := by
  decide

def normalizedAfterSixPlusOneRF : List PartialMachine :=
  remainingTables.filter (fun p => !(matchesAny p acceptedSixPlusOneRF))

theorem normalizedAfterSixPlusOneRF_count :
    normalizedAfterSixPlusOneRF.length = 60 := by
  decide

def normalizedAfterEight : List PartialMachine :=
  remainingTables.filter (fun p => !(matchesAny p acceptedEight))

theorem normalizedAfterEight_count :
    normalizedAfterEight.length = 59 := by
  decide

#print axioms oneRF_occurs_once
#print axioms oneRF_not_in_six
#print axioms oneRF_not_in_seven
#print axioms normalizedAfterSixPlusOneRF_count
#print axioms normalizedAfterEight_count

end BB6.Agent14Raw139NormalizedE0OneRFFinite
