import Raw139NormalizedE0CutsFinite

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0CutsProspective

open BB6Coverage
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite

/-- E0=0RC is the seventh ordinary E0 parent currently under recovery. -/
def e0ZeroRC : PartialMachine := leaf (2, ⟨false, true, 2⟩)

/-- Seven parent tables if the source audit for E0=0RC recovers. -/
def acceptedSixPlusZeroRC : List PartialMachine :=
  e0ZeroRC :: acceptedE0Six

/-- Eight parent tables if both E0=0RC and E0=0LF become available. -/
def acceptedSixPlusZeroRCPlusZeroLF : List PartialMachine :=
  e0ZeroLF :: acceptedSixPlusZeroRC

theorem e0ZeroRC_occurs_once :
    (remainingTables.filter (fun p => sameTable p e0ZeroRC)).length = 1 := by
  decide

theorem acceptedSixPlusZeroRC_nodup :
    acceptedSixPlusZeroRC.Nodup := by
  decide

def normalizedAfterSixPlusZeroRC : List PartialMachine :=
  remainingTables.filter
    (fun p => !(matchesAny p acceptedSixPlusZeroRC))

theorem normalizedAfterSixPlusZeroRC_count :
    normalizedAfterSixPlusZeroRC.length = 60 := by
  decide

theorem acceptedSixPlusZeroRCPlusZeroLF_nodup :
    acceptedSixPlusZeroRCPlusZeroLF.Nodup := by
  decide

def normalizedAfterSixPlusZeroRCPlusZeroLF : List PartialMachine :=
  remainingTables.filter
    (fun p => !(matchesAny p acceptedSixPlusZeroRCPlusZeroLF))

theorem normalizedAfterSixPlusZeroRCPlusZeroLF_count :
    normalizedAfterSixPlusZeroRCPlusZeroLF.length = 59 := by
  decide

#print axioms e0ZeroRC_occurs_once
#print axioms acceptedSixPlusZeroRC_nodup
#print axioms normalizedAfterSixPlusZeroRC_count
#print axioms acceptedSixPlusZeroRCPlusZeroLF_nodup
#print axioms normalizedAfterSixPlusZeroRCPlusZeroLF_count

end BB6.Agent14Raw139NormalizedE0CutsProspective
