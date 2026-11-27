import Raw139LocalCore

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0CutsFinite

open BB6Coverage
open BB6.Agent14Raw139Core

def e0ZeroRA : PartialMachine := leaf (2, ⟨false, true, 0⟩)
def e0ZeroRE : PartialMachine := leaf (2, ⟨false, true, 4⟩)
def e0ZeroRB : PartialMachine := leaf (2, ⟨false, true, 1⟩)
def e0ZeroRD : PartialMachine := leaf (2, ⟨false, true, 3⟩)
def e0ZeroRF : PartialMachine := leaf (2, ⟨false, true, 5⟩)
def e0OneRE  : PartialMachine := leaf (2, ⟨true,  true, 4⟩)
def e0ZeroLF : PartialMachine := leaf (2, ⟨false, false, 5⟩)

def matchesAny (p : PartialMachine) (ps : List PartialMachine) : Bool :=
  ps.any (fun q => sameTable p q)

def acceptedE0Six : List PartialMachine :=
  [e0ZeroRA, e0ZeroRE, e0ZeroRB, e0ZeroRD, e0ZeroRF, e0OneRE]

def acceptedE0Seven : List PartialMachine :=
  e0ZeroLF :: acceptedE0Six

theorem acceptedE0Six_each_once :
    ∀ q ∈ acceptedE0Six,
      (remainingTables.filter (fun p => sameTable p q)).length = 1 := by
  decide

def normalizedAfterAcceptedE0Six : List PartialMachine :=
  remainingTables.filter (fun p => !(matchesAny p acceptedE0Six))

theorem normalizedAfterAcceptedE0Six_count :
    normalizedAfterAcceptedE0Six.length = 61 := by
  decide

def normalizedAfterAcceptedE0Seven : List PartialMachine :=
  remainingTables.filter (fun p => !(matchesAny p acceptedE0Seven))

theorem e0ZeroLF_occurs_once :
    (remainingTables.filter (fun p => sameTable p e0ZeroLF)).length = 1 := by
  decide

theorem normalizedAfterAcceptedE0Seven_count :
    normalizedAfterAcceptedE0Seven.length = 60 := by
  decide

theorem matchesAny_witness {p : PartialMachine} {ps : List PartialMachine}
    (h : matchesAny p ps = true) :
    ∃ q ∈ ps, sameTable p q = true := by
  simpa [matchesAny] using List.any_eq_true.mp h

#print axioms acceptedE0Six_each_once
#print axioms normalizedAfterAcceptedE0Six_count
#print axioms e0ZeroLF_occurs_once
#print axioms normalizedAfterAcceptedE0Seven_count
#print axioms matchesAny_witness

end BB6.Agent14Raw139NormalizedE0CutsFinite
