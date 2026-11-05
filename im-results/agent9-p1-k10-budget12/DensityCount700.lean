import DensityCount695
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace BB6.Agent9Density700

def k10New : List Nat := [213,661,917,977,998]
def certified (q : Nat) : Bool :=
  BB6.Agent9Density.certified q || k10New.contains (q%1024)
def acceptedResidues : List Nat := (List.range 1024).filter certified

/-- Count of source-certified P1 n=16q+2 critical exclusions per
    complete period q modulo 1024, apart from finite low-q tails. -/
theorem certified_density_700 : acceptedResidues.length = 700 := by decide

#print axioms certified_density_700
end BB6.Agent9Density700
