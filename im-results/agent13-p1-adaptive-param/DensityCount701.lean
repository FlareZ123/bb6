import DensityCount700
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace BB6.Agent13Narrow

/-- The existing 700 certified residue classes, augmented by the
    independently source-certified class q = 853 mod 1024. -/
def certified701 (q : Nat) : Bool :=
  BB6.Agent9Density700.certified q || q%1024 == 853

def acceptedResidues701 : List Nat :=
  (List.range 1024).filter certified701

theorem q853_not_in_previous_700 :
    BB6.Agent9Density700.certified 853 = false := by decide

theorem q853_added :
    certified701 853 = true := by decide

/-- Exact union count: 700 previous classes plus q=853 mod 1024. -/
theorem certified_density_701 :
    acceptedResidues701.length = 701 := by decide

#print axioms q853_not_in_previous_700
#print axioms q853_added
#print axioms certified_density_701

end BB6.Agent13Narrow
