import DensityCount700

namespace BB6.Agent9ShallowDensity

/-- Twelve completely new q classes, each certified for q ≡ q0 mod 4096
    and absent from the prior 700/1024 sieve. -/
def newQ : List Nat :=
  [109,253,397,409,413,681,793,877,1017,1021,165,225]

def accepted (q : Nat) : Bool :=
  BB6.Agent9Density700.certified q || newQ.contains (q%4096)

def accepted4096 : List Nat := (List.range 4096).filter accepted

theorem newQ_pairwise_uncovered :
    newQ.all (fun q => !BB6.Agent9Density700.certified q) = true := by decide

/-- Conditional on source-certification of each of the twelve new cylinders,
    the union of source-certified gateway-excluded q classes has
    exactly 2812 of 4096 residues. See Q12Shallow generated source audit. -/
theorem certified_density_2812 : accepted4096.length = 2812 := by decide

#print axioms newQ_pairwise_uncovered
#print axioms certified_density_2812

end BB6.Agent9ShallowDensity
