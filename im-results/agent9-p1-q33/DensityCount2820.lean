import DensityCount700

namespace BB6.Agent9ShallowDensity

/-- Twenty completely new q classes, each certified for q ≡ q0 mod 4096
    and absent from the prior 700/1024 sieve. -/
def newQ : List Nat :=
  [109,165,225,253,397,409,413,433,533,629,681,737,793,821,865,877,993,1013,1017,1021]

def accepted (q : Nat) : Bool :=
  BB6.Agent9Density700.certified q || newQ.contains (q%4096)

def accepted4096 : List Nat := (List.range 4096).filter accepted

theorem newQ_pairwise_uncovered :
    newQ.all (fun q => !BB6.Agent9Density700.certified q) = true := by decide

/-- Conditional on source-certification of each of the twenty new cylinders,
    the union of source-certified gateway-excluded q classes has
    exactly 2820 of 4096 residues. See Q12Shallow generated source audit. -/
theorem certified_density_2820 : accepted4096.length = 2820 := by decide

#print axioms newQ_pairwise_uncovered
#print axioms certified_density_2820

end BB6.Agent9ShallowDensity
