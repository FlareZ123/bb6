import Raw11ExtraFamilyCoverage
import Raw11ExtraSweepCoverage

namespace BB6.Agent47ExtraExternal

open BB6Coverage

/-- Lift the two exact Raw11-extra sweep recurrences to any weighted bound. -/
theorem sweepSafe (v : Bool) (B : Nat) :
    ∀ m, compatible (Raw11ExtraSweepCoverage.table v) m → WeightedBound B m := by
  intro m hm
  exact weighted_never B m (Raw11ExtraSweepCoverage.never_compatible m hm)

/-- Lift each of the six exact E1/F0 growing-return recurrences. -/
theorem familySafe (v : Fin 6) (B : Nat) :
    ∀ m, compatible (Raw11ExtraFamilyCoverage.variantTable v) m → WeightedBound B m := by
  intro m hm
  exact weighted_never B m
    (Raw11ExtraFamilyCoverage.never_compatible
      (Raw11ExtraFamilyCoverage.variant_never v) m hm)

#print axioms sweepSafe
#print axioms familySafe

end BB6.Agent47ExtraExternal
