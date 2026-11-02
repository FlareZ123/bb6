import FirstUniform
import IndexWitness
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11

/-- At every 2-adic inverse depth there are arbitrarily large
    first-family halting indices whose authentic blank-origin
    candidate stopping states are excluded, assuming the source
    DeepFamily theorem used by FirstUniform. -/
theorem every_depth_unbounded_first_halt_exclusion (r lower : Nat) :
    ∃ s : Nat, lower ≤ s ∧
      ∀ m k : Nat, m=64*s+8 → k+3*m+4=2^(2*m+3) →
        ¬ BB6.Agent3.CReach 1 k := by
  obtain ⟨s,t,hs,hfact⟩ := index_witness_unbounded r (lower+r+1)
  refine ⟨s,by omega,?_⟩
  intro m k hm hk
  exact uniform_first_halt_depth m k r s t hm hfact (by omega) hk

#print axioms every_depth_unbounded_first_halt_exclusion
end BB6.Agent11
