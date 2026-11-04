import FastShield

namespace CascadeRoot512

open CascadeSource CascadeFastShield

/-- Finite mass-cutoff certificate: no source-C blank-root orbit can visit
    a surviving fatal reset at any index n<=512. Every step of the finite
    prefix is checked by ordinary Lean kernel reduction (not native_decide). -/
theorem blank_excludes_surviving_through_512 (n : Nat)
    (hn : 4≤n) (ht : n≤512) (hc : n%6=4 ∨ n%6=5) :
    ¬CascadeSource.Orbit (2,0) (CascadeManyShield.fatal n,0) := by
  set_option maxRecDepth 1200000 in
    exact fast_root_excludes 512 159000 n hn ht hc (by decide)

#print axioms blank_excludes_surviving_through_512

end CascadeRoot512
