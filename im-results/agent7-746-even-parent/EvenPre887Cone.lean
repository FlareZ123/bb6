import EvenPre887ConeOnly
import FeederExceptional887

set_option maxHeartbeats 0

namespace CascadeEvenPre887

/-- Combine the independently checkable even-predecessor cone with the
    uniform exceptional-feeder reduction to exclude the full fatal target
    at the single index n=887. -/
theorem fatal887_root_unreachable :
    ¬ CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal 887,0) := by
  intro h
  have he : CascadeSweep.ReachC (2,0) (evenPre887,0) := by
    have hh := (CascadeFeeder887.fatal_root_iff_even_parent_formula_887
      887 (by decide)).mp h
    simpa [evenPre887] using hh
  exact evenPre887_root_unreachable he

#print axioms fatal887_root_unreachable

end CascadeEvenPre887
