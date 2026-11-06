import ResidualExponential
import SecondDeepSector
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Barrier

/-- Source-connected exponential lower bound for the genuine Machine C
    high stopping sector whose odd-depth affine normalization is unbounded. -/
theorem second_deep_affine_residual_exponential
    (j m k : Nat)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hj : j%2=0) (hm : m%2=1) (hs : (j+m)%4=3) :
    2^(m+2) ≤ (BB6.Agent15.affineNormalize (2*j+3) k).2 + 6*m+1 := by
  have hd := BB6.Agent15.second_halt_deep_sector j m k hstop hj hm hs
  exact second_stop_odd_residual_exponential j m k
    (BB6.Agent15.oddDepth k)
    (BB6.Agent15.affineNormalize (2*j+3) k).2
    (by omega) hm hstop hd.2.2.2.2

#print axioms second_deep_affine_residual_exponential
end BB6.Agent29Barrier
