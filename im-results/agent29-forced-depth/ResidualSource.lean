import ResidualLowOdd
import DeepSecondFinal
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

/-- A source-connected UNIFORM residual wall for every deep odd-m high
    stopping candidate with m>=3. The exact normalizer is unbounded. -/
theorem second_deep_affine_residual_ge_220
    (j m k : Nat)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hj : j%2=0) (hm : m%2=1) (hs : (j+m)%4=3)
    (hlarge : 3≤m) :
    220 ≤ (BB6.Agent15.affineNormalize (2*j+3) k).2 := by
  have hd := BB6.Agent15.second_halt_deep_sector j m k hstop hj hm hs
  have hmod := BB6.Agent29Depth.second_deep_affine_terminal_four_mod_twelve
    j m k hstop hj hm hs
  exact odd_residual_ge_220 j m k
    (BB6.Agent15.oddDepth k)
    (BB6.Agent15.affineNormalize (2*j+3) k).2
    hlarge hm hstop hd.2.2.2.2 hmod

#print axioms second_deep_affine_residual_exponential
#print axioms second_deep_affine_residual_ge_220
end BB6.Agent29Barrier
