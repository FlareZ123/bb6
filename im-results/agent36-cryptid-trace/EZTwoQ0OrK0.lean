import Lean.Elab.Tactic.Omega
import EZTwoK0BRegular
import EZeroZTwoAll

/-!
  A single source-backed original D E/p2 Z-marker exit criterion:
  either no 10-pairs (all E indices) or E-index k divisible by three
  (all pair counts). The q=0 case uses the original all-index source
  EZeroZTwoAll theorem; q>0,k≡0 uses our E-to-B source return.

  This closes a complete two-axis infinite prepared family, without
  claiming it contains the true blank-root orbit.
-/
namespace BB6.Agent36EZComplete

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2BoundaryBZero BB6.BoundaryPadding

set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

/-- Original-machine all-q E/p2 zero-marker source return when k=3t. -/
theorem k0_all_q (t q m : Nat) :
    ∃ T a r b,
      ObsEq
        (run T
          (packet (3*(3*t)+4) q 2
            (BB6.Agent2MarkerZero.marker m)))
        (regularSection a r b) := by
  cases q with
  | zero =>
    have h := BB6.Agent36EZeroZTwoAll.all_E_zero_p2_marker_regular (3*t) m
    simpa [BB6.Agent36EZeroZTwoAll.markerZ,BB6.Agent2MarkerZero.marker] using h
  | succ q =>
    exact BB6.Agent36EZTwoBZero.e_two_Z_k0_regular t q m

/-- Combined all E-indices q=0, plus every q when index k≡0 mod 3. -/
theorem all_q0_or_k0 (k q m : Nat)
    (h : q=0 ∨ k%3=0) :
    ∃ T a r b,
      ObsEq
        (run T
          (packet (3*k+4) q 2
            (BB6.Agent2MarkerZero.marker m)))
        (regularSection a r b) := by
  rcases h with hq | hk
  · subst q
    have h := BB6.Agent36EZeroZTwoAll.all_E_zero_p2_marker_regular k m
    simpa [BB6.Agent36EZeroZTwoAll.markerZ,BB6.Agent2MarkerZero.marker] using h
  · let t : Nat := k/3
    have hkt : k=3*t := by dsimp [t]; omega
    rw [hkt]
    exact k0_all_q t q m

#print axioms k0_all_q
#print axioms all_q0_or_k0
end BB6.Agent36EZComplete
