import Raw39ThresholdReduction
import Raw39SiblingThreshold
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
An exact all-threshold characterization of the inductive *Cover*
certificate needed by the global TNF quotient, not merely the numeric
Bound predicate. For every natural B, a Raw39 parent Cover at B exists
if and only if the sole unresolved A1=1LE child is bounded at B.

The theorem does NOT assert existence of a numerical bound for that child.
It uses the source-accepted 28,311 halting witness in 1LE, the
10-sibling upper-bound join, and Cover.sound.
-/

namespace BB6.Agent11Raw39CoverSpectrum

open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent11Raw39AcceptedSix (p39 child)

/-- Universal reduction of a *parent Cover at any score* to precisely one
child's weighted-bound predicate. Both sides remain open above 28,310
until the missing whole-child upper bound is source-certified. -/
theorem cover_iff_oneLE (B : Nat) :
    Cover (WeightedBound B) p39 ↔
      Bound B (child ⟨true,false,4⟩) := by
  constructor
  · intro hc
    have hp : Bound B p39 := by
      intro m hm k d hk hd
      exact hc.sound m hm k d hk hd
    exact (BB6.Agent11Raw39ThresholdReduction.bound_iff_oneLE B).mp hp
  · intro h1
    have hb : 15125 ≤ B := by
      have hmin :=
        BB6.Agent11Raw39ThresholdReduction.oneLE_lower_bound B h1
      omega
    exact BB6.Agent11Raw39SiblingThreshold.cover_from_oneLE B hb h1

#print axioms cover_iff_oneLE

end BB6.Agent11Raw39CoverSpectrum
