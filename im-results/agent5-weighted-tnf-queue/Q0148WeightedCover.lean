import Q0148NeverCover
import WeightedTNF

/-! The completed q0-148 hard-leaf proof is independent of the upper-bound
    threshold, including the initial blank-delay weight. -/
namespace BB6.Agent5Q0148NeverCover
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent5Q0148BoundarySweep

abbrev table : PartialMachine := p

theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf p (fun m hm => weighted_never B m (never_cover.sound m hm))

#print axioms cover
end BB6.Agent5Q0148NeverCover
