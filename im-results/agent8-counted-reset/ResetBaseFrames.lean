import Lean
import CountedReset

namespace BB6Coverage.Agent8CountedReset

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder

/-!
Lightweight reset-base frame data. Kept separate from CountedResetBase's
finite native_decide trace certificates so source closures that only need
the m=2 midpoint can audit the frame without importing those certificates.
-/

/-- The smallest interval containing every head query in the three
a=b=0, n odd, marker-specific base traces. -/
def resetBaseInside (m : Nat) (x : Int) : Bool :=
  if m = 0 then decide (-7 ≤ x ∧ x ≤ 14)
  else decide (-8 ≤ x ∧ x ≤ 14)

/-- Local input tape for the marker-zero base trace. -/
def resetBaseInput0 : FConfig :=
  ⟨3, 0, [-7, -4, -1, 2, 3, 4, 7, 8, 9]⟩

/-- Local input tape for the marker-one base trace. -/
def resetBaseInput1 : FConfig :=
  ⟨3, 0, [-8, -5, -2, 0, 2, 3, 4, 7, 8, 9]⟩

/-- Local input tape for the marker-two base trace. -/
def resetBaseInput2 : FConfig :=
  ⟨3, 0, [-6, -3, -1, 0, 2, 3, 4, 7, 8, 9]⟩

/- The marked lists below deliberately retain `fMove`'s exact insertion/filter order.
Do not sort them: `FConfig` equality is ordered-list equality. -/
/-- Local output tape after the marker-zero base trace. -/
def resetBaseOutput0 : FConfig :=
  ⟨3, 5, [7, 8, 9, 12, 13, 14, 5, 4, 3, 2, 1, -1, -4, -5, -6, -7]⟩

/-- Local output tape after the marker-one base trace. -/
def resetBaseOutput1 : FConfig :=
  ⟨3, 5, [7, 8, 9, 12, 13, 14, 5, 4, 3, 2, 1, 0, -2, -5, -6, -7, -8]⟩

/-- Local output tape after the marker-two base trace. -/
def resetBaseOutput2 : FConfig :=
  ⟨3, 5, [7, 8, 9, 12, 13, 14, 5, 4, 3, 2, 1, 0, -1, -3, -6, -7, -8]⟩

/-- Uniform notation for the three local input frames. -/
def resetBaseInput (m : Nat) : FConfig :=
  if m = 0 then resetBaseInput0
  else if m = 1 then resetBaseInput1
  else resetBaseInput2

/-- Uniform notation for the three local output frames. -/
def resetBaseOutput (m : Nat) : FConfig :=
  if m = 0 then resetBaseOutput0
  else if m = 1 then resetBaseOutput1
  else resetBaseOutput2


end BB6Coverage.Agent8CountedReset
