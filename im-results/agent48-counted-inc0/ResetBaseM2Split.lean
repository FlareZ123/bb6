import CountedResetBase
import Lean.Elab.Tactic.Omega

/-!
# Exact m=2 reset-base midpoint

The existing 71-step finite reset base is split at the 27-step cost of
`outerLCInc_preHRun` for m=2,n=1,a=0. The midpoint is computed with the
actual TM2 transition table and exact ordered finite-tape representation.
This is only a finite base split; no arbitrary-counter lift or S0 embedding
is asserted.
-/

namespace BB6Coverage.Agent48ResetBaseM2Split

open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48Champion

/-- Exact ordered finite configuration after the first 27 steps of
`resetBaseInput2`. -/
def resetBaseMiddle2 : FConfig :=
  ⟨1, -5, [-6,-7,-8,-5,-4,-3,-2,0,1,2,3,4,7,8,9]⟩

/-- The first 27 steps end at the same state/head as the m=2,n=1
outer-L/C pre-H-run boundary. -/
theorem resetBase_m2_prefix27 :
    fRun tm2 27 resetBaseInput2 = some resetBaseMiddle2 := by
  decide

/-- The remaining 44 steps finish the finite m=2 reset base. -/
theorem resetBase_m2_suffix44 :
    fRun tm2 44 resetBaseMiddle2 = some resetBaseOutput2 := by
  decide

#print axioms resetBase_m2_prefix27
#print axioms resetBase_m2_suffix44

end BB6Coverage.Agent48ResetBaseM2Split
