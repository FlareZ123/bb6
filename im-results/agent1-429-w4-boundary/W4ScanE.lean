import BB429JuncHeadExcursion
import Lean.Elab.Tactic.Omega

namespace BB429W4ScanE

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion

/-- The #429 u=0, w=4 partial-sweep A/1 boundary reaches an exact
    source S_E configuration after 19 primitive steps. The parameter
    remains unbounded and the entire zipper tape is preserved. -/
theorem boundary_to_sourceScanE_delta (v : Nat) :
    runWithDelta 19
      (z 0 (true :: (pairs01 (v+5) ++ ones 5)) true [false,true]) =
      some (sourceScanE (v+4) (sourceSuffix 0), -3) := by
  rfl

/-- Even boundary parameter: exact return into the positive-u Junc family,
    with right counter one and all movement accounted for. -/
theorem even_boundary_to_junc_delta (k : Nat) :
    runWithDelta (18*k+109)
      (z 0 (true :: (pairs01 (2*k+5) ++ ones 5)) true [false,true]) =
      some (junc 2 (2*k+6) 1, -((4*k+11 : Nat) : Int)) := by
  have hfirst := boundary_to_sourceScanE_delta (2*k)
  have htail := sourceScanE_finishC_even_delta (k+2) 0
  rw [crossTime_even] at htail
  have hrewrite : 2*k+4 = 2*(k+2) := by omega
  rw [hrewrite] at hfirst
  have htime :
      18*k+109 = 19 + ((14*(k+2)+41)+1 + (12+2*(2*(k+2)))) := by
    omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  have hw : 2*(k+2)+2 = 2*k+6 := by omega
  rw [hw]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Odd boundary parameter: exact return into the zero-u Junc family,
    also with right counter one. -/
theorem odd_boundary_to_junc_delta (k : Nat) :
    runWithDelta (18*k+85)
      (z 0 (true :: (pairs01 (2*k+1+5) ++ ones 5)) true [false,true]) =
      some (junc 0 (2*k+7) 1, -((4*k+13 : Nat) : Int)) := by
  have hfirst := boundary_to_sourceScanE_delta (2*k+1)
  have htail := sourceScanE_finishC_odd_delta (k+2) 0
  rw [crossTime_odd] at htail
  have hrewrite : 2*k+1+4 = 2*(k+2)+1 := by omega
  rw [hrewrite] at hfirst
  have htime :
      18*k+85 = 19 + ((14*(k+2)+15)+1 + (12+2*(2*(k+2)+1))) := by
    omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  have hw : 2*(k+2)+3 = 2*k+7 := by omega
  rw [hw]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

#print axioms boundary_to_sourceScanE_delta
#print axioms even_boundary_to_junc_delta
#print axioms odd_boundary_to_junc_delta

end BB429W4ScanE
