import W4ScanE
import W4JuncOne
import Lean.Elab.Tactic.Omega

namespace BB429W4Closure

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4ScanE BB429W4JuncOne

/-- Entire right-four A/1 boundary for even v reaches a canonical Junc. -/
theorem even_boundary_to_canonical (k : Nat) :
  runWithDelta (34*k+211)
    (z 0 (true :: (pairs01 (2*k+5) ++ ones 5)) true [false,true]) =
    some (junc 0 0 (4*k+22), -((4*k+17 : Nat) : Int)) := by
  have hfirst := even_boundary_to_junc_delta k
  have htail := junc2_w1_to_junc0 (2*k+6) (by omega)
  have htime : 34*k+211 = (18*k+109) + (8*(2*k+6)+54) := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  have hw : 2*(2*k+6)+10 = 4*k+22 := by omega
  rw [hw]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Entire right-four A/1 boundary for odd v reaches a canonical Junc. -/
theorem odd_boundary_to_canonical (k : Nat) :
  runWithDelta (40*k+277)
    (z 0 (true :: (pairs01 (2*k+1+5) ++ ones 5)) true [false,true]) =
    some (junc 0 0 (4*k+28), -((4*k+19 : Nat) : Int)) := by
  have hfirst := odd_boundary_to_junc_delta k
  have htail := junc0_odd_w1_to_junc0 k
  have htime : 40*k+277 = (18*k+85)+(22*k+192) := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

#print axioms even_boundary_to_canonical
#print axioms odd_boundary_to_canonical

end BB429W4Closure
