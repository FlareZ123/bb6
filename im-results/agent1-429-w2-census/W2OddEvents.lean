import W4ScanE
import W4CZeroEvents
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2OddEvent
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4ScanE BB429W4CZeroEvents

/-- Exact C/0-free right-two sweep reaches A/1 at the boundary. -/
theorem w2_to_A_boundary_delta (v : Nat) :
    runWithDelta (2*v+27) (junc 0 v 2) =
      some (z 0 (true :: (pairs01 (v+3) ++ ones 5)) true [false,true],
        ((2*v+3 : Nat) : Int)) := by
  have hB := junc0_to_B_delta v 2 (by omega)
  have hlast :
      runWithDelta 1
        (z 1 (pairs01 (v+3) ++ ones 5) true (ones 1 ++ [false,true])) =
      some (z 0 (true :: (pairs01 (v+3) ++ ones 5)) true [false,true], 1) := by
    rfl
  rw [show 2*v+27 = (2*v+26)+1 by omega, runWithDelta_add, hB]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some]
  simp [Int.natCast_add,Int.natCast_mul]
  omega

/-- Complete right-two odd v>=3 initial passage reaches a right-one
    Junc after 22k+118 moves, exactly four cells to the left. -/
theorem odd_w2_to_w1_delta (k : Nat) :
  runWithDelta (22*k+118) (junc 0 (2*k+3) 2) =
    some (junc 0 (2*k+7) 1, -4) := by
  have hfirst := w2_to_A_boundary_delta (2*k+3)
  have htail := odd_boundary_to_junc_delta k
  have hleft : 2*k+3+3 = 2*k+1+5 := by omega
  have htime : 22*k+118 = (2*(2*k+3)+27)+(18*k+85) := by omega
  rw [htime,runWithDelta_add,hfirst]
  simp only [Option.bind_some]
  rw [hleft,htail]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Exact second C/0 visit for every odd v>=3 has a blank right stack. -/
theorem odd_w2_second_gate_delta (k : Nat) :
    runWithDelta (26*k+163) (junc 0 (2*k+3) 2) =
      some (z 2 (ones 5 ++ (pairs01 ((2*k+7)+3) ++ ones 5)) false [],
       ((4*k+17 : Nat) : Int)) := by
  have hfirst := odd_w2_to_w1_delta k
  have hlast := junc0_w1_first_czero (2*k+7)
  have htime : 26*k+163 = (22*k+118) + (2*(2*k+7)+31) := by omega
  rw [htime,runWithDelta_add,hfirst]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Exact third C/0 visit for every odd v>=3 has a blank right stack. -/
theorem odd_w2_third_gate_delta (k : Nat) :
    runWithDelta (40*k+260) (junc 0 (2*k+3) 2) =
      some (z 2 (([true,false,true] ++ ones 7) ++ finalLeft ((2*k+7)+2)) false [],
       ((4*k+20 : Nat) : Int)) := by
  have hfirst := odd_w2_to_w1_delta k
  have hlast := junc0_w1_second_czero (2*k+7)
  have htime : 40*k+260 = (22*k+118) +
      (2*(2*k+7)+42+(crossTime ((2*k+7)+2)+15)) := by
    rw [show 2*k+7+2=2*(k+4)+1 by omega,crossTime_odd]
    omega
  rw [htime,runWithDelta_add,hfirst]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- All odd v=2k+1, including v=1, have a second C/0 after 26k+137
    primitive moves. Its entire right half-tape is blank. -/
theorem odd_w2_all_second_gate (k : Nat) :
    (runWithDelta (26*k+137) (junc 0 (2*k+1) 2)).map
      (fun p => (p.1.state,p.1.current,p.1.right,p.2)) =
    some (2,false,[], ((4*k+13 : Nat) : Int)) := by
  cases k with
  | zero => decide
  | succ k =>
      rw [show 26*(k+1)+137=26*k+163 by omega,
          show 2*(k+1)+1=2*k+3 by omega,
          odd_w2_second_gate_delta]
      change some (2,false,[], ((4*k+17 : Nat) : Int)) =
        some (2,false,[], ((4*(k+1)+13 : Nat) : Int))
      congr 1 <;> omega

/-- All odd v=2k+1, including v=1, have a third C/0 after 40k+220
    moves. Its entire right half-tape is blank. -/
theorem odd_w2_all_third_gate (k : Nat) :
    (runWithDelta (40*k+220) (junc 0 (2*k+1) 2)).map
      (fun p => (p.1.state,p.1.current,p.1.right,p.2)) =
    some (2,false,[], ((4*k+16 : Nat) : Int)) := by
  cases k with
  | zero => decide
  | succ k =>
      rw [show 40*(k+1)+220=40*k+260 by omega,
          show 2*(k+1)+1=2*k+3 by omega,
          odd_w2_third_gate_delta]
      change some (2,false,[], ((4*k+20 : Nat) : Int)) =
        some (2,false,[], ((4*(k+1)+16 : Nat) : Int))
      congr 1 <;> omega

#print axioms w2_to_A_boundary_delta
#print axioms odd_w2_to_w1_delta
#print axioms odd_w2_second_gate_delta
#print axioms odd_w2_third_gate_delta
#print axioms odd_w2_all_second_gate
#print axioms odd_w2_all_third_gate

end BB429W2OddEvent
