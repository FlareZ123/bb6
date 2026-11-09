import W2MidAauxCount
import W4CZeroOrdinary
import W4CZeroFull
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2JuncFullCount

open BB429OddExcursion BB429SourceE1Return BB429FinishScanEDelta
open BB429W4CZeroSafe BB429W4CZeroCount BB429High2Tail BB429JuncHeadExcursion
open BB429W2MidAauxCount BB429W4CZeroOrdinary BB429W4CZeroFull

/-- The complete fixed twelve-step C/1-to-A preparation is C/0-free. -/
theorem finishC_to_A_safe (left suffix : List Bool) :
    runSafe 12 (z 2 left true (ones 6 ++ suffix)) =
      some (z 0 left true (true :: (pairs01 2 ++ (true :: suffix)))) := by rfl

/-- Full prepared C/1 return, including any number of A/1,F/1 pairs,
    processes zero C/0 instructions. -/
theorem finishC_ScanE_safe (u p k : Nat) :
    runSafe (12+2*p) (finishCStart u p k) =
      some (junc u (p+2) (2*k+1)) := by
  let left : List Bool := pairs01 u ++ ones 5
  let suffix : List Bool := pairs01 2 ++ (true :: (ones (2*k) ++ [false,true]))
  have hfirst : runSafe 12 (finishCStart u p k) =
    some (z 0 (true :: (ones (2*p) ++ left)) true (true :: suffix)) := by
    simpa [finishCStart,left,suffix,ones,pairs01,List.append_assoc] using
      (finishC_to_A_safe (true :: (ones (2*p) ++ left)) (ones (2*k) ++ [false,true]))
  have hsecond := shift_A11_safe p left suffix
  rw [runSafe_add,hfirst]
  simp only [Option.bind_some]
  rw [hsecond]
  have hpairs : pairs01 p ++ pairs01 2 = pairs01 (p+2) := by
    rw [← pairs01_add p 2]
  have hones : ones (2*k+1) = true :: ones (2*k) := by
    calc
      ones (2*k+1) = ones (1+2*k) := by congr 1 <;> omega
      _ = ones 1 ++ ones (2*k) := BB429FinishScanEDelta.ones_add 1 (2*k)
      _ = true :: ones (2*k) := rfl
  have honesTail : true :: (ones (2*k) ++ [false,true]) =
      ones (2*k+1) ++ [false,true] := by
    rw [←List.cons_append,←hones]
  have hright : pairs01 p ++ (pairs01 2 ++ (true :: (ones (2*k) ++ [false,true]))) =
      pairs01 (p+2) ++ (ones (2*k+1) ++ [false,true]) := by
    rw [←List.append_assoc,hpairs,honesTail]
  simp only [junc]
  rw [hright]
  simp [left,List.append_assoc]

/-- Complete positive-u right-one Junc excursion executes one C/0. -/
theorem junc2_w1_count (v : Nat) (hv : 1 ≤ v) :
    runCount (8*v+54) (junc 2 v 1) =
      some (junc 0 0 (2*v+10),1) := by
  have hpre := runSafe_to_count_zero (2*v+6) (junc 2 v 1)
    (midApos 1 v 1) (juncPos_to_midA_safe 1 v 1 (by omega))
  have htail := midApos_w1_count v hv
  rw [show 8*v+54 = (2*v+6)+(6*v+48) by omega,runCount_add,hpre]
  simp only [Option.bind_some]
  rw [htail]
  rfl

/-- The initial zero-u right-two shift avoids C/0 until A/1. -/
theorem junc0_w2_to_boundary_safe (v : Nat) :
    runSafe (2*v+27) (junc 0 v 2) =
      some (z 0 (true :: (pairs01 (v+3) ++ ones 5)) true [false,true]) := by
  have hB := junc0_to_B_safe v 2 (by omega)
  rw [show 2*v+27 = (2*v+26)+1 by omega,runSafe_add,hB]
  rfl

/-- Each right-four A/1 boundary processes precisely its first C/0
    before entering the sourceScanE family. -/
theorem boundary_to_scanE_count (v : Nat) :
    runCount 19 (z 0 (true :: (pairs01 (v+5) ++ ones 5)) true [false,true]) =
      some (sourceScanE (v+4) (sourceSuffix 0),1) := by rfl

/-- Even A/1 boundary: exactly two C/0 starts throughout its full return. -/
theorem even_boundary_complete_count (k : Nat) :
    runCount (34*k+211)
      (z 0 (true :: (pairs01 (2*k+5) ++ ones 5)) true [false,true]) =
      some (junc 0 0 (4*k+22),2) := by
  have hfirst := boundary_to_scanE_count (2*k)
  have hE := runSafe_to_count_zero (crossTime (2*k+4)+1)
      (sourceScanE (2*k+4) (sourceSuffix 0))
      (z 2 (finalLeft (2*k+4)) true (sourceSuffix 0))
      (scanE_safe (2*k+4) (sourceSuffix 0))
  have hentry : z 2 (finalLeft (2*k+4)) true (sourceSuffix 0) =
      finishCStart 2 (2*k+4) 0 := by
    simpa only [show 2*(k+2)=2*k+4 by omega] using
      (finalLeft_even_finishC_entry (k+2) 0)
  have hfinish := runSafe_to_count_zero (12+2*(2*k+4))
      (finishCStart 2 (2*k+4) 0) (junc 2 ((2*k+4)+2) 1)
      (finishC_ScanE_safe 2 (2*k+4) 0)
  have hlast := junc2_w1_count (2*k+6) (by omega)
  have htime : 34*k+211 = 19 + ((crossTime (2*k+4)+1) +
        ((12+2*(2*k+4))+(8*(2*k+6)+54))) := by
    rw [show 2*k+4=2*(k+2) by omega,crossTime_even]
    omega
  rw [htime,runCount_add,hfirst]
  simp only [Option.bind_some]
  rw [runCount_add,hE]
  simp only [Option.bind_some]
  rw [hentry,runCount_add,hfinish]
  simp only [Option.bind_some]
  have hparam : 2*k+4+2=2*k+6 := by omega
  rw [hparam,hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  have hend : 2*(2*k+6)+10=4*k+22 := by omega
  rw [hend]
  trivial

/-- Odd A/1 boundary: exactly three C/0 starts throughout its full return. -/
theorem odd_boundary_complete_count (k : Nat) :
    runCount (40*k+277)
      (z 0 (true :: (pairs01 (2*k+1+5) ++ ones 5)) true [false,true]) =
      some (junc 0 0 (4*k+28),3) := by
  have hfirst := boundary_to_scanE_count (2*k+1)
  have hE := runSafe_to_count_zero (crossTime (2*k+5)+1)
      (sourceScanE (2*k+5) (sourceSuffix 0))
      (z 2 (finalLeft (2*k+5)) true (sourceSuffix 0))
      (scanE_safe (2*k+5) (sourceSuffix 0))
  have hentry : z 2 (finalLeft (2*k+5)) true (sourceSuffix 0) =
      finishCStart 0 (2*k+5) 0 := by
    simpa only [show 2*(k+2)+1=2*k+5 by omega] using
      (finalLeft_odd_finishC_entry (k+2) 0)
  have hfinish := runSafe_to_count_zero (12+2*(2*k+5))
      (finishCStart 0 (2*k+5) 0) (junc 0 ((2*k+5)+2) 1)
      (finishC_ScanE_safe 0 (2*k+5) 0)
  have hlast := junc0_odd_complete_czero_count (k+3)
  have htime : 40*k+277 = 19 + ((crossTime (2*k+5)+1) +
        ((12+2*(2*k+5))+(22*(k+3)+126))) := by
    rw [show 2*k+5=2*(k+2)+1 by omega,crossTime_odd]
    omega
  rw [htime,runCount_add,hfirst]
  simp only [Option.bind_some]
  rw [runCount_add,hE]
  simp only [Option.bind_some]
  rw [hentry,runCount_add,hfinish]
  simp only [Option.bind_some]
  have hparam : 2*k+5+2 = 2*(k+3)+1 := by omega
  rw [hparam,hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  have hend : 4*(k+3)+16=4*k+28 := by omega
  rw [hend]
  trivial

/-- Complete exception w=2 with even index v=2k+2 has exactly two
    C/0 instructions, for all k including arbitrarily large k. -/
theorem junc0_w2_even_complete_count (k : Nat) :
    runCount (38*k+242) (junc 0 (2*k+2) 2) =
      some (junc 0 0 (4*k+22),2) := by
  have hpre : runCount (4*k+31) (junc 0 (2*k+2) 2) =
      some (z 0 (true :: (pairs01 (2*k+5) ++ ones 5)) true [false,true],0) := by
    have hp := runSafe_to_count_zero (2*(2*k+2)+27) (junc 0 (2*k+2) 2)
      (z 0 (true :: (pairs01 ((2*k+2)+3) ++ ones 5)) true [false,true])
      (junc0_w2_to_boundary_safe (2*k+2))
    simpa only [show 2*(2*k+2)+27 = 4*k+31 by omega,
      show (2*k+2)+3 = 2*k+5 by omega] using hp
  have hlast := even_boundary_complete_count k
  rw [show 38*k+242 = (4*k+31)+(34*k+211) by omega,
      runCount_add,hpre]
  simp only [Option.bind_some]
  rw [hlast]
  rfl

/-- Complete exception w=2 with odd index v=2k+3 has exactly three
    C/0 instructions, for all k including arbitrarily large k. -/
theorem junc0_w2_odd_complete_count (k : Nat) :
    runCount (44*k+310) (junc 0 (2*k+3) 2) =
      some (junc 0 0 (4*k+28),3) := by
  have hpre : runCount (4*k+33) (junc 0 (2*k+3) 2) =
      some (z 0 (true :: (pairs01 (2*k+1+5) ++ ones 5)) true [false,true],0) := by
    have hp := runSafe_to_count_zero (2*(2*k+3)+27) (junc 0 (2*k+3) 2)
      (z 0 (true :: (pairs01 ((2*k+3)+3) ++ ones 5)) true [false,true])
      (junc0_w2_to_boundary_safe (2*k+3))
    simpa only [show 2*(2*k+3)+27 = 4*k+33 by omega,
      show (2*k+3)+3 = 2*k+1+5 by omega] using hp
  have hlast := odd_boundary_complete_count k
  rw [show 44*k+310 = (4*k+33)+(40*k+277) by omega,
      runCount_add,hpre]
  simp only [Option.bind_some]
  rw [hlast]
  rfl

/-- Exact base v=0: 204 primitive steps, two C/0 starts and return
    to Junc(0,0,18). Computed by the original zipper definition. -/
theorem junc0_w2_base_even :
    runCount 204 (junc 0 0 2) = some (junc 0 0 18,2) := by decide

/-- Exact base v=1: 266 primitive steps, three C/0 starts and return
    to Junc(0,0,24). Computed by the original zipper definition. -/
theorem junc0_w2_base_odd :
    runCount 266 (junc 0 1 2) = some (junc 0 0 24,3) := by decide

/-- ALL even v, including v=0, have exactly two C/0 visits and end
    in a canonical zero-u Junc. -/
theorem junc0_w2_all_even_count (k : Nat) :
    runCount (38*k+204) (junc 0 (2*k) 2) =
      some (junc 0 0 (4*k+18),2) := by
  cases k with
  | zero => simpa using junc0_w2_base_even
  | succ k =>
      have h := junc0_w2_even_complete_count k
      simpa only [Nat.succ_eq_add_one,
        show 38*(k+1)+204 = 38*k+242 by omega,
        show 2*(k+1) = 2*k+2 by omega,
        show 4*(k+1)+18 = 4*k+22 by omega] using h

/-- ALL odd v, including v=1, have exactly three C/0 visits and end
    in a canonical zero-u Junc. -/
theorem junc0_w2_all_odd_count (k : Nat) :
    runCount (44*k+266) (junc 0 (2*k+1) 2) =
      some (junc 0 0 (4*k+24),3) := by
  cases k with
  | zero => simpa using junc0_w2_base_odd
  | succ k =>
      have h := junc0_w2_odd_complete_count k
      simpa only [Nat.succ_eq_add_one,
        show 44*(k+1)+266 = 44*k+310 by omega,
        show 2*(k+1)+1 = 2*k+3 by omega,
        show 4*(k+1)+24 = 4*k+28 by omega] using h

#print axioms junc0_w2_base_even
#print axioms junc0_w2_base_odd
#print axioms junc0_w2_all_even_count
#print axioms junc0_w2_all_odd_count

#print axioms finishC_ScanE_safe
#print axioms junc2_w1_count
#print axioms boundary_to_scanE_count
#print axioms even_boundary_complete_count
#print axioms odd_boundary_complete_count
#print axioms junc0_w2_even_complete_count
#print axioms junc0_w2_odd_complete_count

end BB429W2JuncFullCount
