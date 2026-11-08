import High2Prefix
import BB429JuncHeadExcursion
import BB429FinishScanEDelta
import Lean.Elab.Tactic.Omega
namespace BB429High1Source
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta BB429High2Prefix
open BB429FinishScanEDelta BB429JuncHeadExcursion

/-- The intermediate J(u,2u+1) C/B sweep has right suffix 101. -/
def high1SweepStart (u : Nat) : Zipper :=
  z 2 (tens (2*u+2) ++ ones 6) true [true,false,true]

/-- First seventeen raw source steps enter the exact even-b E/1 family. -/
theorem high1_enter_e (u : Nat) :
  runWithDelta 17 (high1SweepStart u) =
    some (sourceScanE (2*u+2) [true,true,true,false,true,false,false,true], -1) := by
  unfold high1SweepStart
  rw [tens_append_ones6]
  rfl

/-- Fixed C/1 preparation for the high-one right boundary. -/
theorem c1_high1_to_e (tail : List Bool) :
  runWithDelta 20 (z 2 (ones 5 ++ tail) true
     [true,true,true,false,true,false,false,true]) =
    some (z 4 (ones 13 ++ tail) true [true,false,true], 8) := by
  rfl

/-- E/1 traverses an arbitrary prefix of ones, retaining an untouched left
    suffix, with exact physical displacement. -/
theorem e1_sweep_prefix_delta (n : Nat) (left suffix : List Bool) :
    runWithDelta n (z 4 (ones n ++ left) true suffix) =
      some (z 4 left true (ones n ++ suffix), -((n : Nat) : Int)) := by
  induction n generalizing left suffix with
  | zero =>
      rfl
  | succ n ih =>
      rw [show n+1 = 1+n by omega, runWithDelta_add]
      have hleft : ones (1+n) ++ left = true :: (ones n ++ left) := by
        rw [BB429SourceE1Return.ones_add 1 n]
        simp [ones, List.append_assoc]
      have hstep :
          runWithDelta 1 (z 4 (ones (1+n) ++ left) true suffix) =
            some (z 4 (ones n ++ left) true (true :: suffix), -1) := by
        rw [hleft]
        simp [runWithDelta, oneWithDelta, one, action, z, ones]
      rw [hstep]
      simp only [Option.bind_some]
      rw [ih]
      simp only [Option.map_some]
      have hones : ones n ++ [true] = ones (n+1) := by
        simpa [ones] using (BB429SourceE1Return.ones_add n 1).symm
      have hright : ones n ++ (true :: suffix) = ones (n+1) ++ suffix := by
        calc
          ones n ++ (true :: suffix) = ones n ++ ([true] ++ suffix) := rfl
          _ = (ones n ++ [true]) ++ suffix := by rw [← List.append_assoc]
          _ = ones (n+1) ++ suffix := by rw [hones]
      rw [hright, show n+1 = 1+n by omega]
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · trivial
      · omega

/-- Uniform twenty-step C/1 preparation followed by the long E/1 sweep
    enters the source S_E(2, ..., 2u+4) family. -/
theorem high1_c_to_source (u : Nat) :
  runWithDelta (4*u+33)
    (z 2 (finalLeft (2*u+2)) true
      [true,true,true,false,true,false,false,true]) =
    some (sourceScanE 2 (sourceSuffix (2*u+4)), -((4*u+5 : Nat) : Int)) := by
  have hleft : finalLeft (2*u+2) =
      ones 5 ++ (ones (4*u) ++ (pairs01 2 ++ ones 5)) := by
    rw [show 2*u+2=2*(u+1) by omega, finalLeft_even]
    rw [show 4*(u+1)+1=5+4*u by omega,
        BB429SourceE1Return.ones_add 5 (4*u)]
    simp [pairs01, List.append_assoc]
  have hA := c1_high1_to_e (ones (4*u) ++ (pairs01 2 ++ ones 5))
  have hB := e1_sweep_prefix_delta (4*u+13) (pairs01 2 ++ ones 5)
      [true,false,true]
  have hpart : ones 13 ++ (ones (4*u) ++ (pairs01 2 ++ ones 5)) =
      ones (4*u+13) ++ (pairs01 2 ++ ones 5) := by
    rw [← List.append_assoc, ← BB429SourceE1Return.ones_add]
    rw [show 13+4*u=4*u+13 by omega]
  have hright : ones (4*u+13) ++ [true,false,true] =
      sourceSuffix (2*u+4) := by
    have hh : ones (4*u+13) ++ [true] = ones (4*u+14) := by
      calc
        ones (4*u+13) ++ [true] = ones (4*u+13) ++ ones 1 := rfl
        _ = ones ((4*u+13)+1) := (BB429SourceE1Return.ones_add _ 1).symm
        _ = ones (4*u+14) := by congr 1
    have hw : ones 6 ++ ones (2*(2*u+4)) = ones (4*u+14) := by
      rw [← BB429SourceE1Return.ones_add]
      congr 1 <;> omega
    calc
      ones (4*u+13) ++ [true,false,true] =
          (ones (4*u+13) ++ [true]) ++ [false,true] := by
            simp [List.append_assoc]
      _ = ones (4*u+14) ++ [false,true] := by rw [hh]
      _ = sourceSuffix (2*u+4) := by
         simp [sourceSuffix, List.append_assoc, hw]
  have htime : 4*u+33 = 20 + (4*u+13) := by omega
  rw [hleft, htime, runWithDelta_add, hA]
  simp only [Option.bind_some]
  rw [hpart, hB]
  simp only [Option.map_some]
  rw [← hright]
  simp only [sourceScanE, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

/-- Complete source-exact intermediate high-one J branch. -/
theorem high1_to_junc (u : Nat) :
  runWithDelta (18*u+281) (high1SweepStart u) =
    some (junc 11 0 (4*u+2), 5-4*(u:Int)) := by
  have a := high1_enter_e u
  have b := sourceScanE_e1_revisit_delta (2*u+2)
      [true,true,true,false,true,false,false,true]
  have c := high1_c_to_source u
  have d := sourceScanE_finishC_even_after_junc0_delta 1 (2*u+4) (by omega)
  have ht : 18*u+281 =
      17 + ((crossTime (2*u+2)+1) + ((4*u+33) +
        ((crossTime 2+1 + (12+2*2)) + (juncPosFullTime 2 4 + (2*(2*1+6)+27))))) := by
    rw [show 2*u+2=2*(u+1) by omega, crossTime_even]
    simp [crossTime, juncPosFullTime]
    omega
  rw [ht, runWithDelta_add, a]
  simp only [Option.bind_some]
  rw [runWithDelta_add, b]
  simp only [Option.bind_some]
  rw [runWithDelta_add, c]
  simp only [Option.bind_some]
  have htime : ((crossTime 2+1 + (12+2*2)) + (juncPosFullTime 2 4 + (2*(2*1+6)+27))) =
         ((crossTime (2*1)+1 + (12+2*(2*1))) +
         (juncPosFullTime 2 (2*1+2) + (2*(2*1+6)+27))) := by rfl
  rw [htime, d]
  simp only [Option.map_some]
  have hw : (2*(2*u+4)-6) = 4*u+2 := by omega
  simp only [hw]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  omega

#print axioms high1_enter_e
#print axioms high1_c_to_source
#print axioms high1_to_junc
end BB429High1Source
