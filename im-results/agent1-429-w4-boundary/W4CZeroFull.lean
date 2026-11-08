import W4CZeroCount
import W4JuncOne
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429W4CZeroFull

open BB429OddExcursion BB429SourceE1Return
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4CZeroSafe BB429W4CZeroCount BB429W4JuncOne

/-- Starting from C/0 after its right-hand record, a fixed six-step
    original-table continuation reaches E/1 and counts exactly one
    C/0 instruction: the starting configuration. -/
theorem czero_to_e1_6_count (left : List Bool) :
    runCount 6 (z 2 (([true,false,true] ++ ones 7) ++ left) false []) =
      some (z 4 (ones 8 ++ left) true [true,false,true],1) := by rfl

/-- Every leftward E/1 sweep over an arbitrary all-ones block is C/0-free,
    with all untouched left and right context parameterized. -/
theorem E1_sweep_safe (n : Nat) (left suffix : List Bool) :
    runSafe n (z 4 (ones n ++ left) true suffix) =
      some (z 4 left true (ones n ++ suffix)) := by
  induction n generalizing left suffix with
  | zero => rfl
  | succ n ih =>
      have hstep : runSafe 1
        (z 4 (ones (n+1) ++ left) true suffix) =
          some (z 4 (ones n ++ left) true (true::suffix)) := by rfl
      rw [show n+1 = 1+n by omega, runSafe_add,
        show 1+n = n+1 by omega, hstep]
      simp only [Option.bind_some]
      rw [ih]
      have hright : ones n ++ (true::suffix) = ones (n+1) ++ suffix := by
        simp [ones, List.replicate_succ', List.append_assoc]
      rw [hright]

/-- Fixed twelve-step E/1-to-Junc suffix, with arbitrary unvisited right
    context, has no C/0 transition. -/
theorem E1_tail12_safe (suffix : List Bool) :
    runSafe 12 (z 4 [] true (ones 4 ++ suffix)) =
      some (z 0 (ones 6) true suffix) := by rfl

/-- The fixed 72-step even E/1 tail, including its symbolic unbounded
    right-hand block, contains no C/0 transition. -/
theorem even_E1_tail72_safe (k : Nat) :
    runSafe 72
      (z 4 (pairs01 2 ++ ones 5) true
        (ones (4*k+13) ++ [true,false,true])) =
      some (junc 2 4 (4*k+9)) := by
  have hr : ones (4*k+13) ++ [true,false,true] =
      ones (4*k+14) ++ [false,true] := by
    have h : ones (4*k+13) ++ [true] = ones (4*k+14) := by
      change List.replicate (4*k+13) true ++ [true] =
        List.replicate (4*k+14) true
      rw [show 4*k+14 = (4*k+13)+1 by omega]
      exact List.replicate_succ'.symm
    calc
      ones (4*k+13) ++ [true,false,true] =
        (ones (4*k+13) ++ [true]) ++ [false,true] := by
          simp [List.append_assoc]
      _ = ones (4*k+14) ++ [false,true] := by rw [h]
  rw [hr]
  rfl

/-- For every k, the entire completed ODD-indexed right-one Junc passage
    makes exactly two C/0 moves, before arriving at the canonical Junc.
    The first and second visits are source-identified at 2v+31 and
    2v+42+crossTime(v+2)+15; each scans past the old marked frontier
    into a completely blank right half-tape. -/
theorem junc0_odd_complete_czero_count (k : Nat) :
    runCount (22*k+126) (junc 0 (2*k+1) 1) =
      some (junc 0 0 (4*k+16),2) := by
  have hfirst := junc0_w1_second_czero_count (2*k+1)
  have h6 := czero_to_e1_6_count (finalLeft (2*k+3))
  have hsum : ones 8 ++ finalLeft (2*k+3) = ones (4*k+20) := by
    rw [show 2*k+3=2*(k+1)+1 by omega, finalLeft_odd]
    rw [show 4*(k+1)+8=4*k+12 by omega]
    rw [← BB429SourceE1Return.ones_add]
    congr 1; omega
  have hsweep := runSafe_to_count_zero (4*k+20)
      (z 4 (ones (4*k+20)) true [true,false,true])
      (z 4 [] true (ones (4*k+20) ++ [true,false,true]))
      (by simpa using (E1_sweep_safe (4*k+20) [] [true,false,true]))
  have htail := runSafe_to_count_zero 12
      (z 4 [] true (ones 4 ++ (ones (4*k+16) ++ [true,false,true])))
      (z 0 (ones 6) true (ones (4*k+16) ++ [true,false,true]))
      (E1_tail12_safe (ones (4*k+16) ++ [true,false,true]))
  have htailinput :
      ones (4*k+20) ++ [true,false,true] =
      ones 4 ++ (ones (4*k+16) ++ [true,false,true]) := by
    rw [show 4*k+20 = 4+(4*k+16) by omega,
      BB429SourceE1Return.ones_add, List.append_assoc]
  have hfirsttime :
      2*(2*k+1)+42+(crossTime ((2*k+1)+2)+15) = 18*k+88 := by
    rw [show (2*k+1)+2=2*(k+1)+1 by omega,
      crossTime_odd]
    omega
  have htime : 22*k+126 =
      (18*k+88)+(6+((4*k+20)+12)) := by omega
  rw [htime, ← hfirsttime, runCount_add, hfirst]
  simp only [Option.bind_some]
  rw [runCount_add, h6]
  simp only [Option.bind_some]
  rw [hsum, runCount_add, hsweep]
  simp only [Option.bind_some]
  rw [htailinput, htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · change z 0 (ones 6) true (ones (4*k+16) ++ [true,false,true]) =
        z 0 (true :: (pairs01 0 ++ ones 5)) true
          (true :: (pairs01 0 ++ ones (4*k+16) ++ [false,true]))
    rw [ones_right_101]
    rfl
  · trivial

/-- For every k, the entire completed EVEN-indexed right-one Junc
    passage likewise makes exactly two C/0 moves. The terminal 72-step
    suffix is proved C/0-free for every symbolic right-hand block. -/
theorem junc0_even_complete_czero_count (k : Nat) :
    runCount (22*k+203) (junc 0 (2*k) 1) =
      some (junc 2 4 (4*k+9),2) := by
  have hfirst := junc0_w1_second_czero_count (2*k)
  have h6 := czero_to_e1_6_count (finalLeft (2*k+2))
  have hsum : ones 8 ++ finalLeft (2*k+2) =
      ones (4*k+13) ++ pairs01 2 ++ ones 5 := by
    rw [show 2*k+2=2*(k+1) by omega, finalLeft_even]
    rw [show 4*(k+1)+1=4*k+5 by omega]
    change ones 8 ++ (ones (4*k+5) ++ pairs01 2 ++ ones 5) = _
    calc
      ones 8 ++ (ones (4*k+5) ++ pairs01 2) ++ ones 5 =
          (ones 8 ++ ones (4*k+5)) ++ pairs01 2 ++ ones 5 := by
            simp [List.append_assoc]
      _ = ones (4*k+13) ++ pairs01 2 ++ ones 5 := by
        rw [← BB429SourceE1Return.ones_add]
        rw [show 8+(4*k+5)=4*k+13 by omega]
  have hsweep := runSafe_to_count_zero (4*k+13)
      (z 4 (ones (4*k+13) ++ pairs01 2 ++ ones 5) true [true,false,true])
      (z 4 (pairs01 2 ++ ones 5) true
        (ones (4*k+13) ++ [true,false,true]))
      (by simpa only [List.append_assoc] using
        (E1_sweep_safe (4*k+13) (pairs01 2 ++ ones 5) [true,false,true]))
  have htail := runSafe_to_count_zero 72
      (z 4 (pairs01 2 ++ ones 5) true
        (ones (4*k+13) ++ [true,false,true]))
      (junc 2 4 (4*k+9)) (even_E1_tail72_safe k)
  have hfirsttime :
      2*(2*k)+42+(crossTime ((2*k)+2)+15) = 18*k+112 := by
    rw [show 2*k+2=2*(k+1) by omega, crossTime_even]
    omega
  have htime : 22*k+203 =
      (18*k+112)+(6+((4*k+13)+72)) := by omega
  rw [htime, ← hfirsttime, runCount_add, hfirst]
  simp only [Option.bind_some]
  rw [runCount_add, h6]
  simp only [Option.bind_some]
  rw [hsum, runCount_add, hsweep]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]

#print axioms czero_to_e1_6_count
#print axioms E1_sweep_safe
#print axioms even_E1_tail72_safe
#print axioms junc0_odd_complete_czero_count
#print axioms junc0_even_complete_czero_count

end BB429W4CZeroFull
